import V185TrunkScan23Chunk0799

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4731893 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4731893 : Nat := 118140960795 + 4731893 * 2 ^ 59
def prefixEnd_4731893 : Nat := 4983230072969 + 3 ^ 40 * 4731893 * 2
def baseEnd_4731893 : Nat := 2429735514645560180575927

theorem tailTrace_4731893 : CollatzResearch.WordTrace tailWord_4731893 prefixEnd_4731893 2429735514645560180575927 := by
  unfold tailWord_4731893
  simp only [CollatzResearch.WordTrace]
  refine ⟨172586316246167278829960333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115057544164111519219973555 172586316246167278829960333)
  ·
    refine ⟨64719868592312729561235125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172586316246167278829960333 64719868592312729561235125)
    ·
      refine ⟨6067487680529318396365793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64719868592312729561235125 6067487680529318396365793)
      ·
        refine ⟨4550615760396988797274345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067487680529318396365793 4550615760396988797274345)
        ·
          refine ⟨3412961820297741597955759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4550615760396988797274345 3412961820297741597955759)
          ·
            refine ⟨5119442730446612396933639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412961820297741597955759 5119442730446612396933639)
            ·
              refine ⟨7679164095669918595400459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119442730446612396933639 7679164095669918595400459)
              ·
                refine ⟨11518746143504877893100689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679164095669918595400459 11518746143504877893100689)
                ·
                  refine ⟨8639059607628658419825517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11518746143504877893100689 8639059607628658419825517)
                  ·
                    refine ⟨3239647352860746907434569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8639059607628658419825517 3239647352860746907434569)
                    ·
                      refine ⟨2429735514645560180575927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239647352860746907434569 2429735514645560180575927)
                      ·
                        rfl

theorem cell23_4731893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4731893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731893 prefixEnd_4731893 := by exact prefixLift 4731893
  have htrace : WordTrace (prefixWord ++ tailWord_4731893) baseStart_4731893 baseEnd_4731893 := by
    simpa [prefixWord, tailWord_4731893, baseEnd_4731893] using wordTrace_append hprefix tailTrace_4731893
  have hstable : (prefixWord ++ tailWord_4731893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731893).length < 2 ^ (prefixWord ++ tailWord_4731893).sum := by decide
  have hdescent : baseEnd_4731893 < baseStart_4731893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731905 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4731905 : Nat := 118140960795 + 4731905 * 2 ^ 59
def prefixEnd_4731905 : Nat := 4983230072969 + 3 ^ 40 * 4731905 * 2
def baseEnd_4731905 : Nat := 2429741676413414133625871

theorem tailTrace_4731905 : CollatzResearch.WordTrace tailWord_4731905 prefixEnd_4731905 2429741676413414133625871 := by
  unfold tailWord_4731905
  simp only [CollatzResearch.WordTrace]
  refine ⟨172586753922123804879397169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115057835948082536586264779 172586753922123804879397169)
  ·
    refine ⟨129440065441592853659547877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172586753922123804879397169 129440065441592853659547877)
    ·
      refine ⟨24270012270298660061165227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129440065441592853659547877 24270012270298660061165227)
      ·
        refine ⟨36405018405447990091747841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24270012270298660061165227 36405018405447990091747841)
        ·
          refine ⟨27303763804085992568810881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36405018405447990091747841 27303763804085992568810881)
          ·
            refine ⟨20477822853064494426608161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27303763804085992568810881 20477822853064494426608161)
            ·
              refine ⟨15358367139798370819956121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20477822853064494426608161 15358367139798370819956121)
              ·
                refine ⟨11518775354848778114967091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15358367139798370819956121 11518775354848778114967091)
                ·
                  refine ⟨17278163032273167172450637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11518775354848778114967091 17278163032273167172450637)
                  ·
                    refine ⟨6479311137102437689668989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17278163032273167172450637 6479311137102437689668989)
                    ·
                      refine ⟨2429741676413414133625871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6479311137102437689668989 2429741676413414133625871)
                      ·
                        rfl

theorem cell23_4731905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4731905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731905 prefixEnd_4731905 := by exact prefixLift 4731905
  have htrace : WordTrace (prefixWord ++ tailWord_4731905) baseStart_4731905 baseEnd_4731905 := by
    simpa [prefixWord, tailWord_4731905, baseEnd_4731905] using wordTrace_append hprefix tailTrace_4731905
  have hstable : (prefixWord ++ tailWord_4731905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731905).length < 2 ^ (prefixWord ++ tailWord_4731905).sum := by decide
  have hdescent : baseEnd_4731905 < baseStart_4731905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731939 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 2, 1, 3]
def baseStart_4731939 : Nat := 118140960795 + 4731939 * 2 ^ 59
def prefixEnd_4731939 : Nat := 4983230072969 + 3 ^ 40 * 4731939 * 2
def baseEnd_4731939 : Nat := 2429759134755667000600715

theorem tailTrace_4731939 : CollatzResearch.WordTrace tailWord_4731939 prefixEnd_4731939 2429759134755667000600715 := by
  unfold tailWord_4731939
  simp only [CollatzResearch.WordTrace]
  refine ⟨172587994004000628686134871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115058662669333752457423247 172587994004000628686134871)
  ·
    refine ⟨258881991006000943029202307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172587994004000628686134871 258881991006000943029202307)
    ·
      refine ⟨388322986509001414543803461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258881991006000943029202307 388322986509001414543803461)
      ·
        refine ⟨72810559970437765226963149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388322986509001414543803461 72810559970437765226963149)
        ·
          refine ⟨27303959988914161960111181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72810559970437765226963149 27303959988914161960111181)
          ·
            refine ⟨10238984995842810735041693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27303959988914161960111181 10238984995842810735041693)
            ·
              refine ⟨3839619373441054025640635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10238984995842810735041693 3839619373441054025640635)
              ·
                refine ⟨5759429060161581038460953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839619373441054025640635 5759429060161581038460953)
                ·
                  refine ⟨4319571795121185778845715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759429060161581038460953 4319571795121185778845715)
                  ·
                    refine ⟨6479357692681778668268573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4319571795121185778845715 6479357692681778668268573)
                    ·
                      refine ⟨2429759134755667000600715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6479357692681778668268573 2429759134755667000600715)
                      ·
                        rfl

theorem cell23_4731939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_4731939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731939 prefixEnd_4731939 := by exact prefixLift 4731939
  have htrace : WordTrace (prefixWord ++ tailWord_4731939) baseStart_4731939 baseEnd_4731939 := by
    simpa [prefixWord, tailWord_4731939, baseEnd_4731939] using wordTrace_append hprefix tailTrace_4731939
  have hstable : (prefixWord ++ tailWord_4731939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731939).length < 2 ^ (prefixWord ++ tailWord_4731939).sum := by decide
  have hdescent : baseEnd_4731939 < baseStart_4731939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731948 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_4731948 : Nat := 118140960795 + 4731948 * 2 ^ 59
def prefixEnd_4731948 : Nat := 4983230072969 + 3 ^ 40 * 4731948 * 2
def baseEnd_4731948 : Nat := 2429763756081557465388173

theorem tailTrace_4731948 : CollatzResearch.WordTrace tailWord_4731948 prefixEnd_4731948 2429763756081557465388173 := by
  unfold tailWord_4731948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86294161130484011611606249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115058881507312015482141665 86294161130484011611606249)
  ·
    refine ⟨64720620847863008708704687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86294161130484011611606249 64720620847863008708704687)
    ·
      refine ⟨97080931271794513063057031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64720620847863008708704687 97080931271794513063057031)
      ·
        refine ⟨145621396907691769594585547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97080931271794513063057031 145621396907691769594585547)
        ·
          refine ⟨218432095361537654391878321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145621396907691769594585547 218432095361537654391878321)
          ·
            refine ⟨163824071521153240793908741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218432095361537654391878321 163824071521153240793908741)
            ·
              refine ⟨30717013410216232648857889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163824071521153240793908741 30717013410216232648857889)
              ·
                refine ⟨23037760057662174486643417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30717013410216232648857889 23037760057662174486643417)
                ·
                  refine ⟨17278320043246630864982563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23037760057662174486643417 17278320043246630864982563)
                  ·
                    refine ⟨25917480064869946297473845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17278320043246630864982563 25917480064869946297473845)
                    ·
                      refine ⟨2429763756081557465388173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25917480064869946297473845 2429763756081557465388173)
                      ·
                        rfl

theorem cell23_4731948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_4731948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731948 prefixEnd_4731948 := by exact prefixLift 4731948
  have htrace : WordTrace (prefixWord ++ tailWord_4731948) baseStart_4731948 baseEnd_4731948 := by
    simpa [prefixWord, tailWord_4731948, baseEnd_4731948] using wordTrace_append hprefix tailTrace_4731948
  have hstable : (prefixWord ++ tailWord_4731948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731948).length < 2 ^ (prefixWord ++ tailWord_4731948).sum := by decide
  have hdescent : baseEnd_4731948 < baseStart_4731948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731962 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_4731962 : Nat := 118140960795 + 4731962 * 2 ^ 59
def prefixEnd_4731962 : Nat := 4983230072969 + 3 ^ 40 * 4731962 * 2
def baseEnd_4731962 : Nat := 2429770944810720410613109

theorem tailTrace_4731962 : CollatzResearch.WordTrace tailWord_4731962 prefixEnd_4731962 2429770944810720410613109 := by
  unfold tailWord_4731962
  simp only [CollatzResearch.WordTrace]
  refine ⟨43147208220729325903555535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115059221921944869076148093 43147208220729325903555535)
  ·
    refine ⟨64720812331093988855333303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43147208220729325903555535 64720812331093988855333303)
    ·
      refine ⟨97081218496640983282999955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64720812331093988855333303 97081218496640983282999955)
      ·
        refine ⟨145621827744961474924499933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97081218496640983282999955 145621827744961474924499933)
        ·
          refine ⟨54608185404360553096687475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145621827744961474924499933 54608185404360553096687475)
          ·
            refine ⟨81912278106540829645031213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54608185404360553096687475 81912278106540829645031213)
            ·
              refine ⟨30717104289952811116886705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81912278106540829645031213 30717104289952811116886705)
              ·
                refine ⟨23037828217464608337665029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30717104289952811116886705 23037828217464608337665029)
                ·
                  refine ⟨4319592790774614063312193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23037828217464608337665029 4319592790774614063312193)
                  ·
                    refine ⟨3239694593080960547484145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319592790774614063312193 3239694593080960547484145)
                    ·
                      refine ⟨2429770944810720410613109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239694593080960547484145 2429770944810720410613109)
                      ·
                        rfl

theorem cell23_4731962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_4731962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731962 prefixEnd_4731962 := by exact prefixLift 4731962
  have htrace : WordTrace (prefixWord ++ tailWord_4731962) baseStart_4731962 baseEnd_4731962 := by
    simpa [prefixWord, tailWord_4731962, baseEnd_4731962] using wordTrace_append hprefix tailTrace_4731962
  have hstable : (prefixWord ++ tailWord_4731962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731962).length < 2 ^ (prefixWord ++ tailWord_4731962).sum := by decide
  have hdescent : baseEnd_4731962 < baseStart_4731962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731965 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4731965 : Nat := 118140960795 + 4731965 * 2 ^ 59
def prefixEnd_4731965 : Nat := 4983230072969 + 3 ^ 40 * 4731965 * 2
def baseEnd_4731965 : Nat := 2429772485252683898875595

theorem tailTrace_4731965 : CollatzResearch.WordTrace tailWord_4731965 prefixEnd_4731965 2429772485252683898875595 := by
  unfold tailWord_4731965
  simp only [CollatzResearch.WordTrace]
  refine ⟨172588942301906435126581349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115059294867937623417720899 172588942301906435126581349)
  ·
    refine ⟨32360426681607456586234003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172588942301906435126581349 32360426681607456586234003)
    ·
      refine ⟨48540640022411184879351005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32360426681607456586234003 48540640022411184879351005)
      ·
        refine ⟨18202740008404194329756627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48540640022411184879351005 18202740008404194329756627)
        ·
          refine ⟨27304110012606291494634941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18202740008404194329756627 27304110012606291494634941)
          ·
            refine ⟨10239041254727359310488103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27304110012606291494634941 10239041254727359310488103)
            ·
              refine ⟨15358561882091038965732155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239041254727359310488103 15358561882091038965732155)
              ·
                refine ⟨23037842823136558448598233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15358561882091038965732155 23037842823136558448598233)
                ·
                  refine ⟨17278382117352418836448675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23037842823136558448598233 17278382117352418836448675)
                  ·
                    refine ⟨25917573176028628254673013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17278382117352418836448675 25917573176028628254673013)
                    ·
                      refine ⟨2429772485252683898875595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25917573176028628254673013 2429772485252683898875595)
                      ·
                        rfl

theorem cell23_4731965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4731965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731965 prefixEnd_4731965 := by exact prefixLift 4731965
  have htrace : WordTrace (prefixWord ++ tailWord_4731965) baseStart_4731965 baseEnd_4731965 := by
    simpa [prefixWord, tailWord_4731965, baseEnd_4731965] using wordTrace_append hprefix tailTrace_4731965
  have hstable : (prefixWord ++ tailWord_4731965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731965).length < 2 ^ (prefixWord ++ tailWord_4731965).sum := by decide
  have hdescent : baseEnd_4731965 < baseStart_4731965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731985 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 5]
def baseStart_4731985 : Nat := 118140960795 + 4731985 * 2 ^ 59
def prefixEnd_4731985 : Nat := 4983230072969 + 3 ^ 40 * 4731985 * 2
def baseEnd_4731985 : Nat := 269975861651752646736167

theorem tailTrace_4731985 : CollatzResearch.WordTrace tailWord_4731985 prefixEnd_4731985 269975861651752646736167 := by
  unfold tailWord_4731985
  simp only [CollatzResearch.WordTrace]
  refine ⟨172589671761833978542309409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115059781174555985694872939 172589671761833978542309409)
  ·
    refine ⟨129442253821375483906732057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172589671761833978542309409 129442253821375483906732057)
    ·
      refine ⟨97081690366031612930049043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129442253821375483906732057 97081690366031612930049043)
      ·
        refine ⟨145622535549047419395073565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97081690366031612930049043 145622535549047419395073565)
        ·
          refine ⟨54608450830892782273152587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145622535549047419395073565 54608450830892782273152587)
          ·
            refine ⟨81912676246339173409728881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54608450830892782273152587 81912676246339173409728881)
            ·
              refine ⟨61434507184754380057296661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81912676246339173409728881 61434507184754380057296661)
              ·
                refine ⟨2879742524285361565185781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61434507184754380057296661 2879742524285361565185781)
                ·
                  refine ⟨269975861651752646736167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879742524285361565185781 269975861651752646736167)
                  ·
                    rfl

theorem cell23_4731985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 5].length) (baseStart_4731985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731985 prefixEnd_4731985 := by exact prefixLift 4731985
  have htrace : WordTrace (prefixWord ++ tailWord_4731985) baseStart_4731985 baseEnd_4731985 := by
    simpa [prefixWord, tailWord_4731985, baseEnd_4731985] using wordTrace_append hprefix tailTrace_4731985
  have hstable : (prefixWord ++ tailWord_4731985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731985).length < 2 ^ (prefixWord ++ tailWord_4731985).sum := by decide
  have hdescent : baseEnd_4731985 < baseStart_4731985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731990 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4731990 : Nat := 118140960795 + 4731990 * 2 ^ 59
def prefixEnd_4731990 : Nat := 4983230072969 + 3 ^ 40 * 4731990 * 2
def baseEnd_4731990 : Nat := 2429785322269046301062981

theorem tailTrace_4731990 : CollatzResearch.WordTrace tailWord_4731990 prefixEnd_4731990 2429785322269046301062981 := by
  unfold tailWord_4731990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786865882925991524765089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115059902751210576264160949 10786865882925991524765089)
  ·
    refine ⟨8090149412194493643573817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10786865882925991524765089 8090149412194493643573817)
    ·
      refine ⟨6067612059145870232680363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8090149412194493643573817 6067612059145870232680363)
      ·
        refine ⟨9101418088718805349020545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067612059145870232680363 9101418088718805349020545)
        ·
          refine ⟨6826063566539104011765409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9101418088718805349020545 6826063566539104011765409)
          ·
            refine ⟨5119547674904328008824057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6826063566539104011765409 5119547674904328008824057)
            ·
              refine ⟨3839660756178246006618043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119547674904328008824057 3839660756178246006618043)
              ·
                refine ⟨5759491134267369009927065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839660756178246006618043 5759491134267369009927065)
                ·
                  refine ⟨4319618350700526757445299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759491134267369009927065 4319618350700526757445299)
                  ·
                    refine ⟨6479427526050790136167949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4319618350700526757445299 6479427526050790136167949)
                    ·
                      refine ⟨2429785322269046301062981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6479427526050790136167949 2429785322269046301062981)
                      ·
                        rfl

theorem cell23_4731990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4731990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731990 prefixEnd_4731990 := by exact prefixLift 4731990
  have htrace : WordTrace (prefixWord ++ tailWord_4731990) baseStart_4731990 baseEnd_4731990 := by
    simpa [prefixWord, tailWord_4731990, baseEnd_4731990] using wordTrace_append hprefix tailTrace_4731990
  have hstable : (prefixWord ++ tailWord_4731990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731990).length < 2 ^ (prefixWord ++ tailWord_4731990).sum := by decide
  have hdescent : baseEnd_4731990 < baseStart_4731990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732015 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 2, 5]
def baseStart_4732015 : Nat := 118140960795 + 4732015 * 2 ^ 59
def prefixEnd_4732015 : Nat := 4983230072969 + 3 ^ 40 * 4732015 * 2
def baseEnd_4732015 : Nat := 809932719761802901083455

theorem tailTrace_4732015 : CollatzResearch.WordTrace tailWord_4732015 prefixEnd_4732015 809932719761802901083455 := by
  unfold tailWord_4732015
  simp only [CollatzResearch.WordTrace]
  refine ⟨172590765951725293665901499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115060510634483529110600999 172590765951725293665901499)
  ·
    refine ⟨258886148927587940498852249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172590765951725293665901499 258886148927587940498852249)
    ·
      refine ⟨194164611695690955374139187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258886148927587940498852249 194164611695690955374139187)
      ·
        refine ⟨291246917543536433061208781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194164611695690955374139187 291246917543536433061208781)
        ·
          refine ⟨109217594078826162397953293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291246917543536433061208781 109217594078826162397953293)
          ·
            refine ⟨40956597779559810899232485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109217594078826162397953293 40956597779559810899232485)
            ·
              refine ⟨7679362083667464543606091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40956597779559810899232485 7679362083667464543606091)
              ·
                refine ⟨11519043125501196815409137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679362083667464543606091 11519043125501196815409137)
                ·
                  refine ⟨8639282344125897611556853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519043125501196815409137 8639282344125897611556853)
                  ·
                    refine ⟨809932719761802901083455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8639282344125897611556853 809932719761802901083455)
                    ·
                      rfl

theorem cell23_4732015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_4732015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732015 prefixEnd_4732015 := by exact prefixLift 4732015
  have htrace : WordTrace (prefixWord ++ tailWord_4732015) baseStart_4732015 baseEnd_4732015 := by
    simpa [prefixWord, tailWord_4732015, baseEnd_4732015] using wordTrace_append hprefix tailTrace_4732015
  have hstable : (prefixWord ++ tailWord_4732015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732015).length < 2 ^ (prefixWord ++ tailWord_4732015).sum := by decide
  have hdescent : baseEnd_4732015 < baseStart_4732015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732035 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4]
def baseStart_4732035 : Nat := 118140960795 + 4732035 * 2 ^ 59
def prefixEnd_4732035 : Nat := 4983230072969 + 3 ^ 40 * 4732035 * 2
def baseEnd_4732035 : Nat := 2429808428898498625000273

theorem tailTrace_4732035 : CollatzResearch.WordTrace tailWord_4732035 prefixEnd_4732035 2429808428898498625000273 := by
  unfold tailWord_4732035
  simp only [CollatzResearch.WordTrace]
  refine ⟨172591495411652837081629559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115060996941101891387753039 172591495411652837081629559)
  ·
    refine ⟨258887243117479255622444339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172591495411652837081629559 258887243117479255622444339)
    ·
      refine ⟨388330864676218883433666509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258887243117479255622444339 388330864676218883433666509)
      ·
        refine ⟨145624074253582081287624941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388330864676218883433666509 145624074253582081287624941)
        ·
          refine ⟨54609027845093280482859353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145624074253582081287624941 54609027845093280482859353)
          ·
            refine ⟨40956770883819960362144515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54609027845093280482859353 40956770883819960362144515)
            ·
              refine ⟨61435156325729940543216773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40956770883819960362144515 61435156325729940543216773)
              ·
                refine ⟨11519091811074363851853145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61435156325729940543216773 11519091811074363851853145)
                ·
                  refine ⟨8639318858305772888889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519091811074363851853145 8639318858305772888889859)
                  ·
                    refine ⟨12958978287458659333334789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8639318858305772888889859 12958978287458659333334789)
                    ·
                      refine ⟨2429808428898498625000273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12958978287458659333334789 2429808428898498625000273)
                      ·
                        rfl

theorem cell23_4732035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_4732035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732035 prefixEnd_4732035 := by exact prefixLift 4732035
  have htrace : WordTrace (prefixWord ++ tailWord_4732035) baseStart_4732035 baseEnd_4732035 := by
    simpa [prefixWord, tailWord_4732035, baseEnd_4732035] using wordTrace_append hprefix tailTrace_4732035
  have hstable : (prefixWord ++ tailWord_4732035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732035).length < 2 ^ (prefixWord ++ tailWord_4732035).sum := by decide
  have hdescent : baseEnd_4732035 < baseStart_4732035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732048 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_4732048 : Nat := 118140960795 + 4732048 * 2 ^ 59
def prefixEnd_4732048 : Nat := 4983230072969 + 3 ^ 40 * 4732048 * 2
def baseEnd_4732048 : Nat := 2429815104147007074137713

theorem tailTrace_4732048 : CollatzResearch.WordTrace tailWord_4732048 prefixEnd_4732048 2429815104147007074137713 := by
  unfold tailWord_4732048
  simp only [CollatzResearch.WordTrace]
  refine ⟨86295984780302870150926399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115061313040403826867901865 86295984780302870150926399)
  ·
    refine ⟨129443977170454305226389599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86295984780302870150926399 129443977170454305226389599)
    ·
      refine ⟨194165965755681457839584399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129443977170454305226389599 194165965755681457839584399)
      ·
        refine ⟨291248948633522186759376599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194165965755681457839584399 291248948633522186759376599)
        ·
          refine ⟨436873422950283280139064899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291248948633522186759376599 436873422950283280139064899)
          ·
            refine ⟨655310134425424920208597349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436873422950283280139064899 655310134425424920208597349)
            ·
              refine ⟨122870650204767172539112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 655310134425424920208597349 122870650204767172539112003)
              ·
                refine ⟨184305975307150758808668005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122870650204767172539112003 184305975307150758808668005)
                ·
                  refine ⟨34557370370090767276625251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184305975307150758808668005 34557370370090767276625251)
                  ·
                    refine ⟨51836055555136150914937877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34557370370090767276625251 51836055555136150914937877)
                    ·
                      refine ⟨2429815104147007074137713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51836055555136150914937877 2429815104147007074137713)
                      ·
                        rfl

theorem cell23_4732048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_4732048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732048 prefixEnd_4732048 := by exact prefixLift 4732048
  have htrace : WordTrace (prefixWord ++ tailWord_4732048) baseStart_4732048 baseEnd_4732048 := by
    simpa [prefixWord, tailWord_4732048, baseEnd_4732048] using wordTrace_append hprefix tailTrace_4732048
  have hstable : (prefixWord ++ tailWord_4732048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732048).length < 2 ^ (prefixWord ++ tailWord_4732048).sum := by decide
  have hdescent : baseEnd_4732048 < baseStart_4732048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732066 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4732066 : Nat := 118140960795 + 4732066 * 2 ^ 59
def prefixEnd_4732066 : Nat := 4983230072969 + 3 ^ 40 * 4732066 * 2
def baseEnd_4732066 : Nat := 809941448932929334570877

theorem tailTrace_4732066 : CollatzResearch.WordTrace tailWord_4732066 prefixEnd_4732066 809941448932929334570877 := by
  unfold tailWord_4732066
  simp only [CollatzResearch.WordTrace]
  refine ⟨43148156518635132344002013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115061750716360352917338701 43148156518635132344002013)
  ·
    refine ⟨16180558694488174629000755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43148156518635132344002013 16180558694488174629000755)
    ·
      refine ⟨24270838041732261943501133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16180558694488174629000755 24270838041732261943501133)
      ·
        refine ⟨9101564265649598228812925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24270838041732261943501133 9101564265649598228812925)
        ·
          refine ⟨3413086599618599335804847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9101564265649598228812925 3413086599618599335804847)
          ·
            refine ⟨5119629899427899003707271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413086599618599335804847 5119629899427899003707271)
            ·
              refine ⟨7679444849141848505560907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119629899427899003707271 7679444849141848505560907)
              ·
                refine ⟨11519167273712772758341361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679444849141848505560907 11519167273712772758341361)
                ·
                  refine ⟨8639375455284579568756021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519167273712772758341361 8639375455284579568756021)
                  ·
                    refine ⟨809941448932929334570877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8639375455284579568756021 809941448932929334570877)
                    ·
                      rfl

theorem cell23_4732066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4732066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732066 prefixEnd_4732066 := by exact prefixLift 4732066
  have htrace : WordTrace (prefixWord ++ tailWord_4732066) baseStart_4732066 baseEnd_4732066 := by
    simpa [prefixWord, tailWord_4732066, baseEnd_4732066] using wordTrace_append hprefix tailTrace_4732066
  have hstable : (prefixWord ++ tailWord_4732066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732066).length < 2 ^ (prefixWord ++ tailWord_4732066).sum := by decide
  have hdescent : baseEnd_4732066 < baseStart_4732066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732092 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 6]
def baseStart_4732092 : Nat := 118140960795 + 4732092 * 2 ^ 59
def prefixEnd_4732092 : Nat := 4983230072969 + 3 ^ 40 * 4732092 * 2
def baseEnd_4732092 : Nat := 269981966366200544665279

theorem tailTrace_4732092 : CollatzResearch.WordTrace tailWord_4732092 prefixEnd_4732092 269981966366200544665279 := by
  unfold tailWord_4732092
  simp only [CollatzResearch.WordTrace]
  refine ⟨86296787186223167908227265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115062382914964223877636353 86296787186223167908227265)
  ·
    refine ⟨64722590389667375931170449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86296787186223167908227265 64722590389667375931170449)
    ·
      refine ⟨48541942792250531948377837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64722590389667375931170449 48541942792250531948377837)
      ·
        refine ⟨18203228547093949480641689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48541942792250531948377837 18203228547093949480641689)
        ·
          refine ⟨13652421410320462110481267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18203228547093949480641689 13652421410320462110481267)
          ·
            refine ⟨20478632115480693165721901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13652421410320462110481267 20478632115480693165721901)
            ·
              refine ⟨7679487043305259937145713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20478632115480693165721901 7679487043305259937145713)
              ·
                refine ⟨5759615282478944952859285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7679487043305259937145713 5759615282478944952859285)
                ·
                  refine ⟨269981966366200544665279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5759615282478944952859285 269981966366200544665279)
                  ·
                    rfl

theorem cell23_4732092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_4732092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732092 prefixEnd_4732092 := by exact prefixLift 4732092
  have htrace : WordTrace (prefixWord ++ tailWord_4732092) baseStart_4732092 baseEnd_4732092 := by
    simpa [prefixWord, tailWord_4732092, baseEnd_4732092] using wordTrace_append hprefix tailTrace_4732092
  have hstable : (prefixWord ++ tailWord_4732092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732092).length < 2 ^ (prefixWord ++ tailWord_4732092).sum := by decide
  have hdescent : baseEnd_4732092 < baseStart_4732092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732146 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4732146 : Nat := 118140960795 + 4732146 * 2 ^ 59
def prefixEnd_4732146 : Nat := 4983230072969 + 3 ^ 40 * 4732146 * 2
def baseEnd_4732146 : Nat := 2429865425251147690712263

theorem tailTrace_4732146 : CollatzResearch.WordTrace tailWord_4732146 prefixEnd_4732146 2429865425251147690712263 := by
  unfold tailWord_4732146
  simp only [CollatzResearch.WordTrace]
  refine ⟨43148885978562675759730073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115063695942833802025946861 43148885978562675759730073)
  ·
    refine ⟨32361664483922006819797555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43148885978562675759730073 32361664483922006819797555)
    ·
      refine ⟨48542496725883010229696333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32361664483922006819797555 48542496725883010229696333)
      ·
        refine ⟨18203436272206128836136125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48542496725883010229696333 18203436272206128836136125)
        ·
          refine ⟨6826288602077298313551047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18203436272206128836136125 6826288602077298313551047)
          ·
            refine ⟨10239432903115947470326571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6826288602077298313551047 10239432903115947470326571)
            ·
              refine ⟨15359149354673921205489857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239432903115947470326571 15359149354673921205489857)
              ·
                refine ⟨11519362016005440904117393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15359149354673921205489857 11519362016005440904117393)
                ·
                  refine ⟨8639521512004080678088045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519362016005440904117393 8639521512004080678088045)
                  ·
                    refine ⟨3239820567001530254283017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8639521512004080678088045 3239820567001530254283017)
                    ·
                      refine ⟨2429865425251147690712263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239820567001530254283017 2429865425251147690712263)
                      ·
                        rfl

theorem cell23_4732146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4732146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732146 prefixEnd_4732146 := by exact prefixLift 4732146
  have htrace : WordTrace (prefixWord ++ tailWord_4732146) baseStart_4732146 baseEnd_4732146 := by
    simpa [prefixWord, tailWord_4732146, baseEnd_4732146] using wordTrace_append hprefix tailTrace_4732146
  have hstable : (prefixWord ++ tailWord_4732146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732146).length < 2 ^ (prefixWord ++ tailWord_4732146).sum := by decide
  have hdescent : baseEnd_4732146 < baseStart_4732146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732165 : List Nat := [1, 3, 1, 1, 2, 1, 6, 8]
def baseStart_4732165 : Nat := 118140960795 + 4732165 * 2 ^ 59
def prefixEnd_4732165 : Nat := 4983230072969 + 3 ^ 40 * 4732165 * 2
def baseEnd_4732165 : Nat := 89995377088280856162025

theorem tailTrace_4732165 : CollatzResearch.WordTrace tailWord_4732165 prefixEnd_4732165 89995377088280856162025 := by
  unfold tailWord_4732165
  simp only [CollatzResearch.WordTrace]
  refine ⟨172596236901181869283861949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115064157934121246189241299 172596236901181869283861949)
  ·
    refine ⟨64723588837943200981448231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172596236901181869283861949 64723588837943200981448231)
    ·
      refine ⟨97085383256914801472172347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64723588837943200981448231 97085383256914801472172347)
      ·
        refine ⟨145628074885372202208258521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97085383256914801472172347 145628074885372202208258521)
        ·
          refine ⟨109221056164029151656193891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145628074885372202208258521 109221056164029151656193891)
          ·
            refine ⟨163831584246043727484290837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109221056164029151656193891 163831584246043727484290837)
            ·
              refine ⟨7679605511533299725826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163831584246043727484290837 7679605511533299725826133)
              ·
                refine ⟨89995377088280856162025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7679605511533299725826133 89995377088280856162025)
                ·
                  rfl

theorem cell23_4732165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 8].length) (baseStart_4732165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732165 prefixEnd_4732165 := by exact prefixLift 4732165
  have htrace : WordTrace (prefixWord ++ tailWord_4732165) baseStart_4732165 baseEnd_4732165 := by
    simpa [prefixWord, tailWord_4732165, baseEnd_4732165] using wordTrace_append hprefix tailTrace_4732165
  have hstable : (prefixWord ++ tailWord_4732165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732165).length < 2 ^ (prefixWord ++ tailWord_4732165).sum := by decide
  have hdescent : baseEnd_4732165 < baseStart_4732165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732189 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4732189 : Nat := 118140960795 + 4732189 * 2 ^ 59
def prefixEnd_4732189 : Nat := 4983230072969 + 3 ^ 40 * 4732189 * 2
def baseEnd_4732189 : Nat := 2429887504919291022474565

theorem tailTrace_4732189 : CollatzResearch.WordTrace tailWord_4732189 prefixEnd_4732189 2429887504919291022474565 := by
  unfold tailWord_4732189
  simp only [CollatzResearch.WordTrace]
  refine ⟨172597112253094921382735621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115064741502063280921823747 172597112253094921382735621)
  ·
    refine ⟨32361958547455297759262929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172597112253094921382735621 32361958547455297759262929)
    ·
      refine ⟨24271468910591473319447197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32361958547455297759262929 24271468910591473319447197)
      ·
        refine ⟨9101800841471802494792699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24271468910591473319447197 9101800841471802494792699)
        ·
          refine ⟨13652701262207703742189049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101800841471802494792699 13652701262207703742189049)
          ·
            refine ⟨10239525946655777806641787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13652701262207703742189049 10239525946655777806641787)
            ·
              refine ⟨15359288919983666709962681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239525946655777806641787 15359288919983666709962681)
              ·
                refine ⟨11519466689987750032472011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15359288919983666709962681 11519466689987750032472011)
                ·
                  refine ⟨17279200034981625048708017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11519466689987750032472011 17279200034981625048708017)
                  ·
                    refine ⟨12959400026236218786531013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17279200034981625048708017 12959400026236218786531013)
                    ·
                      refine ⟨2429887504919291022474565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12959400026236218786531013 2429887504919291022474565)
                      ·
                        rfl

theorem cell23_4732189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4732189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732189 prefixEnd_4732189 := by exact prefixLift 4732189
  have htrace : WordTrace (prefixWord ++ tailWord_4732189) baseStart_4732189 baseEnd_4732189 := by
    simpa [prefixWord, tailWord_4732189, baseEnd_4732189] using wordTrace_append hprefix tailTrace_4732189
  have hstable : (prefixWord ++ tailWord_4732189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732189).length < 2 ^ (prefixWord ++ tailWord_4732189).sum := by decide
  have hdescent : baseEnd_4732189 < baseStart_4732189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732196 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_4732196 : Nat := 118140960795 + 4732196 * 2 ^ 59
def prefixEnd_4732196 : Nat := 4983230072969 + 3 ^ 40 * 4732196 * 2
def baseEnd_4732196 : Nat := 2429891099283872495087033

theorem tailTrace_4732196 : CollatzResearch.WordTrace tailWord_4732196 prefixEnd_4732196 2429891099283872495087033 := by
  unfold tailWord_4732196
  simp only [CollatzResearch.WordTrace]
  refine ⟨86298683782034780789120221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115064911709379707718826961 86298683782034780789120221)
  ·
    refine ⟨32362006418263042795920083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86298683782034780789120221 32362006418263042795920083)
    ·
      refine ⟨48543009627394564193880125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32362006418263042795920083 48543009627394564193880125)
      ·
        refine ⟨18203628610272961572705047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48543009627394564193880125 18203628610272961572705047)
        ·
          refine ⟨27305442915409442359057571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18203628610272961572705047 27305442915409442359057571)
          ·
            refine ⟨40958164373114163538586357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27305442915409442359057571 40958164373114163538586357)
            ·
              refine ⟨3839827909979452831742471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40958164373114163538586357 3839827909979452831742471)
              ·
                refine ⟨5759741864969179247613707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839827909979452831742471 5759741864969179247613707)
                ·
                  refine ⟨8639612797453768871420561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5759741864969179247613707 8639612797453768871420561)
                  ·
                    refine ⟨6479709598090326653565421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8639612797453768871420561 6479709598090326653565421)
                    ·
                      refine ⟨2429891099283872495087033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6479709598090326653565421 2429891099283872495087033)
                      ·
                        rfl

theorem cell23_4732196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_4732196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732196 prefixEnd_4732196 := by exact prefixLift 4732196
  have htrace : WordTrace (prefixWord ++ tailWord_4732196) baseStart_4732196 baseEnd_4732196 := by
    simpa [prefixWord, tailWord_4732196, baseEnd_4732196] using wordTrace_append hprefix tailTrace_4732196
  have hstable : (prefixWord ++ tailWord_4732196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732196).length < 2 ^ (prefixWord ++ tailWord_4732196).sum := by decide
  have hdescent : baseEnd_4732196 < baseStart_4732196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732210 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_4732210 : Nat := 118140960795 + 4732210 * 2 ^ 59
def prefixEnd_4732210 : Nat := 4983230072969 + 3 ^ 40 * 4732210 * 2
def baseEnd_4732210 : Nat := 2429898288013035440311969

theorem tailTrace_4732210 : CollatzResearch.WordTrace tailWord_4732210 prefixEnd_4732210 2429898288013035440311969 := by
  unfold tailWord_4732210
  simp only [CollatzResearch.WordTrace]
  refine ⟨43149469546504710492312521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115065252124012561312833389 43149469546504710492312521)
  ·
    refine ⟨32362102159878532869234391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43149469546504710492312521 32362102159878532869234391)
    ·
      refine ⟨48543153239817799303851587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32362102159878532869234391 48543153239817799303851587)
      ·
        refine ⟨72814729859726698955777381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48543153239817799303851587 72814729859726698955777381)
        ·
          refine ⟨13652761848698756054208259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72814729859726698955777381 13652761848698756054208259)
          ·
            refine ⟨20479142773048134081312389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13652761848698756054208259 20479142773048134081312389)
            ·
              refine ⟨3839839269946525140246073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20479142773048134081312389 3839839269946525140246073)
              ·
                refine ⟨2879879452459893855184555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839839269946525140246073 2879879452459893855184555)
                ·
                  refine ⟨4319819178689840782776833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879879452459893855184555 4319819178689840782776833)
                  ·
                    refine ⟨3239864384017380587082625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319819178689840782776833 3239864384017380587082625)
                    ·
                      refine ⟨2429898288013035440311969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239864384017380587082625 2429898288013035440311969)
                      ·
                        rfl

theorem cell23_4732210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_4732210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732210 prefixEnd_4732210 := by exact prefixLift 4732210
  have htrace : WordTrace (prefixWord ++ tailWord_4732210) baseStart_4732210 baseEnd_4732210 := by
    simpa [prefixWord, tailWord_4732210, baseEnd_4732210] using wordTrace_append hprefix tailTrace_4732210
  have hstable : (prefixWord ++ tailWord_4732210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732210).length < 2 ^ (prefixWord ++ tailWord_4732210).sum := by decide
  have hdescent : baseEnd_4732210 < baseStart_4732210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732212 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_4732212 : Nat := 118140960795 + 4732212 * 2 ^ 59
def prefixEnd_4732212 : Nat := 4983230072969 + 3 ^ 40 * 4732212 * 2
def baseEnd_4732212 : Nat := 809966438324781477495653

theorem tailTrace_4732212 : CollatzResearch.WordTrace tailWord_4732212 prefixEnd_4732212 809966438324781477495653 := by
  unfold tailWord_4732212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86298975566005798155411445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115065300754674397540548593 86298975566005798155411445)
  ·
    refine ⟨8090528959313043577069823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86298975566005798155411445 8090528959313043577069823)
    ·
      refine ⟨12135793438969565365604735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8090528959313043577069823 12135793438969565365604735)
      ·
        refine ⟨18203690158454348048407103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12135793438969565365604735 18203690158454348048407103)
        ·
          refine ⟨27305535237681522072610655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18203690158454348048407103 27305535237681522072610655)
          ·
            refine ⟨40958302856522283108915983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27305535237681522072610655 40958302856522283108915983)
            ·
              refine ⟨61437454284783424663373975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40958302856522283108915983 61437454284783424663373975)
              ·
                refine ⟨92156181427175136995060963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61437454284783424663373975 92156181427175136995060963)
                ·
                  refine ⟨138234272140762705492591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92156181427175136995060963 138234272140762705492591445)
                  ·
                    refine ⟨809966438324781477495653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138234272140762705492591445 809966438324781477495653)
                    ·
                      rfl

theorem cell23_4732212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_4732212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732212 prefixEnd_4732212 := by exact prefixLift 4732212
  have htrace : WordTrace (prefixWord ++ tailWord_4732212) baseStart_4732212 baseEnd_4732212 := by
    simpa [prefixWord, tailWord_4732212, baseEnd_4732212] using wordTrace_append hprefix tailTrace_4732212
  have hstable : (prefixWord ++ tailWord_4732212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732212).length < 2 ^ (prefixWord ++ tailWord_4732212).sum := by decide
  have hdescent : baseEnd_4732212 < baseStart_4732212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732249 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 4, 2]
def baseStart_4732249 : Nat := 118140960795 + 4732249 * 2 ^ 59
def prefixEnd_4732249 : Nat := 4983230072969 + 3 ^ 40 * 4732249 * 2
def baseEnd_4732249 : Nat := 2429918313758560787724289

theorem tailTrace_4732249 : CollatzResearch.WordTrace tailWord_4732249 prefixEnd_4732249 2429918313758560787724289 := by
  unfold tailWord_4732249
  simp only [CollatzResearch.WordTrace]
  refine ⟨172599300632877551629919801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115066200421918367753279867 172599300632877551629919801)
  ·
    refine ⟨129449475474658163722439851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172599300632877551629919801 129449475474658163722439851)
    ·
      refine ⟨194174213211987245583659777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129449475474658163722439851 194174213211987245583659777)
      ·
        refine ⟨145630659908990434187744833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194174213211987245583659777 145630659908990434187744833)
        ·
          refine ⟨109222994931742825640808625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145630659908990434187744833 109222994931742825640808625)
          ·
            refine ⟨81917246198807119230606469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109222994931742825640808625 81917246198807119230606469)
            ·
              refine ⟨15359483662276334855738713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81917246198807119230606469 15359483662276334855738713)
              ·
                refine ⟨11519612746707251141804035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15359483662276334855738713 11519612746707251141804035)
                ·
                  refine ⟨17279419120060876712706053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11519612746707251141804035 17279419120060876712706053)
                  ·
                    refine ⟨3239891085011414383632385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17279419120060876712706053 3239891085011414383632385)
                    ·
                      refine ⟨2429918313758560787724289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239891085011414383632385 2429918313758560787724289)
                      ·
                        rfl

theorem cell23_4732249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_4732249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732249 prefixEnd_4732249 := by exact prefixLift 4732249
  have htrace : WordTrace (prefixWord ++ tailWord_4732249) baseStart_4732249 baseEnd_4732249 := by
    simpa [prefixWord, tailWord_4732249, baseEnd_4732249] using wordTrace_append hprefix tailTrace_4732249
  have hstable : (prefixWord ++ tailWord_4732249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732249).length < 2 ^ (prefixWord ++ tailWord_4732249).sum := by decide
  have hdescent : baseEnd_4732249 < baseStart_4732249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732255 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 11]
def baseStart_4732255 : Nat := 118140960795 + 4732255 * 2 ^ 59
def prefixEnd_4732255 : Nat := 4983230072969 + 3 ^ 40 * 4732255 * 2
def baseEnd_4732255 : Nat := 269991266071387529361029

theorem tailTrace_4732255 : CollatzResearch.WordTrace tailWord_4732255 prefixEnd_4732255 269991266071387529361029 := by
  unfold tailWord_4732255
  simp only [CollatzResearch.WordTrace]
  refine ⟨172599519470855814654638219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115066346313903876436425479 172599519470855814654638219)
  ·
    refine ⟨258899279206283721981957329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172599519470855814654638219 258899279206283721981957329)
    ·
      refine ⟨194174459404712791486467997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258899279206283721981957329 194174459404712791486467997)
      ·
        refine ⟨72815422276767296807425499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194174459404712791486467997 72815422276767296807425499)
        ·
          refine ⟨109223133415150945211138249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72815422276767296807425499 109223133415150945211138249)
          ·
            refine ⟨81917350061363208908353687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109223133415150945211138249 81917350061363208908353687)
            ·
              refine ⟨122876025092044813362530531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81917350061363208908353687 122876025092044813362530531)
              ·
                refine ⟨184314037638067220043795797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122876025092044813362530531 184314037638067220043795797)
                ·
                  refine ⟨269991266071387529361029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 184314037638067220043795797 269991266071387529361029)
                  ·
                    rfl

theorem cell23_4732255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 11].length) (baseStart_4732255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732255 prefixEnd_4732255 := by exact prefixLift 4732255
  have htrace : WordTrace (prefixWord ++ tailWord_4732255) baseStart_4732255 baseEnd_4732255 := by
    simpa [prefixWord, tailWord_4732255, baseEnd_4732255] using wordTrace_append hprefix tailTrace_4732255
  have hstable : (prefixWord ++ tailWord_4732255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732255).length < 2 ^ (prefixWord ++ tailWord_4732255).sum := by decide
  have hdescent : baseEnd_4732255 < baseStart_4732255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732265 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_4732265 : Nat := 118140960795 + 4732265 * 2 ^ 59
def prefixEnd_4732265 : Nat := 4983230072969 + 3 ^ 40 * 4732265 * 2
def baseEnd_4732265 : Nat := 2429926529449032725124215

theorem tailTrace_4732265 : CollatzResearch.WordTrace tailWord_4732265 prefixEnd_4732265 2429926529449032725124215 := by
  unfold tailWord_4732265
  simp only [CollatzResearch.WordTrace]
  refine ⟨172599884200819586362502249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115066589467213057575001499 172599884200819586362502249)
  ·
    refine ⟨129449913150614689771876687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172599884200819586362502249 129449913150614689771876687)
    ·
      refine ⟨194174869725922034657815031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129449913150614689771876687 194174869725922034657815031)
      ·
        refine ⟨291262304588883051986722547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194174869725922034657815031 291262304588883051986722547)
        ·
          refine ⟨436893456883324577980083821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291262304588883051986722547 436893456883324577980083821)
          ·
            refine ⟨163835046331246716742531433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436893456883324577980083821 163835046331246716742531433)
            ·
              refine ⟨122876284748435037556898575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163835046331246716742531433 122876284748435037556898575)
              ·
                refine ⟨184314427122652556335347863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122876284748435037556898575 184314427122652556335347863)
                ·
                  refine ⟨276471640683978834503021795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184314427122652556335347863 276471640683978834503021795)
                  ·
                    refine ⟨414707461025968251754532693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276471640683978834503021795 414707461025968251754532693)
                    ·
                      refine ⟨2429926529449032725124215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 414707461025968251754532693 2429926529449032725124215)
                      ·
                        rfl

theorem cell23_4732265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_4732265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732265 prefixEnd_4732265 := by exact prefixLift 4732265
  have htrace : WordTrace (prefixWord ++ tailWord_4732265) baseStart_4732265 baseEnd_4732265 := by
    simpa [prefixWord, tailWord_4732265, baseEnd_4732265] using wordTrace_append hprefix tailTrace_4732265
  have hstable : (prefixWord ++ tailWord_4732265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732265).length < 2 ^ (prefixWord ++ tailWord_4732265).sum := by decide
  have hdescent : baseEnd_4732265 < baseStart_4732265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732272 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 7]
def baseStart_4732272 : Nat := 118140960795 + 4732272 * 2 ^ 59
def prefixEnd_4732272 : Nat := 4983230072969 + 3 ^ 40 * 4732272 * 2
def baseEnd_4732272 : Nat := 269992235979290466415187

theorem tailTrace_4732272 : CollatzResearch.WordTrace tailWord_4732272 prefixEnd_4732272 269992235979290466415187 := by
  unfold tailWord_4732272
  simp only [CollatzResearch.WordTrace]
  refine ⟨86300069755897113279003535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115066759674529484372004713 86300069755897113279003535)
  ·
    refine ⟨129450104633845669918505303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86300069755897113279003535 129450104633845669918505303)
    ·
      refine ⟨194175156950768504877757955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129450104633845669918505303 194175156950768504877757955)
      ·
        refine ⟨291262735426152757316636933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194175156950768504877757955 291262735426152757316636933)
        ·
          refine ⟨54611762892403641996869425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291262735426152757316636933 54611762892403641996869425)
          ·
            refine ⟨40958822169302731497652069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54611762892403641996869425 40958822169302731497652069)
            ·
              refine ⟨7679779156744262155809763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40958822169302731497652069 7679779156744262155809763)
              ·
                refine ⟨11519668735116393233714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679779156744262155809763 11519668735116393233714645)
                ·
                  refine ⟨269992235979290466415187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11519668735116393233714645 269992235979290466415187)
                  ·
                    rfl

theorem cell23_4732272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_4732272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732272 prefixEnd_4732272 := by exact prefixLift 4732272
  have htrace : WordTrace (prefixWord ++ tailWord_4732272) baseStart_4732272 baseEnd_4732272 := by
    simpa [prefixWord, tailWord_4732272, baseEnd_4732272] using wordTrace_append hprefix tailTrace_4732272
  have hstable : (prefixWord ++ tailWord_4732272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732272).length < 2 ^ (prefixWord ++ tailWord_4732272).sum := by decide
  have hdescent : baseEnd_4732272 < baseStart_4732272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732275 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_4732275 : Nat := 118140960795 + 4732275 * 2 ^ 59
def prefixEnd_4732275 : Nat := 4983230072969 + 3 ^ 40 * 4732275 * 2
def baseEnd_4732275 : Nat := 2429931664255577685999169

theorem tailTrace_4732275 : CollatzResearch.WordTrace tailWord_4732275 prefixEnd_4732275 2429931664255577685999169 := by
  unfold tailWord_4732275
  simp only [CollatzResearch.WordTrace]
  refine ⟨172600248930783358070366279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115066832620522238713577519 172600248930783358070366279)
  ·
    refine ⟨258900373396175037105549419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172600248930783358070366279 258900373396175037105549419)
    ·
      refine ⟨388350560094262555658324129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258900373396175037105549419 388350560094262555658324129)
      ·
        refine ⟨291262920070696916743743097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388350560094262555658324129 291262920070696916743743097)
        ·
          refine ⟨218447190053022687557807323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291262920070696916743743097 218447190053022687557807323)
          ·
            refine ⟨327670785079534031336710985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218447190053022687557807323 327670785079534031336710985)
            ·
              refine ⟨245753088809650523502533239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327670785079534031336710985 245753088809650523502533239)
              ·
                refine ⟨368629633214475785253799859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245753088809650523502533239 368629633214475785253799859)
                ·
                  refine ⟨552944449821713677880699789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368629633214475785253799859 552944449821713677880699789)
                  ·
                    refine ⟨207354168683142629205262421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552944449821713677880699789 207354168683142629205262421)
                    ·
                      refine ⟨2429931664255577685999169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 207354168683142629205262421 2429931664255577685999169)
                      ·
                        rfl

theorem cell23_4732275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_4732275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732275 prefixEnd_4732275 := by exact prefixLift 4732275
  have htrace : WordTrace (prefixWord ++ tailWord_4732275) baseStart_4732275 baseEnd_4732275 := by
    simpa [prefixWord, tailWord_4732275, baseEnd_4732275] using wordTrace_append hprefix tailTrace_4732275
  have hstable : (prefixWord ++ tailWord_4732275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732275).length < 2 ^ (prefixWord ++ tailWord_4732275).sum := by decide
  have hdescent : baseEnd_4732275 < baseStart_4732275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732283 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 2, 2, 2]
def baseStart_4732283 : Nat := 118140960795 + 4732283 * 2 ^ 59
def prefixEnd_4732283 : Nat := 4983230072969 + 3 ^ 40 * 4732283 * 2
def baseEnd_4732283 : Nat := 2429935772100813654699133

theorem tailTrace_4732283 : CollatzResearch.WordTrace tailWord_4732283 prefixEnd_4732283 2429935772100813654699133 := by
  unfold tailWord_4732283
  simp only [CollatzResearch.WordTrace]
  refine ⟨172600540714754375436657503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115067027143169583624438335 172600540714754375436657503)
  ·
    refine ⟨258900811072131563154986255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172600540714754375436657503 258900811072131563154986255)
    ·
      refine ⟨388351216608197344732479383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258900811072131563154986255 388351216608197344732479383)
      ·
        refine ⟨582526824912296017098719075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388351216608197344732479383 582526824912296017098719075)
        ·
          refine ⟨873790237368444025648078613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582526824912296017098719075 873790237368444025648078613)
          ·
            refine ⟨40958917376645813702253685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 873790237368444025648078613 40958917376645813702253685)
            ·
              refine ⟨3839898504060545034586283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40958917376645813702253685 3839898504060545034586283)
              ·
                refine ⟨5759847756090817551879425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839898504060545034586283 5759847756090817551879425)
                ·
                  refine ⟨4319885817068113163909569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759847756090817551879425 4319885817068113163909569)
                  ·
                    refine ⟨3239914362801084872932177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319885817068113163909569 3239914362801084872932177)
                    ·
                      refine ⟨2429935772100813654699133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239914362801084872932177 2429935772100813654699133)
                      ·
                        rfl

theorem cell23_4732283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 2, 2].length) (baseStart_4732283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732283 prefixEnd_4732283 := by exact prefixLift 4732283
  have htrace : WordTrace (prefixWord ++ tailWord_4732283) baseStart_4732283 baseEnd_4732283 := by
    simpa [prefixWord, tailWord_4732283, baseEnd_4732283] using wordTrace_append hprefix tailTrace_4732283
  have hstable : (prefixWord ++ tailWord_4732283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732283).length < 2 ^ (prefixWord ++ tailWord_4732283).sum := by decide
  have hdescent : baseEnd_4732283 < baseStart_4732283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732319 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 2, 5]
def baseStart_4732319 : Nat := 118140960795 + 4732319 * 2 ^ 59
def prefixEnd_4732319 : Nat := 4983230072969 + 3 ^ 40 * 4732319 * 2
def baseEnd_4732319 : Nat := 809984752468125171282989

theorem tailTrace_4732319 : CollatzResearch.WordTrace tailWord_4732319 prefixEnd_4732319 809984752468125171282989 := by
  unfold tailWord_4732319
  simp only [CollatzResearch.WordTrace]
  refine ⟨172601853742623953584968011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115067902495082635723312007 172601853742623953584968011)
  ·
    refine ⟨258902780613935930377452017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172601853742623953584968011 258902780613935930377452017)
    ·
      refine ⟨194177085460451947783089013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258902780613935930377452017 194177085460451947783089013)
      ·
        refine ⟨18204101761917370104664595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194177085460451947783089013 18204101761917370104664595)
        ·
          refine ⟨27306152642876055156996893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18204101761917370104664595 27306152642876055156996893)
          ·
            refine ⟨10239807241078520683873835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27306152642876055156996893 10239807241078520683873835)
            ·
              refine ⟨15359710861617781025810753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239807241078520683873835 15359710861617781025810753)
              ·
                refine ⟨11519783146213335769358065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15359710861617781025810753 11519783146213335769358065)
                ·
                  refine ⟨8639837359660001827018549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519783146213335769358065 8639837359660001827018549)
                  ·
                    refine ⟨809984752468125171282989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8639837359660001827018549 809984752468125171282989)
                    ·
                      rfl

theorem cell23_4732319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_4732319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732319 prefixEnd_4732319 := by exact prefixLift 4732319
  have htrace : WordTrace (prefixWord ++ tailWord_4732319) baseStart_4732319 baseEnd_4732319 := by
    simpa [prefixWord, tailWord_4732319, baseEnd_4732319] using wordTrace_append hprefix tailTrace_4732319
  have hstable : (prefixWord ++ tailWord_4732319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732319).length < 2 ^ (prefixWord ++ tailWord_4732319).sum := by decide
  have hdescent : baseEnd_4732319 < baseStart_4732319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732339 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 4, 2]
def baseStart_4732339 : Nat := 118140960795 + 4732339 * 2 ^ 59
def prefixEnd_4732339 : Nat := 4983230072969 + 3 ^ 40 * 4732339 * 2
def baseEnd_4732339 : Nat := 2429964527017465435598875

theorem tailTrace_4732339 : CollatzResearch.WordTrace tailWord_4732339 prefixEnd_4732339 2429964527017465435598875 := by
  unfold tailWord_4732339
  simp only [CollatzResearch.WordTrace]
  refine ⟨172602583202551497000696071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115068388801700998000464047 172602583202551497000696071)
  ·
    refine ⟨258903874803827245501044107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172602583202551497000696071 258903874803827245501044107)
    ·
      refine ⟨388355812205740868251566161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258903874803827245501044107 388355812205740868251566161)
      ·
        refine ⟨291266859154305651188674621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388355812205740868251566161 291266859154305651188674621)
        ·
          refine ⟨109225072182864619195752983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291266859154305651188674621 109225072182864619195752983)
          ·
            refine ⟨163837608274296928793629475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109225072182864619195752983 163837608274296928793629475)
            ·
              refine ⟨245756412411445393190444213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163837608274296928793629475 245756412411445393190444213)
              ·
                refine ⟨23039663663573005611604145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 245756412411445393190444213 23039663663573005611604145)
                ·
                  refine ⟨17279747747679754208703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23039663663573005611604145 17279747747679754208703109)
                  ·
                    refine ⟨3239952702689953914131833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17279747747679754208703109 3239952702689953914131833)
                    ·
                      refine ⟨2429964527017465435598875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239952702689953914131833 2429964527017465435598875)
                      ·
                        rfl

theorem cell23_4732339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4, 2].length) (baseStart_4732339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732339 prefixEnd_4732339 := by exact prefixLift 4732339
  have htrace : WordTrace (prefixWord ++ tailWord_4732339) baseStart_4732339 baseEnd_4732339 := by
    simpa [prefixWord, tailWord_4732339, baseEnd_4732339] using wordTrace_append hprefix tailTrace_4732339
  have hstable : (prefixWord ++ tailWord_4732339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732339).length < 2 ^ (prefixWord ++ tailWord_4732339).sum := by decide
  have hdescent : baseEnd_4732339 < baseStart_4732339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732349 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_4732349 : Nat := 118140960795 + 4732349 * 2 ^ 59
def prefixEnd_4732349 : Nat := 4983230072969 + 3 ^ 40 * 4732349 * 2
def baseEnd_4732349 : Nat := 809989887274670132157943

theorem tailTrace_4732349 : CollatzResearch.WordTrace tailWord_4732349 prefixEnd_4732349 809989887274670132157943 := by
  unfold tailWord_4732349
  simp only [CollatzResearch.WordTrace]
  refine ⟨172602947932515268708560101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115068631955010179139040067 172602947932515268708560101)
  ·
    refine ⟨32363052737346612882855019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172602947932515268708560101 32363052737346612882855019)
    ·
      refine ⟨48544579106019919324282529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32363052737346612882855019 48544579106019919324282529)
      ·
        refine ⟨36408434329514939493211897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48544579106019919324282529 36408434329514939493211897)
        ·
          refine ⟨27306325747136204619908923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36408434329514939493211897 27306325747136204619908923)
          ·
            refine ⟨40959488620704306929863385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27306325747136204619908923 40959488620704306929863385)
            ·
              refine ⟨30719616465528230197397539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40959488620704306929863385 30719616465528230197397539)
              ·
                refine ⟨46079424698292345296096309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30719616465528230197397539 46079424698292345296096309)
                ·
                  refine ⟨4319946065464907371509029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46079424698292345296096309 4319946065464907371509029)
                  ·
                    refine ⟨809989887274670132157943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319946065464907371509029 809989887274670132157943)
                    ·
                      rfl

theorem cell23_4732349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_4732349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732349 prefixEnd_4732349 := by exact prefixLift 4732349
  have htrace : WordTrace (prefixWord ++ tailWord_4732349) baseStart_4732349 baseEnd_4732349 := by
    simpa [prefixWord, tailWord_4732349, baseEnd_4732349] using wordTrace_append hprefix tailTrace_4732349
  have hstable : (prefixWord ++ tailWord_4732349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732349).length < 2 ^ (prefixWord ++ tailWord_4732349).sum := by decide
  have hdescent : baseEnd_4732349 < baseStart_4732349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732352 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_4732352 : Nat := 118140960795 + 4732352 * 2 ^ 59
def prefixEnd_4732352 : Nat := 4983230072969 + 3 ^ 40 * 4732352 * 2
def baseEnd_4732352 : Nat := 2429971202265973884736315

theorem tailTrace_4732352 : CollatzResearch.WordTrace tailWord_4732352 prefixEnd_4732352 2429971202265973884736315 := by
  unfold tailWord_4732352
  simp only [CollatzResearch.WordTrace]
  refine ⟨86301528675752200110459655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115068704901002933480612873 86301528675752200110459655)
  ·
    refine ⟨129452293013628300165689483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86301528675752200110459655 129452293013628300165689483)
    ·
      refine ⟨194178439520442450248534225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129452293013628300165689483 194178439520442450248534225)
      ·
        refine ⟨145633829640331837686400669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194178439520442450248534225 145633829640331837686400669)
        ·
          refine ⟨54612686115124439132400251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145633829640331837686400669 54612686115124439132400251)
          ·
            refine ⟨81919029172686658698600377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54612686115124439132400251 81919029172686658698600377)
            ·
              refine ⟨61439271879514994023950283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81919029172686658698600377 61439271879514994023950283)
              ·
                refine ⟨92158907819272491035925425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61439271879514994023950283 92158907819272491035925425)
                ·
                  refine ⟨69119180864454368276944069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92158907819272491035925425 69119180864454368276944069)
                  ·
                    refine ⟨12959846412085194051927013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69119180864454368276944069 12959846412085194051927013)
                    ·
                      refine ⟨2429971202265973884736315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12959846412085194051927013 2429971202265973884736315)
                      ·
                        rfl

theorem cell23_4732352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_4732352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732352 prefixEnd_4732352 := by exact prefixLift 4732352
  have htrace : WordTrace (prefixWord ++ tailWord_4732352) baseStart_4732352 baseEnd_4732352 := by
    simpa [prefixWord, tailWord_4732352, baseEnd_4732352] using wordTrace_append hprefix tailTrace_4732352
  have hstable : (prefixWord ++ tailWord_4732352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732352).length < 2 ^ (prefixWord ++ tailWord_4732352).sum := by decide
  have hdescent : baseEnd_4732352 < baseStart_4732352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732356 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4732356 : Nat := 118140960795 + 4732356 * 2 ^ 59
def prefixEnd_4732356 : Nat := 4983230072969 + 3 ^ 40 * 4732356 * 2
def baseEnd_4732356 : Nat := 2429973256188591869086297

theorem tailTrace_4732356 : CollatzResearch.WordTrace tailWord_4732356 prefixEnd_4732356 2429973256188591869086297 := by
  unfold tailWord_4732356
  simp only [CollatzResearch.WordTrace]
  refine ⟨86301601621744954452032461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115068802162326605936043281 86301601621744954452032461)
  ·
    refine ⟨32363100608154357919512173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86301601621744954452032461 32363100608154357919512173)
    ·
      refine ⟨12136162728057884219817065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32363100608154357919512173 12136162728057884219817065)
      ·
        refine ⟨9102122046043413164862799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12136162728057884219817065 9102122046043413164862799)
        ·
          refine ⟨13653183069065119747294199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102122046043413164862799 13653183069065119747294199)
          ·
            refine ⟨20479774603597679620941299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13653183069065119747294199 20479774603597679620941299)
            ·
              refine ⟨30719661905396519431411949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20479774603597679620941299 30719661905396519431411949)
              ·
                refine ⟨11519873214523694786779481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30719661905396519431411949 11519873214523694786779481)
                ·
                  refine ⟨8639904910892771090084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519873214523694786779481 8639904910892771090084611)
                  ·
                    refine ⟨12959857366339156635126917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8639904910892771090084611 12959857366339156635126917)
                    ·
                      refine ⟨2429973256188591869086297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12959857366339156635126917 2429973256188591869086297)
                      ·
                        rfl

theorem cell23_4732356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4732356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732356 prefixEnd_4732356 := by exact prefixLift 4732356
  have htrace : WordTrace (prefixWord ++ tailWord_4732356) baseStart_4732356 baseEnd_4732356 := by
    simpa [prefixWord, tailWord_4732356, baseEnd_4732356] using wordTrace_append hprefix tailTrace_4732356
  have hstable : (prefixWord ++ tailWord_4732356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732356).length < 2 ^ (prefixWord ++ tailWord_4732356).sum := by decide
  have hdescent : baseEnd_4732356 < baseStart_4732356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732409 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_4732409 : Nat := 118140960795 + 4732409 * 2 ^ 59
def prefixEnd_4732409 : Nat := 4983230072969 + 3 ^ 40 * 4732409 * 2
def baseEnd_4732409 : Nat := 810000156887760053907851

theorem tailTrace_4732409 : CollatzResearch.WordTrace tailWord_4732409 prefixEnd_4732409 810000156887760053907851 := by
  unfold tailWord_4732409
  simp only [CollatzResearch.WordTrace]
  refine ⟨172605136312297898955744281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115070090874865265970496187 172605136312297898955744281)
  ·
    refine ⟨129453852234223424216808211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172605136312297898955744281 129453852234223424216808211)
    ·
      refine ⟨194180778351335136325212317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129453852234223424216808211 194180778351335136325212317)
      ·
        refine ⟨72817791881750676121954619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194180778351335136325212317 72817791881750676121954619)
        ·
          refine ⟨109226687822626014182931929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72817791881750676121954619 109226687822626014182931929)
          ·
            refine ⟨81920015866969510637198947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109226687822626014182931929 81920015866969510637198947)
            ·
              refine ⟨122880023800454265955798421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81920015866969510637198947 122880023800454265955798421)
              ·
                refine ⟨5760001115646293716678051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122880023800454265955798421 5760001115646293716678051)
                ·
                  refine ⟨8640001673469440575017077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760001115646293716678051 8640001673469440575017077)
                  ·
                    refine ⟨810000156887760053907851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8640001673469440575017077 810000156887760053907851)
                    ·
                      rfl

theorem cell23_4732409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_4732409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732409 prefixEnd_4732409 := by exact prefixLift 4732409
  have htrace : WordTrace (prefixWord ++ tailWord_4732409) baseStart_4732409 baseEnd_4732409 := by
    simpa [prefixWord, tailWord_4732409, baseEnd_4732409] using wordTrace_append hprefix tailTrace_4732409
  have hstable : (prefixWord ++ tailWord_4732409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732409).length < 2 ^ (prefixWord ++ tailWord_4732409).sum := by decide
  have hdescent : baseEnd_4732409 < baseStart_4732409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732426 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_4732426 : Nat := 118140960795 + 4732426 * 2 ^ 59
def prefixEnd_4732426 : Nat := 4983230072969 + 3 ^ 40 * 4732426 * 2
def baseEnd_4732426 : Nat := 810003066611468865070325

theorem tailTrace_4732426 : CollatzResearch.WordTrace tailWord_4732426 prefixEnd_4732426 810003066611468865070325 := by
  unfold tailWord_4732426
  simp only [CollatzResearch.WordTrace]
  refine ⟨43151439088309077714778283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115070504235490873906075421 43151439088309077714778283)
  ·
    refine ⟨64727158632463616572167425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43151439088309077714778283 64727158632463616572167425)
    ·
      refine ⟨48545368974347712429125569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64727158632463616572167425 48545368974347712429125569)
      ·
        refine ⟨36409026730760784321844177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48545368974347712429125569 36409026730760784321844177)
        ·
          refine ⟨27306770048070588241383133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36409026730760784321844177 27306770048070588241383133)
          ·
            refine ⟨10240038768026470590518675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27306770048070588241383133 10240038768026470590518675)
            ·
              refine ⟨15360058152039705885778013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10240038768026470590518675 15360058152039705885778013)
              ·
                refine ⟨5760021807014889707166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15360058152039705885778013 5760021807014889707166755)
                ·
                  refine ⟨8640032710522334560750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760021807014889707166755 8640032710522334560750133)
                  ·
                    refine ⟨810003066611468865070325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8640032710522334560750133 810003066611468865070325)
                    ·
                      rfl

theorem cell23_4732426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_4732426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732426 prefixEnd_4732426 := by exact prefixLift 4732426
  have htrace : WordTrace (prefixWord ++ tailWord_4732426) baseStart_4732426 baseEnd_4732426 := by
    simpa [prefixWord, tailWord_4732426, baseEnd_4732426] using wordTrace_append hprefix tailTrace_4732426
  have hstable : (prefixWord ++ tailWord_4732426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732426).length < 2 ^ (prefixWord ++ tailWord_4732426).sum := by decide
  have hdescent : baseEnd_4732426 < baseStart_4732426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732432 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_4732432 : Nat := 118140960795 + 4732432 * 2 ^ 59
def prefixEnd_4732432 : Nat := 4983230072969 + 3 ^ 40 * 4732432 * 2
def baseEnd_4732432 : Nat := 2430012280718333571735947

theorem tailTrace_4732432 : CollatzResearch.WordTrace tailWord_4732432 prefixEnd_4732432 2430012280718333571735947 := by
  unfold tailWord_4732432
  simp only [CollatzResearch.WordTrace]
  refine ⟨86302987595607286941915775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115070650127476382589221033 86302987595607286941915775)
  ·
    refine ⟨129454481393410930412873663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86302987595607286941915775 129454481393410930412873663)
    ·
      refine ⟨194181722090116395619310495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129454481393410930412873663 194181722090116395619310495)
      ·
        refine ⟨291272583135174593428965743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194181722090116395619310495 291272583135174593428965743)
        ·
          refine ⟨436908874702761890143448615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291272583135174593428965743 436908874702761890143448615)
          ·
            refine ⟨655363312054142835215172923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436908874702761890143448615 655363312054142835215172923)
            ·
              refine ⟨983044968081214252822759385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655363312054142835215172923 983044968081214252822759385)
              ·
                refine ⟨737283726060910689617069539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983044968081214252822759385 737283726060910689617069539)
                ·
                  refine ⟨1105925589091366034425604309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737283726060910689617069539 1105925589091366034425604309)
                  ·
                    refine ⟨25920130994328891431850101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1105925589091366034425604309 25920130994328891431850101)
                    ·
                      refine ⟨2430012280718333571735947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25920130994328891431850101 2430012280718333571735947)
                      ·
                        rfl

theorem cell23_4732432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_4732432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732432 prefixEnd_4732432 := by exact prefixLift 4732432
  have htrace : WordTrace (prefixWord ++ tailWord_4732432) baseStart_4732432 baseEnd_4732432 := by
    simpa [prefixWord, tailWord_4732432, baseEnd_4732432] using wordTrace_append hprefix tailTrace_4732432
  have hstable : (prefixWord ++ tailWord_4732432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732432).length < 2 ^ (prefixWord ++ tailWord_4732432).sum := by decide
  have hdescent : baseEnd_4732432 < baseStart_4732432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732449 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4732449 : Nat := 118140960795 + 4732449 * 2 ^ 59
def prefixEnd_4732449 : Nat := 4983230072969 + 3 ^ 40 * 4732449 * 2
def baseEnd_4732449 : Nat := 2430021009889460005223369

theorem tailTrace_4732449 : CollatzResearch.WordTrace tailWord_4732449 prefixEnd_4732449 2430021009889460005223369 := by
  unfold tailWord_4732449
  simp only [CollatzResearch.WordTrace]
  refine ⟨172606595232152985787200401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115071063488101990524800267 172606595232152985787200401)
  ·
    refine ⟨129454946424114739340400301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172606595232152985787200401 129454946424114739340400301)
    ·
      refine ⟨48545604909043027252650113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129454946424114739340400301 48545604909043027252650113)
      ·
        refine ⟨36409203681782270439487585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48545604909043027252650113 36409203681782270439487585)
        ·
          refine ⟨27306902761336702829615689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36409203681782270439487585 27306902761336702829615689)
          ·
            refine ⟨20480177071002527122211767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27306902761336702829615689 20480177071002527122211767)
            ·
              refine ⟨30720265606503790683317651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20480177071002527122211767 30720265606503790683317651)
              ·
                refine ⟨46080398409755686024976477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30720265606503790683317651 46080398409755686024976477)
                ·
                  refine ⟨17280149403658382259366179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46080398409755686024976477 17280149403658382259366179)
                  ·
                    refine ⟨25920224105487573389049269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17280149403658382259366179 25920224105487573389049269)
                    ·
                      refine ⟨2430021009889460005223369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25920224105487573389049269 2430021009889460005223369)
                      ·
                        rfl

theorem cell23_4732449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4732449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732449 prefixEnd_4732449 := by exact prefixLift 4732449
  have htrace : WordTrace (prefixWord ++ tailWord_4732449) baseStart_4732449 baseEnd_4732449 := by
    simpa [prefixWord, tailWord_4732449, baseEnd_4732449] using wordTrace_append hprefix tailTrace_4732449
  have hstable : (prefixWord ++ tailWord_4732449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732449).length < 2 ^ (prefixWord ++ tailWord_4732449).sum := by decide
  have hdescent : baseEnd_4732449 < baseStart_4732449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732469 : List Nat := [1, 3, 3, 1, 1, 4, 1, 9]
def baseStart_4732469 : Nat := 118140960795 + 4732469 * 2 ^ 59
def prefixEnd_4732469 : Nat := 4983230072969 + 3 ^ 40 * 4732469 * 2
def baseEnd_4732469 : Nat := 90001158500094441739751

theorem tailTrace_4732469 : CollatzResearch.WordTrace tailWord_4732469 prefixEnd_4732469 90001158500094441739751 := by
  unfold tailWord_4732469
  simp only [CollatzResearch.WordTrace]
  refine ⟨172607324692080529202928461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115071549794720352801952307 172607324692080529202928461)
  ·
    refine ⟨64727746759530198451098173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172607324692080529202928461 64727746759530198451098173)
    ·
      refine ⟨24272905034823824419161815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64727746759530198451098173 24272905034823824419161815)
      ·
        refine ⟨36409357552235736628742723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24272905034823824419161815 36409357552235736628742723)
        ·
          refine ⟨54614036328353604943114085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36409357552235736628742723 54614036328353604943114085)
          ·
            refine ⟨10240131811566300926833891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54614036328353604943114085 10240131811566300926833891)
            ·
              refine ⟨15360197717349451390250837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10240131811566300926833891 15360197717349451390250837)
              ·
                refine ⟨90001158500094441739751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15360197717349451390250837 90001158500094441739751)
                ·
                  rfl

theorem cell23_4732469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 9].length) (baseStart_4732469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732469 prefixEnd_4732469 := by exact prefixLift 4732469
  have htrace : WordTrace (prefixWord ++ tailWord_4732469) baseStart_4732469 baseEnd_4732469 := by
    simpa [prefixWord, tailWord_4732469, baseEnd_4732469] using wordTrace_append hprefix tailTrace_4732469
  have hstable : (prefixWord ++ tailWord_4732469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732469).length < 2 ^ (prefixWord ++ tailWord_4732469).sum := by decide
  have hdescent : baseEnd_4732469 < baseStart_4732469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732496 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_4732496 : Nat := 118140960795 + 4732496 * 2 ^ 59
def prefixEnd_4732496 : Nat := 4983230072969 + 3 ^ 40 * 4732496 * 2
def baseEnd_4732496 : Nat := 2430045143480221321335653

theorem tailTrace_4732496 : CollatzResearch.WordTrace tailWord_4732496 prefixEnd_4732496 2430045143480221321335653 := by
  unfold tailWord_4732496
  simp only [CollatzResearch.WordTrace]
  refine ⟨86304154731491356407080671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115072206308655141876107561 86304154731491356407080671)
  ·
    refine ⟨129456232097237034610621007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86304154731491356407080671 129456232097237034610621007)
    ·
      refine ⟨194184348145855551915931511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129456232097237034610621007 194184348145855551915931511)
      ·
        refine ⟨291276522218783327873897267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194184348145855551915931511 291276522218783327873897267)
        ·
          refine ⟨436914783328174991810845901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291276522218783327873897267 436914783328174991810845901)
          ·
            refine ⟨163843043748065621929067213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436914783328174991810845901 163843043748065621929067213)
            ·
              refine ⟨61441141405524608223400205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163843043748065621929067213 61441141405524608223400205)
              ·
                refine ⟨23040428027071728083775077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61441141405524608223400205 23040428027071728083775077)
                ·
                  refine ⟨4320080255075949015707827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23040428027071728083775077 4320080255075949015707827)
                  ·
                    refine ⟨6480120382613923523561741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320080255075949015707827 6480120382613923523561741)
                    ·
                      refine ⟨2430045143480221321335653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6480120382613923523561741 2430045143480221321335653)
                      ·
                        rfl

theorem cell23_4732496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_4732496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732496 prefixEnd_4732496 := by exact prefixLift 4732496
  have htrace : WordTrace (prefixWord ++ tailWord_4732496) baseStart_4732496 baseEnd_4732496 := by
    simpa [prefixWord, tailWord_4732496, baseEnd_4732496] using wordTrace_append hprefix tailTrace_4732496
  have hstable : (prefixWord ++ tailWord_4732496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732496).length < 2 ^ (prefixWord ++ tailWord_4732496).sum := by decide
  have hdescent : baseEnd_4732496 < baseStart_4732496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732497 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_4732497 : Nat := 118140960795 + 4732497 * 2 ^ 59
def prefixEnd_4732497 : Nat := 4983230072969 + 3 ^ 40 * 4732497 * 2
def baseEnd_4732497 : Nat := 2430045656960875817423149

theorem tailTrace_4732497 : CollatzResearch.WordTrace tailWord_4732497 prefixEnd_4732497 2430045656960875817423149 := by
  unfold tailWord_4732497
  simp only [CollatzResearch.WordTrace]
  refine ⟨172608345935979089984947745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115072230623986059989965163 172608345935979089984947745)
  ·
    refine ⟨129456259451984317488710809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172608345935979089984947745 129456259451984317488710809)
    ·
      refine ⟨97092194588988238116533107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129456259451984317488710809 97092194588988238116533107)
      ·
        refine ⟨145638291883482357174799661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97092194588988238116533107 145638291883482357174799661)
        ·
          refine ⟨54614359456305883940549873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145638291883482357174799661 54614359456305883940549873)
          ·
            refine ⟨40960769592229412955412405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54614359456305883940549873 40960769592229412955412405)
            ·
              refine ⟨3840072149271507464569913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40960769592229412955412405 3840072149271507464569913)
              ·
                refine ⟨2880054111953630598427435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3840072149271507464569913 2880054111953630598427435)
                ·
                  refine ⟨4320081167930445897641153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880054111953630598427435 4320081167930445897641153)
                  ·
                    refine ⟨3240060875947834423230865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320081167930445897641153 3240060875947834423230865)
                    ·
                      refine ⟨2430045656960875817423149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240060875947834423230865 2430045656960875817423149)
                      ·
                        rfl

theorem cell23_4732497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_4732497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732497 prefixEnd_4732497 := by exact prefixLift 4732497
  have htrace : WordTrace (prefixWord ++ tailWord_4732497) baseStart_4732497 baseEnd_4732497 := by
    simpa [prefixWord, tailWord_4732497, baseEnd_4732497] using wordTrace_append hprefix tailTrace_4732497
  have hstable : (prefixWord ++ tailWord_4732497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732497).length < 2 ^ (prefixWord ++ tailWord_4732497).sum := by decide
  have hdescent : baseEnd_4732497 < baseStart_4732497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732513 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_4732513 : Nat := 118140960795 + 4732513 * 2 ^ 59
def prefixEnd_4732513 : Nat := 4983230072969 + 3 ^ 40 * 4732513 * 2
def baseEnd_4732513 : Nat := 2430053872651347754823075

theorem tailTrace_4732513 : CollatzResearch.WordTrace tailWord_4732513 prefixEnd_4732513 2430053872651347754823075 := by
  unfold tailWord_4732513
  simp only [CollatzResearch.WordTrace]
  refine ⟨172608929503921124717530193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115072619669280749811686795 172608929503921124717530193)
  ·
    refine ⟨129456697127940843538147645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172608929503921124717530193 129456697127940843538147645)
    ·
      refine ⟨48546261422977816326805367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129456697127940843538147645 48546261422977816326805367)
      ·
        refine ⟨72819392134466724490208051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48546261422977816326805367 72819392134466724490208051)
        ·
          refine ⟨109229088201700086735312077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72819392134466724490208051 109229088201700086735312077)
          ·
            refine ⟨40960908075637532525742029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109229088201700086735312077 40960908075637532525742029)
            ·
              refine ⟨15360340528364074697153261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40960908075637532525742029 15360340528364074697153261)
              ·
                refine ⟨5760127698136528011432473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15360340528364074697153261 5760127698136528011432473)
                ·
                  refine ⟨4320095773602396008574355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760127698136528011432473 4320095773602396008574355)
                  ·
                    refine ⟨6480143660403594012861533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320095773602396008574355 6480143660403594012861533)
                    ·
                      refine ⟨2430053872651347754823075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6480143660403594012861533 2430053872651347754823075)
                      ·
                        rfl

theorem cell23_4732513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_4732513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732513 prefixEnd_4732513 := by exact prefixLift 4732513
  have htrace : WordTrace (prefixWord ++ tailWord_4732513) baseStart_4732513 baseEnd_4732513 := by
    simpa [prefixWord, tailWord_4732513, baseEnd_4732513] using wordTrace_append hprefix tailTrace_4732513
  have hstable : (prefixWord ++ tailWord_4732513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732513).length < 2 ^ (prefixWord ++ tailWord_4732513).sum := by decide
  have hdescent : baseEnd_4732513 < baseStart_4732513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732539 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_4732539 : Nat := 118140960795 + 4732539 * 2 ^ 59
def prefixEnd_4732539 : Nat := 4983230072969 + 3 ^ 40 * 4732539 * 2
def baseEnd_4732539 : Nat := 2430067223148364653097955

theorem tailTrace_4732539 : CollatzResearch.WordTrace tailWord_4732539 prefixEnd_4732539 2430067223148364653097955 := by
  unfold tailWord_4732539
  simp only [CollatzResearch.WordTrace]
  refine ⟨172609877801826931157976671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115073251867884620771984447 172609877801826931157976671)
  ·
    refine ⟨258914816702740396736965007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172609877801826931157976671 258914816702740396736965007)
    ·
      refine ⟨388372225054110595105447511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258914816702740396736965007 388372225054110595105447511)
      ·
        refine ⟨582558337581165892658171267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388372225054110595105447511 582558337581165892658171267)
        ·
          refine ⟨873837506371748838987256901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582558337581165892658171267 873837506371748838987256901)
          ·
            refine ⟨163844532444702907310110669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 873837506371748838987256901 163844532444702907310110669)
            ·
              refine ⟨61441699666763590241291501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163844532444702907310110669 61441699666763590241291501)
              ·
                refine ⟨23040637375036346340484313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61441699666763590241291501 23040637375036346340484313)
                ·
                  refine ⟨17280478031277259755363235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23040637375036346340484313 17280478031277259755363235)
                  ·
                    refine ⟨25920717046915889633044853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17280478031277259755363235 25920717046915889633044853)
                    ·
                      refine ⟨2430067223148364653097955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25920717046915889633044853 2430067223148364653097955)
                      ·
                        rfl

theorem cell23_4732539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_4732539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732539 prefixEnd_4732539 := by exact prefixLift 4732539
  have htrace : WordTrace (prefixWord ++ tailWord_4732539) baseStart_4732539 baseEnd_4732539 := by
    simpa [prefixWord, tailWord_4732539, baseEnd_4732539] using wordTrace_append hprefix tailTrace_4732539
  have hstable : (prefixWord ++ tailWord_4732539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732539).length < 2 ^ (prefixWord ++ tailWord_4732539).sum := by decide
  have hdescent : baseEnd_4732539 < baseStart_4732539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732553 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 4, 2, 2]
def baseStart_4732553 : Nat := 118140960795 + 4732553 * 2 ^ 59
def prefixEnd_4732553 : Nat := 4983230072969 + 3 ^ 40 * 4732553 * 2
def baseEnd_4732553 : Nat := 2430074411877527598322891

theorem tailTrace_4732553 : CollatzResearch.WordTrace tailWord_4732553 prefixEnd_4732553 2430074411877527598322891 := by
  unfold tailWord_4732553
  simp only [CollatzResearch.WordTrace]
  refine ⟨172610388423776211548986313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115073592282517474365990875 172610388423776211548986313)
  ·
    refine ⟨129457791317832158661739735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172610388423776211548986313 129457791317832158661739735)
    ·
      refine ⟨194186686976748237992609603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129457791317832158661739735 194186686976748237992609603)
      ·
        refine ⟨291280030465122356988914405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194186686976748237992609603 291280030465122356988914405)
        ·
          refine ⟨54615005712210441935421451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291280030465122356988914405 54615005712210441935421451)
          ·
            refine ⟨81922508568315662903132177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54615005712210441935421451 81922508568315662903132177)
            ·
              refine ⟨61441881426236747177349133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81922508568315662903132177 61441881426236747177349133)
              ·
                refine ⟨23040705534838780191505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61441881426236747177349133 23040705534838780191505925)
                ·
                  refine ⟨4320132287782271285907361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23040705534838780191505925 4320132287782271285907361)
                  ·
                    refine ⟨3240099215836703464430521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320132287782271285907361 3240099215836703464430521)
                    ·
                      refine ⟨2430074411877527598322891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240099215836703464430521 2430074411877527598322891)
                      ·
                        rfl

theorem cell23_4732553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2, 2].length) (baseStart_4732553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732553 prefixEnd_4732553 := by exact prefixLift 4732553
  have htrace : WordTrace (prefixWord ++ tailWord_4732553) baseStart_4732553 baseEnd_4732553 := by
    simpa [prefixWord, tailWord_4732553, baseEnd_4732553] using wordTrace_append hprefix tailTrace_4732553
  have hstable : (prefixWord ++ tailWord_4732553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732553).length < 2 ^ (prefixWord ++ tailWord_4732553).sum := by decide
  have hdescent : baseEnd_4732553 < baseStart_4732553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732576 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 7]
def baseStart_4732576 : Nat := 118140960795 + 4732576 * 2 ^ 59
def prefixEnd_4732576 : Nat := 4983230072969 + 3 ^ 40 * 4732576 * 2
def baseEnd_4732576 : Nat := 270009580214731223148365

theorem tailTrace_4732576 : CollatzResearch.WordTrace tailWord_4732576 prefixEnd_4732576 270009580214731223148365 := by
  unfold tailWord_4732576
  simp only [CollatzResearch.WordTrace]
  refine ⟨86305613651346443238536791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115074151535128590984715721 86305613651346443238536791)
  ·
    refine ⟨129458420477019664857805187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86305613651346443238536791 129458420477019664857805187)
    ·
      refine ⟨194187630715529497286707781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129458420477019664857805187 194187630715529497286707781)
      ·
        refine ⟨36410180759161780741257709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194187630715529497286707781 36410180759161780741257709)
        ·
          refine ⟨13653817784685667777971641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36410180759161780741257709 13653817784685667777971641)
          ·
            refine ⟨10240363338514250833478731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13653817784685667777971641 10240363338514250833478731)
            ·
              refine ⟨15360545007771376250218097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10240363338514250833478731 15360545007771376250218097)
              ·
                refine ⟨11520408755828532187663573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15360545007771376250218097 11520408755828532187663573)
                ·
                  refine ⟨270009580214731223148365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11520408755828532187663573 270009580214731223148365)
                  ·
                    rfl

theorem cell23_4732576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_4732576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732576 prefixEnd_4732576 := by exact prefixLift 4732576
  have htrace : WordTrace (prefixWord ++ tailWord_4732576) baseStart_4732576 baseEnd_4732576 := by
    simpa [prefixWord, tailWord_4732576, baseEnd_4732576] using wordTrace_append hprefix tailTrace_4732576
  have hstable : (prefixWord ++ tailWord_4732576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732576).length < 2 ^ (prefixWord ++ tailWord_4732576).sum := by decide
  have hdescent : baseEnd_4732576 < baseStart_4732576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732621 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4732621 : Nat := 118140960795 + 4732621 * 2 ^ 59
def prefixEnd_4732621 : Nat := 4983230072969 + 3 ^ 40 * 4732621 * 2
def baseEnd_4732621 : Nat := 2430109328562033332272579

theorem tailTrace_4732621 : CollatzResearch.WordTrace tailWord_4732621 prefixEnd_4732621 2430109328562033332272579 := by
  unfold tailWord_4732621
  simp only [CollatzResearch.WordTrace]
  refine ⟨172612868587529859162461717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115075245725019906108307811 172612868587529859162461717)
  ·
    refine ⟨8091228215040462148240393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172612868587529859162461717 8091228215040462148240393)
    ·
      refine ⟨6068421161280346611180295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8091228215040462148240393 6068421161280346611180295)
      ·
        refine ⟨9102631741920519916770443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068421161280346611180295 9102631741920519916770443)
        ·
          refine ⟨13653947612880779875155665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102631741920519916770443 13653947612880779875155665)
          ·
            refine ⟨10240460709660584906366749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13653947612880779875155665 10240460709660584906366749)
            ·
              refine ⟨3840172766122719339887531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10240460709660584906366749 3840172766122719339887531)
              ·
                refine ⟨5760259149184079009831297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840172766122719339887531 5760259149184079009831297)
                ·
                  refine ⟨4320194361888059257373473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760259149184079009831297 4320194361888059257373473)
                  ·
                    refine ⟨3240145771416044443030105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320194361888059257373473 3240145771416044443030105)
                    ·
                      refine ⟨2430109328562033332272579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240145771416044443030105 2430109328562033332272579)
                      ·
                        rfl

theorem cell23_4732621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4732621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732621 prefixEnd_4732621 := by exact prefixLift 4732621
  have htrace : WordTrace (prefixWord ++ tailWord_4732621) baseStart_4732621 baseEnd_4732621 := by
    simpa [prefixWord, tailWord_4732621, baseEnd_4732621] using wordTrace_append hprefix tailTrace_4732621
  have hstable : (prefixWord ++ tailWord_4732621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732621).length < 2 ^ (prefixWord ++ tailWord_4732621).sum := by decide
  have hdescent : baseEnd_4732621 < baseStart_4732621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732666 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_4732666 : Nat := 118140960795 + 4732666 * 2 ^ 59
def prefixEnd_4732666 : Nat := 4983230072969 + 3 ^ 40 * 4732666 * 2
def baseEnd_4732666 : Nat := 270014715021276184023319

theorem tailTrace_4732666 : CollatzResearch.WordTrace tailWord_4732666 prefixEnd_4732666 270014715021276184023319 := by
  unfold tailWord_4732666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43153627468091707961962463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115076339914911221231899901 43153627468091707961962463)
  ·
    refine ⟨64730441202137561942943695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43153627468091707961962463 64730441202137561942943695)
    ·
      refine ⟨97095661803206342914415543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64730441202137561942943695 97095661803206342914415543)
      ·
        refine ⟨145643492704809514371623315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97095661803206342914415543 145643492704809514371623315)
        ·
          refine ⟨218465239057214271557434973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145643492704809514371623315 218465239057214271557434973)
          ·
            refine ⟨81924464646455351834038115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218465239057214271557434973 81924464646455351834038115)
            ·
              refine ⟨122886696969683027751057173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81924464646455351834038115 122886696969683027751057173)
              ·
                refine ⟨5760313920453891925830805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122886696969683027751057173 5760313920453891925830805)
                ·
                  refine ⟨270014715021276184023319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5760313920453891925830805 270014715021276184023319)
                  ·
                    rfl

theorem cell23_4732666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_4732666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732666 prefixEnd_4732666 := by exact prefixLift 4732666
  have htrace : WordTrace (prefixWord ++ tailWord_4732666) baseStart_4732666 baseEnd_4732666 := by
    simpa [prefixWord, tailWord_4732666, baseEnd_4732666] using wordTrace_append hprefix tailTrace_4732666
  have hstable : (prefixWord ++ tailWord_4732666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732666).length < 2 ^ (prefixWord ++ tailWord_4732666).sum := by decide
  have hdescent : baseEnd_4732666 < baseStart_4732666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732683 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 6]
def baseStart_4732683 : Nat := 118140960795 + 4732683 * 2 ^ 59
def prefixEnd_4732683 : Nat := 4983230072969 + 3 ^ 40 * 4732683 * 2
def baseEnd_4732683 : Nat := 270015684929179121077477

theorem tailTrace_4732683 : CollatzResearch.WordTrace tailWord_4732683 prefixEnd_4732683 270015684929179121077477 := by
  unfold tailWord_4732683
  simp only [CollatzResearch.WordTrace]
  refine ⟨172615129913305243751218703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115076753275536829167479135 172615129913305243751218703)
  ·
    refine ⟨258922694869957865626828055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172615129913305243751218703 258922694869957865626828055)
    ·
      refine ⟨388384042304936798440242083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258922694869957865626828055 388384042304936798440242083)
      ·
        refine ⟨582576063457405197660363125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388384042304936798440242083 582576063457405197660363125)
        ·
          refine ⟨54616505949131737280659043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 582576063457405197660363125 54616505949131737280659043)
          ·
            refine ⟨81924758923697605920988565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54616505949131737280659043 81924758923697605920988565)
            ·
              refine ⟨3840223074548325277546339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81924758923697605920988565 3840223074548325277546339)
              ·
                refine ⟨5760334611822487916319509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840223074548325277546339 5760334611822487916319509)
                ·
                  refine ⟨270015684929179121077477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5760334611822487916319509 270015684929179121077477)
                  ·
                    rfl

theorem cell23_4732683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 6].length) (baseStart_4732683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732683 prefixEnd_4732683 := by exact prefixLift 4732683
  have htrace : WordTrace (prefixWord ++ tailWord_4732683) baseStart_4732683 baseEnd_4732683 := by
    simpa [prefixWord, tailWord_4732683, baseEnd_4732683] using wordTrace_append hprefix tailTrace_4732683
  have hstable : (prefixWord ++ tailWord_4732683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732683).length < 2 ^ (prefixWord ++ tailWord_4732683).sum := by decide
  have hdescent : baseEnd_4732683 < baseStart_4732683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732686 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4732686 : Nat := 118140960795 + 4732686 * 2 ^ 59
def prefixEnd_4732686 : Nat := 4983230072969 + 3 ^ 40 * 4732686 * 2
def baseEnd_4732686 : Nat := 2430142704804575577959779

theorem tailTrace_4732686 : CollatzResearch.WordTrace tailWord_4732686 prefixEnd_4732686 2430142704804575577959779 := by
  unfold tailWord_4732686
  simp only [CollatzResearch.WordTrace]
  refine ⟨21576904916536796907947239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115076826221529583509051941 21576904916536796907947239)
  ·
    refine ⟨32365357374805195361920859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21576904916536796907947239 32365357374805195361920859)
    ·
      refine ⟨48548036062207793042881289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32365357374805195361920859 48548036062207793042881289)
      ·
        refine ⟨36411027046655844782160967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48548036062207793042881289 36411027046655844782160967)
        ·
          refine ⟨54616540569983767173241451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36411027046655844782160967 54616540569983767173241451)
          ·
            refine ⟨81924810854975650759862177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54616540569983767173241451 81924810854975650759862177)
            ·
              refine ⟨61443608141231738069896633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81924810854975650759862177 61443608141231738069896633)
              ·
                refine ⟨46082706105923803552422475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61443608141231738069896633 46082706105923803552422475)
                ·
                  refine ⟨69124059158885705328633713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46082706105923803552422475 69124059158885705328633713)
                  ·
                    refine ⟨51843044369164278996475285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69124059158885705328633713 51843044369164278996475285)
                    ·
                      refine ⟨2430142704804575577959779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51843044369164278996475285 2430142704804575577959779)
                      ·
                        rfl

theorem cell23_4732686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4732686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732686 prefixEnd_4732686 := by exact prefixLift 4732686
  have htrace : WordTrace (prefixWord ++ tailWord_4732686) baseStart_4732686 baseEnd_4732686 := by
    simpa [prefixWord, tailWord_4732686, baseEnd_4732686] using wordTrace_append hprefix tailTrace_4732686
  have hstable : (prefixWord ++ tailWord_4732686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732686).length < 2 ^ (prefixWord ++ tailWord_4732686).sum := by decide
  have hdescent : baseEnd_4732686 < baseStart_4732686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732764 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4732764 : Nat := 118140960795 + 4732764 * 2 ^ 59
def prefixEnd_4732764 : Nat := 4983230072969 + 3 ^ 40 * 4732764 * 2
def baseEnd_4732764 : Nat := 810060918765208757594807

theorem tailTrace_4732764 : CollatzResearch.WordTrace tailWord_4732764 prefixEnd_4732764 810060918765208757594807 := by
  unfold tailWord_4732764
  simp only [CollatzResearch.WordTrace]
  refine ⟨86309042113005897292458673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115078722817341196389944897 86309042113005897292458673)
  ·
    refine ⟨64731781584754422969344005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86309042113005897292458673 64731781584754422969344005)
    ·
      refine ⟨12137209047141454306752001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64731781584754422969344005 12137209047141454306752001)
      ·
        refine ⟨9102906785356090730064001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12137209047141454306752001 9102906785356090730064001)
        ·
          refine ⟨6827180089017068047548001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9102906785356090730064001 6827180089017068047548001)
          ·
            refine ⟨5120385066762801035661001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827180089017068047548001 5120385066762801035661001)
            ·
              refine ⟨3840288800072100776745751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120385066762801035661001 3840288800072100776745751)
              ·
                refine ⟨5760433200108151165118627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840288800072100776745751 5760433200108151165118627)
                ·
                  refine ⟨8640649800162226747677941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760433200108151165118627 8640649800162226747677941)
                  ·
                    refine ⟨810060918765208757594807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8640649800162226747677941 810060918765208757594807)
                    ·
                      rfl

theorem cell23_4732764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4732764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732764 prefixEnd_4732764 := by exact prefixLift 4732764
  have htrace : WordTrace (prefixWord ++ tailWord_4732764) baseStart_4732764 baseEnd_4732764 := by
    simpa [prefixWord, tailWord_4732764, baseEnd_4732764] using wordTrace_append hprefix tailTrace_4732764
  have hstable : (prefixWord ++ tailWord_4732764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732764).length < 2 ^ (prefixWord ++ tailWord_4732764).sum := by decide
  have hdescent : baseEnd_4732764 < baseStart_4732764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732767 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 1, 1, 4]
def baseStart_4732767 : Nat := 118140960795 + 4732767 * 2 ^ 59
def prefixEnd_4732767 : Nat := 4983230072969 + 3 ^ 40 * 4732767 * 2
def baseEnd_4732767 : Nat := 2430184296737589761046907

theorem tailTrace_4732767 : CollatzResearch.WordTrace tailWord_4732767 prefixEnd_4732767 2430184296737589761046907 := by
  unfold tailWord_4732767
  simp only [CollatzResearch.WordTrace]
  refine ⟨172618193645000926097276555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115078795763333950731517703 172618193645000926097276555)
  ·
    refine ⟨258927290467501389145914833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172618193645000926097276555 258927290467501389145914833)
    ·
      refine ⟨194195467850626041859436125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258927290467501389145914833 194195467850626041859436125)
      ·
        refine ⟨72823300443984765697288547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194195467850626041859436125 72823300443984765697288547)
        ·
          refine ⟨109234950665977148545932821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72823300443984765697288547 109234950665977148545932821)
          ·
            refine ⟨5120388312467678838090601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109234950665977148545932821 5120388312467678838090601)
            ·
              refine ⟨3840291234350759128567951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120388312467678838090601 3840291234350759128567951)
              ·
                refine ⟨5760436851526138692851927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840291234350759128567951 5760436851526138692851927)
                ·
                  refine ⟨8640655277289208039277891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760436851526138692851927 8640655277289208039277891)
                  ·
                    refine ⟨12960982915933812058916837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8640655277289208039277891 12960982915933812058916837)
                    ·
                      refine ⟨2430184296737589761046907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12960982915933812058916837 2430184296737589761046907)
                      ·
                        rfl

theorem cell23_4732767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_4732767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732767 prefixEnd_4732767 := by exact prefixLift 4732767
  have htrace : WordTrace (prefixWord ++ tailWord_4732767) baseStart_4732767 baseEnd_4732767 := by
    simpa [prefixWord, tailWord_4732767, baseEnd_4732767] using wordTrace_append hprefix tailTrace_4732767
  have hstable : (prefixWord ++ tailWord_4732767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732767).length < 2 ^ (prefixWord ++ tailWord_4732767).sum := by decide
  have hdescent : baseEnd_4732767 < baseStart_4732767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732807 : List Nat := [1, 1, 4, 2, 5, 1, 2, 7]
def baseStart_4732807 : Nat := 118140960795 + 4732807 * 2 ^ 59
def prefixEnd_4732807 : Nat := 4983230072969 + 3 ^ 40 * 4732807 * 2
def baseEnd_4732807 : Nat := 90007586517176652020249

theorem tailTrace_4732807 : CollatzResearch.WordTrace tailWord_4732807 prefixEnd_4732807 90007586517176652020249 := by
  unfold tailWord_4732807
  simp only [CollatzResearch.WordTrace]
  refine ⟨172619652564856012928732675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115079768376570675285821783 172619652564856012928732675)
  ·
    refine ⟨258929478847284019393099013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172619652564856012928732675 258929478847284019393099013)
    ·
      refine ⟨48549277283865753636206065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258929478847284019393099013 48549277283865753636206065)
      ·
        refine ⟨36411957962899315227154549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48549277283865753636206065 36411957962899315227154549)
        ·
          refine ⟨3413621059021810802545739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36411957962899315227154549 3413621059021810802545739)
          ·
            refine ⟨5120431588532716203818609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413621059021810802545739 5120431588532716203818609)
            ·
              refine ⟨3840323691399537152863957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120431588532716203818609 3840323691399537152863957)
              ·
                refine ⟨90007586517176652020249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3840323691399537152863957 90007586517176652020249)
                ·
                  rfl

theorem cell23_4732807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 7].length) (baseStart_4732807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732807 prefixEnd_4732807 := by exact prefixLift 4732807
  have htrace : WordTrace (prefixWord ++ tailWord_4732807) baseStart_4732807 baseEnd_4732807 := by
    simpa [prefixWord, tailWord_4732807, baseEnd_4732807] using wordTrace_append hprefix tailTrace_4732807
  have hstable : (prefixWord ++ tailWord_4732807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732807).length < 2 ^ (prefixWord ++ tailWord_4732807).sum := by decide
  have hdescent : baseEnd_4732807 < baseStart_4732807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732816 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_4732816 : Nat := 118140960795 + 4732816 * 2 ^ 59
def prefixEnd_4732816 : Nat := 4983230072969 + 3 ^ 40 * 4732816 * 2
def baseEnd_4732816 : Nat := 810069819096553356444727

theorem tailTrace_4732816 : CollatzResearch.WordTrace tailWord_4732816 prefixEnd_4732816 810069819096553356444727 := by
  unfold tailWord_4732816
  simp only [CollatzResearch.WordTrace]
  refine ⟨86309990410911703732905151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115079987214548938310540201 86309990410911703732905151)
  ·
    refine ⟨129464985616367555599357727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86309990410911703732905151 129464985616367555599357727)
    ·
      refine ⟨194197478424551333399036591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129464985616367555599357727 194197478424551333399036591)
      ·
        refine ⟨291296217636827000098554887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194197478424551333399036591 291296217636827000098554887)
        ·
          refine ⟨436944326455240500147832331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291296217636827000098554887 436944326455240500147832331)
          ·
            refine ⟨655416489682860750221748497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436944326455240500147832331 655416489682860750221748497)
            ·
              refine ⟨491562367262145562666311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655416489682860750221748497 491562367262145562666311373)
              ·
                refine ⟨184335887723304585999866765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491562367262145562666311373 184335887723304585999866765)
                ·
                  refine ⟨69125957896239219749950037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184335887723304585999866765 69125957896239219749950037)
                  ·
                    refine ⟨810069819096553356444727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69125957896239219749950037 810069819096553356444727)
                    ·
                      rfl

theorem cell23_4732816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_4732816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732816 prefixEnd_4732816 := by exact prefixLift 4732816
  have htrace : WordTrace (prefixWord ++ tailWord_4732816) baseStart_4732816 baseEnd_4732816 := by
    simpa [prefixWord, tailWord_4732816, baseEnd_4732816] using wordTrace_append hprefix tailTrace_4732816
  have hstable : (prefixWord ++ tailWord_4732816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732816).length < 2 ^ (prefixWord ++ tailWord_4732816).sum := by decide
  have hdescent : baseEnd_4732816 < baseStart_4732816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732818 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4732818 : Nat := 118140960795 + 4732818 * 2 ^ 59
def prefixEnd_4732818 : Nat := 4983230072969 + 3 ^ 40 * 4732818 * 2
def baseEnd_4732818 : Nat := 2430210484250969061509173

theorem tailTrace_4732818 : CollatzResearch.WordTrace tailWord_4732818 prefixEnd_4732818 2430210484250969061509173 := by
  unfold tailWord_4732818
  simp only [CollatzResearch.WordTrace]
  refine ⟨43155013441954040451845777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115080035845210774538255405 43155013441954040451845777)
  ·
    refine ⟨32366260081465530338884333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43155013441954040451845777 32366260081465530338884333)
    ·
      refine ⟨12137347530549573877081625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32366260081465530338884333 12137347530549573877081625)
      ·
        refine ⟨9103010647912180407811219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12137347530549573877081625 9103010647912180407811219)
        ·
          refine ⟨13654515971868270611716829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103010647912180407811219 13654515971868270611716829)
          ·
            refine ⟨5120443489450601479393811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13654515971868270611716829 5120443489450601479393811)
            ·
              refine ⟨7680665234175902219090717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120443489450601479393811 7680665234175902219090717)
              ·
                refine ⟨2880249462815963332159019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7680665234175902219090717 2880249462815963332159019)
                ·
                  refine ⟨4320374194223944998238529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880249462815963332159019 4320374194223944998238529)
                  ·
                    refine ⟨3240280645667958748678897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320374194223944998238529 3240280645667958748678897)
                    ·
                      refine ⟨2430210484250969061509173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240280645667958748678897 2430210484250969061509173)
                      ·
                        rfl

theorem cell23_4732818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4732818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732818 prefixEnd_4732818 := by exact prefixLift 4732818
  have htrace : WordTrace (prefixWord ++ tailWord_4732818) baseStart_4732818 baseEnd_4732818 := by
    simpa [prefixWord, tailWord_4732818, baseEnd_4732818] using wordTrace_append hprefix tailTrace_4732818
  have hstable : (prefixWord ++ tailWord_4732818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732818).length < 2 ^ (prefixWord ++ tailWord_4732818).sum := by decide
  have hdescent : baseEnd_4732818 < baseStart_4732818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732873 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_4732873 : Nat := 118140960795 + 4732873 * 2 ^ 59
def prefixEnd_4732873 : Nat := 4983230072969 + 3 ^ 40 * 4732873 * 2
def baseEnd_4732873 : Nat := 2430238725686966346321419

theorem tailTrace_4732873 : CollatzResearch.WordTrace tailWord_4732873 prefixEnd_4732873 2430238725686966346321419 := by
  unfold tailWord_4732873
  simp only [CollatzResearch.WordTrace]
  refine ⟨172622059782616906200635273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115081373188411270800423515 172622059782616906200635273)
  ·
    refine ⟨129466544836962679650476455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172622059782616906200635273 129466544836962679650476455)
    ·
      refine ⟨194199817255444019475714683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129466544836962679650476455 194199817255444019475714683)
      ·
        refine ⟨291299725883166029213572025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194199817255444019475714683 291299725883166029213572025)
        ·
          refine ⟨218474794412374521910179019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291299725883166029213572025 218474794412374521910179019)
          ·
            refine ⟨327712191618561782865268529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218474794412374521910179019 327712191618561782865268529)
            ·
              refine ⟨245784143713921337148951397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327712191618561782865268529 245784143713921337148951397)
              ·
                refine ⟨46084526946360250715428387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245784143713921337148951397 46084526946360250715428387)
                ·
                  refine ⟨69126790419540376073142581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46084526946360250715428387 69126790419540376073142581)
                  ·
                    refine ⟨6480636601831910256857117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69126790419540376073142581 6480636601831910256857117)
                    ·
                      refine ⟨2430238725686966346321419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6480636601831910256857117 2430238725686966346321419)
                      ·
                        rfl

theorem cell23_4732873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_4732873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732873 prefixEnd_4732873 := by exact prefixLift 4732873
  have htrace : WordTrace (prefixWord ++ tailWord_4732873) baseStart_4732873 baseEnd_4732873 := by
    simpa [prefixWord, tailWord_4732873, baseEnd_4732873] using wordTrace_append hprefix tailTrace_4732873
  have hstable : (prefixWord ++ tailWord_4732873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732873).length < 2 ^ (prefixWord ++ tailWord_4732873).sum := by decide
  have hdescent : baseEnd_4732873 < baseStart_4732873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732897 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 5]
def baseStart_4732897 : Nat := 118140960795 + 4732897 * 2 ^ 59
def prefixEnd_4732897 : Nat := 4983230072969 + 3 ^ 40 * 4732897 * 2
def baseEnd_4732897 : Nat := 270027894358074916935701

theorem tailTrace_4732897 : CollatzResearch.WordTrace tailWord_4732897 prefixEnd_4732897 270027894358074916935701 := by
  unfold tailWord_4732897
  simp only [CollatzResearch.WordTrace]
  refine ⟨172622935134529958299508945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115081956756353305533005963 172622935134529958299508945)
  ·
    refine ⟨129467201350897468724631709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172622935134529958299508945 129467201350897468724631709)
    ·
      refine ⟨48550200506586550771736891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129467201350897468724631709 48550200506586550771736891)
      ·
        refine ⟨72825300759879826157605337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48550200506586550771736891 72825300759879826157605337)
        ·
          refine ⟨54618975569909869618204003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72825300759879826157605337 54618975569909869618204003)
          ·
            refine ⟨81928463354864804427306005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54618975569909869618204003 81928463354864804427306005)
            ·
              refine ⟨3840396719759287707529969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81928463354864804427306005 3840396719759287707529969)
              ·
                refine ⟨2880297539819465780647477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3840396719759287707529969 2880297539819465780647477)
                ·
                  refine ⟨270027894358074916935701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880297539819465780647477 270027894358074916935701)
                  ·
                    rfl

theorem cell23_4732897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 5].length) (baseStart_4732897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732897 prefixEnd_4732897 := by exact prefixLift 4732897
  have htrace : WordTrace (prefixWord ++ tailWord_4732897) baseStart_4732897 baseEnd_4732897 := by
    simpa [prefixWord, tailWord_4732897, baseEnd_4732897] using wordTrace_append hprefix tailTrace_4732897
  have hstable : (prefixWord ++ tailWord_4732897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732897).length < 2 ^ (prefixWord ++ tailWord_4732897).sum := by decide
  have hdescent : baseEnd_4732897 < baseStart_4732897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732900 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_4732900 : Nat := 118140960795 + 4732900 * 2 ^ 59
def prefixEnd_4732900 : Nat := 4983230072969 + 3 ^ 40 * 4732900 * 2
def baseEnd_4732900 : Nat := 2430252589664637740683795

theorem tailTrace_4732900 : CollatzResearch.WordTrace tailWord_4732900 prefixEnd_4732900 2430252589664637740683795 := by
  unfold tailWord_4732900
  simp only [CollatzResearch.WordTrace]
  refine ⟨86311522276759544905934077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115082029702346059874578769 86311522276759544905934077)
  ·
    refine ⟨32366820853784829339725279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86311522276759544905934077 32366820853784829339725279)
    ·
      refine ⟨48550231280677244009587919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32366820853784829339725279 48550231280677244009587919)
      ·
        refine ⟨72825346921015866014381879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48550231280677244009587919 72825346921015866014381879)
        ·
          refine ⟨109238020381523799021572819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72825346921015866014381879 109238020381523799021572819)
          ·
            refine ⟨163857030572285698532359229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109238020381523799021572819 163857030572285698532359229)
            ·
              refine ⟨61446386464607136949634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163857030572285698532359229 61446386464607136949634711)
              ·
                refine ⟨92169579696910705424452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61446386464607136949634711 92169579696910705424452067)
                ·
                  refine ⟨138254369545366058136678101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92169579696910705424452067 138254369545366058136678101)
                  ·
                    refine ⟨3240336786219516987578393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138254369545366058136678101 3240336786219516987578393)
                    ·
                      refine ⟨2430252589664637740683795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240336786219516987578393 2430252589664637740683795)
                      ·
                        rfl

theorem cell23_4732900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_4732900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732900 prefixEnd_4732900 := by exact prefixLift 4732900
  have htrace : WordTrace (prefixWord ++ tailWord_4732900) baseStart_4732900 baseEnd_4732900 := by
    simpa [prefixWord, tailWord_4732900, baseEnd_4732900] using wordTrace_append hprefix tailTrace_4732900
  have hstable : (prefixWord ++ tailWord_4732900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732900).length < 2 ^ (prefixWord ++ tailWord_4732900).sum := by decide
  have hdescent : baseEnd_4732900 < baseStart_4732900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732940 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_4732940 : Nat := 118140960795 + 4732940 * 2 ^ 59
def prefixEnd_4732940 : Nat := 4983230072969 + 3 ^ 40 * 4732940 * 2
def baseEnd_4732940 : Nat := 810091042963605861394537

theorem tailTrace_4732940 : CollatzResearch.WordTrace tailWord_4732940 prefixEnd_4732940 810091042963605861394537 := by
  unfold tailWord_4732940
  simp only [CollatzResearch.WordTrace]
  refine ⟨86312251736687088321662137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115083002315582784428882849 86312251736687088321662137)
  ·
    refine ⟨64734188802515316241246603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86312251736687088321662137 64734188802515316241246603)
    ·
      refine ⟨97101283203772974361869905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64734188802515316241246603 97101283203772974361869905)
      ·
        refine ⟨72825962402829730771402429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97101283203772974361869905 72825962402829730771402429)
        ·
          refine ⟨27309735901061149039275911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72825962402829730771402429 27309735901061149039275911)
          ·
            refine ⟨40964603851591723558913867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27309735901061149039275911 40964603851591723558913867)
            ·
              refine ⟨61446905777387585338370801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40964603851591723558913867 61446905777387585338370801)
              ·
                refine ⟨46085179333040689003778101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61446905777387585338370801 46085179333040689003778101)
                ·
                  refine ⟨4320485562472564594104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46085179333040689003778101 4320485562472564594104197)
                  ·
                    refine ⟨810091042963605861394537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320485562472564594104197 810091042963605861394537)
                    ·
                      rfl

theorem cell23_4732940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_4732940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732940 prefixEnd_4732940 := by exact prefixLift 4732940
  have htrace : WordTrace (prefixWord ++ tailWord_4732940) baseStart_4732940 baseEnd_4732940 := by
    simpa [prefixWord, tailWord_4732940, baseEnd_4732940] using wordTrace_append hprefix tailTrace_4732940
  have hstable : (prefixWord ++ tailWord_4732940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732940).length < 2 ^ (prefixWord ++ tailWord_4732940).sum := by decide
  have hdescent : baseEnd_4732940 < baseStart_4732940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4732957 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4732957 : Nat := 118140960795 + 4732957 * 2 ^ 59
def prefixEnd_4732957 : Nat := 4983230072969 + 3 ^ 40 * 4732957 * 2
def baseEnd_4732957 : Nat := 810093952687314672557011

theorem tailTrace_4732957 : CollatzResearch.WordTrace tailWord_4732957 prefixEnd_4732957 810093952687314672557011 := by
  unfold tailWord_4732957
  simp only [CollatzResearch.WordTrace]
  refine ⟨172625123514312588546693125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115083415676208392364462083 172625123514312588546693125)
  ·
    refine ⟨32367210658933610352504961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172625123514312588546693125 32367210658933610352504961)
    ·
      refine ⟨24275407994200207764378721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32367210658933610352504961 24275407994200207764378721)
      ·
        refine ⟨18206555995650155823284041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24275407994200207764378721 18206555995650155823284041)
        ·
          refine ⟨13654916996737616867463031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18206555995650155823284041 13654916996737616867463031)
          ·
            refine ⟨20482375495106425301194547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13654916996737616867463031 20482375495106425301194547)
            ·
              refine ⟨30723563242659637951791821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20482375495106425301194547 30723563242659637951791821)
              ·
                refine ⟨11521336215997364231921933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30723563242659637951791821 11521336215997364231921933)
                ·
                  refine ⟨4320501080999011586970725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11521336215997364231921933 4320501080999011586970725)
                  ·
                    refine ⟨810093952687314672557011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320501080999011586970725 810093952687314672557011)
                    ·
                      rfl

theorem cell23_4732957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4732957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4732957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4732957 prefixEnd_4732957 := by exact prefixLift 4732957
  have htrace : WordTrace (prefixWord ++ tailWord_4732957) baseStart_4732957 baseEnd_4732957 := by
    simpa [prefixWord, tailWord_4732957, baseEnd_4732957] using wordTrace_append hprefix tailTrace_4732957
  have hstable : (prefixWord ++ tailWord_4732957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4732957).length < 2 ^ (prefixWord ++ tailWord_4732957).sum := by decide
  have hdescent : baseEnd_4732957 < baseStart_4732957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4732957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733007 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 2, 3, 2]
def baseStart_4733007 : Nat := 118140960795 + 4733007 * 2 ^ 59
def prefixEnd_4733007 : Nat := 4983230072969 + 3 ^ 40 * 4733007 * 2
def baseEnd_4733007 : Nat := 2430307532094668822045803

theorem tailTrace_4733007 : CollatzResearch.WordTrace tailWord_4733007 prefixEnd_4733007 2430307532094668822045803 := by
  unfold tailWord_4733007
  simp only [CollatzResearch.WordTrace]
  refine ⟨172626947164131447086013275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115084631442754298057342183 172626947164131447086013275)
  ·
    refine ⟨258940420746197170629019913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172626947164131447086013275 258940420746197170629019913)
    ·
      refine ⟨194205315559647877971764935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258940420746197170629019913 194205315559647877971764935)
      ·
        refine ⟨291307973339471816957647403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194205315559647877971764935 291307973339471816957647403)
        ·
          refine ⟨436961960009207725436471105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291307973339471816957647403 436961960009207725436471105)
          ·
            refine ⟨327721470006905794077353329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436961960009207725436471105 327721470006905794077353329)
            ·
              refine ⟨245791102505179345558014997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327721470006905794077353329 245791102505179345558014997)
              ·
                refine ⟨11521457929930281823031953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 245791102505179345558014997 11521457929930281823031953)
                ·
                  refine ⟨8641093447447711367273965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11521457929930281823031953 8641093447447711367273965)
                  ·
                    refine ⟨3240410042792891762727737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8641093447447711367273965 3240410042792891762727737)
                    ·
                      refine ⟨2430307532094668822045803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240410042792891762727737 2430307532094668822045803)
                      ·
                        rfl

theorem cell23_4733007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3, 2].length) (baseStart_4733007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733007 prefixEnd_4733007 := by exact prefixLift 4733007
  have htrace : WordTrace (prefixWord ++ tailWord_4733007) baseStart_4733007 baseEnd_4733007 := by
    simpa [prefixWord, tailWord_4733007, baseEnd_4733007] using wordTrace_append hprefix tailTrace_4733007
  have hstable : (prefixWord ++ tailWord_4733007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733007).length < 2 ^ (prefixWord ++ tailWord_4733007).sum := by decide
  have hdescent : baseEnd_4733007 < baseStart_4733007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733021 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 6]
def baseStart_4733021 : Nat := 118140960795 + 4733021 * 2 ^ 59
def prefixEnd_4733021 : Nat := 4983230072969 + 3 ^ 40 * 4733021 * 2
def baseEnd_4733021 : Nat := 270034968980425751918971

theorem tailTrace_4733021 : CollatzResearch.WordTrace tailWord_4733021 prefixEnd_4733021 270034968980425751918971 := by
  unfold tailWord_4733021
  simp only [CollatzResearch.WordTrace]
  refine ⟨172627457786080727477022917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115084971857387151651348611 172627457786080727477022917)
  ·
    refine ⟨32367648334890136401941797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172627457786080727477022917 32367648334890136401941797)
    ·
      refine ⟨6068934062791900575364087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32367648334890136401941797 6068934062791900575364087)
      ·
        refine ⟨9103401094187850863046131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068934062791900575364087 9103401094187850863046131)
        ·
          refine ⟨13655101641281776294569197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103401094187850863046131 13655101641281776294569197)
          ·
            refine ⟨5120663115480666110463449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13655101641281776294569197 5120663115480666110463449)
            ·
              refine ⟨3840497336610499582847587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120663115480666110463449 3840497336610499582847587)
              ·
                refine ⟨5760746004915749374271381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840497336610499582847587 5760746004915749374271381)
                ·
                  refine ⟨270034968980425751918971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5760746004915749374271381 270034968980425751918971)
                  ·
                    rfl

theorem cell23_4733021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_4733021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733021 prefixEnd_4733021 := by exact prefixLift 4733021
  have htrace : WordTrace (prefixWord ++ tailWord_4733021) baseStart_4733021 baseEnd_4733021 := by
    simpa [prefixWord, tailWord_4733021, baseEnd_4733021] using wordTrace_append hprefix tailTrace_4733021
  have hstable : (prefixWord ++ tailWord_4733021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733021).length < 2 ^ (prefixWord ++ tailWord_4733021).sum := by decide
  have hdescent : baseEnd_4733021 < baseStart_4733021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733037 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4733037 : Nat := 118140960795 + 4733037 * 2 ^ 59
def prefixEnd_4733037 : Nat := 4983230072969 + 3 ^ 40 * 4733037 * 2
def baseEnd_4733037 : Nat := 2430322936514303704670665

theorem tailTrace_4733037 : CollatzResearch.WordTrace tailWord_4733037 prefixEnd_4733037 2430322936514303704670665 := by
  unfold tailWord_4733037
  simp only [CollatzResearch.WordTrace]
  refine ⟨172628041354022762209605365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115085360902681841473070243 172628041354022762209605365)
  ·
    refine ⟨16183878876939633957150503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172628041354022762209605365 16183878876939633957150503)
    ·
      refine ⟨24275818315409450935725755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16183878876939633957150503 24275818315409450935725755)
      ·
        refine ⟨36413727473114176403588633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24275818315409450935725755 36413727473114176403588633)
        ·
          refine ⟨27310295604835632302691475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36413727473114176403588633 27310295604835632302691475)
          ·
            refine ⟨40965443407253448454037213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27310295604835632302691475 40965443407253448454037213)
            ·
              refine ⟨15362041277720043170263955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40965443407253448454037213 15362041277720043170263955)
              ·
                refine ⟨23043061916580064755395933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15362041277720043170263955 23043061916580064755395933)
                ·
                  refine ⟨8641148218717524283273475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23043061916580064755395933 8641148218717524283273475)
                  ·
                    refine ⟨12961722328076286424910213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8641148218717524283273475 12961722328076286424910213)
                    ·
                      refine ⟨2430322936514303704670665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12961722328076286424910213 2430322936514303704670665)
                      ·
                        rfl

theorem cell23_4733037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4733037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733037 prefixEnd_4733037 := by exact prefixLift 4733037
  have htrace : WordTrace (prefixWord ++ tailWord_4733037) baseStart_4733037 baseEnd_4733037 := by
    simpa [prefixWord, tailWord_4733037, baseEnd_4733037] using wordTrace_append hprefix tailTrace_4733037
  have hstable : (prefixWord ++ tailWord_4733037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733037).length < 2 ^ (prefixWord ++ tailWord_4733037).sum := by decide
  have hdescent : baseEnd_4733037 < baseStart_4733037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733064 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_4733064 : Nat := 118140960795 + 4733064 * 2 ^ 59
def prefixEnd_4733064 : Nat := 4983230072969 + 3 ^ 40 * 4733064 * 2
def baseEnd_4733064 : Nat := 810112266830658366344347

theorem tailTrace_4733064 : CollatzResearch.WordTrace tailWord_4733064 prefixEnd_4733064 810112266830658366344347 := by
  unfold tailWord_4733064
  simp only [CollatzResearch.WordTrace]
  refine ⟨86314513062462472910419123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115086017416616630547225497 86314513062462472910419123)
  ·
    refine ⟨129471769593693709365628685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86314513062462472910419123 129471769593693709365628685)
    ·
      refine ⟨48551913597635141012110757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129471769593693709365628685 48551913597635141012110757)
      ·
        refine ⟨9103483799556588939770767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48551913597635141012110757 9103483799556588939770767)
        ·
          refine ⟨13655225699334883409656151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103483799556588939770767 13655225699334883409656151)
          ·
            refine ⟨20482838549002325114484227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13655225699334883409656151 20482838549002325114484227)
            ·
              refine ⟨30724257823503487671726341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20482838549002325114484227 30724257823503487671726341)
              ·
                refine ⟨5760798341906903938448689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30724257823503487671726341 5760798341906903938448689)
                ·
                  refine ⟨4320598756430177953836517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760798341906903938448689 4320598756430177953836517)
                  ·
                    refine ⟨810112266830658366344347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320598756430177953836517 810112266830658366344347)
                    ·
                      rfl

theorem cell23_4733064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_4733064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733064 prefixEnd_4733064 := by exact prefixLift 4733064
  have htrace : WordTrace (prefixWord ++ tailWord_4733064) baseStart_4733064 baseEnd_4733064 := by
    simpa [prefixWord, tailWord_4733064, baseEnd_4733064] using wordTrace_append hprefix tailTrace_4733064
  have hstable : (prefixWord ++ tailWord_4733064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733064).length < 2 ^ (prefixWord ++ tailWord_4733064).sum := by decide
  have hdescent : baseEnd_4733064 < baseStart_4733064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733105 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4733105 : Nat := 118140960795 + 4733105 * 2 ^ 59
def prefixEnd_4733105 : Nat := 4983230072969 + 3 ^ 40 * 4733105 * 2
def baseEnd_4733105 : Nat := 2430357853198809438620353

theorem tailTrace_4733105 : CollatzResearch.WordTrace tailWord_4733105 prefixEnd_4733105 2430357853198809438620353 := by
  unfold tailWord_4733105
  simp only [CollatzResearch.WordTrace]
  refine ⟨172630521517776409823080769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115087014345184273215387179 172630521517776409823080769)
  ·
    refine ⟨129472891138332307367310577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172630521517776409823080769 129472891138332307367310577)
    ·
      refine ⟨97104668353749230525482933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129472891138332307367310577 97104668353749230525482933)
      ·
        refine ⟨9103562658163990361764025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97104668353749230525482933 9103562658163990361764025)
        ·
          refine ⟨6827671993622992771323019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9103562658163990361764025 6827671993622992771323019)
          ·
            refine ⟨10241507990434489156984529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827671993622992771323019 10241507990434489156984529)
            ·
              refine ⟨7681130992825866867738397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10241507990434489156984529 7681130992825866867738397)
              ·
                refine ⟨2880424122309700075401899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7681130992825866867738397 2880424122309700075401899)
                ·
                  refine ⟨4320636183464550113102849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880424122309700075401899 4320636183464550113102849)
                  ·
                    refine ⟨3240477137598412584827137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320636183464550113102849 3240477137598412584827137)
                    ·
                      refine ⟨2430357853198809438620353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240477137598412584827137 2430357853198809438620353)
                      ·
                        rfl

theorem cell23_4733105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4733105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733105 prefixEnd_4733105 := by exact prefixLift 4733105
  have htrace : WordTrace (prefixWord ++ tailWord_4733105) baseStart_4733105 baseEnd_4733105 := by
    simpa [prefixWord, tailWord_4733105, baseEnd_4733105] using wordTrace_append hprefix tailTrace_4733105
  have hstable : (prefixWord ++ tailWord_4733105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733105).length < 2 ^ (prefixWord ++ tailWord_4733105).sum := by decide
  have hdescent : baseEnd_4733105 < baseStart_4733105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733122 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4733122 : Nat := 118140960795 + 4733122 * 2 ^ 59
def prefixEnd_4733122 : Nat := 4983230072969 + 3 ^ 40 * 4733122 * 2
def baseEnd_4733122 : Nat := 2430366582369935872107775

theorem tailTrace_4733122 : CollatzResearch.WordTrace tailWord_4733122 prefixEnd_4733122 2430366582369935872107775 := by
  unfold tailWord_4733122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43157785389678705431612405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115087427705809881150966413 43157785389678705431612405)
  ·
    refine ⟨4046042380282378634213663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43157785389678705431612405 4046042380282378634213663)
    ·
      refine ⟨6069063570423567951320495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046042380282378634213663 6069063570423567951320495)
      ·
        refine ⟨9103595355635351926980743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069063570423567951320495 9103595355635351926980743)
        ·
          refine ⟨13655393033453027890471115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103595355635351926980743 13655393033453027890471115)
          ·
            refine ⟨20483089550179541835706673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13655393033453027890471115 20483089550179541835706673)
            ·
              refine ⟨15362317162634656376780005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20483089550179541835706673 15362317162634656376780005)
              ·
                refine ⟨2880434467993998070646251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15362317162634656376780005 2880434467993998070646251)
                ·
                  refine ⟨4320651701990997105969377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880434467993998070646251 4320651701990997105969377)
                  ·
                    refine ⟨3240488776493247829477033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320651701990997105969377 3240488776493247829477033)
                    ·
                      refine ⟨2430366582369935872107775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240488776493247829477033 2430366582369935872107775)
                      ·
                        rfl

theorem cell23_4733122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4733122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733122 prefixEnd_4733122 := by exact prefixLift 4733122
  have htrace : WordTrace (prefixWord ++ tailWord_4733122) baseStart_4733122 baseEnd_4733122 := by
    simpa [prefixWord, tailWord_4733122, baseEnd_4733122] using wordTrace_append hprefix tailTrace_4733122
  have hstable : (prefixWord ++ tailWord_4733122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733122).length < 2 ^ (prefixWord ++ tailWord_4733122).sum := by decide
  have hdescent : baseEnd_4733122 < baseStart_4733122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733127 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_4733127 : Nat := 118140960795 + 4733127 * 2 ^ 59
def prefixEnd_4733127 : Nat := 4983230072969 + 3 ^ 40 * 4733127 * 2
def baseEnd_4733127 : Nat := 2430369149773208352545251

theorem tailTrace_4733127 : CollatzResearch.WordTrace tailWord_4733127 prefixEnd_4733127 2430369149773208352545251 := by
  unfold tailWord_4733127
  simp only [CollatzResearch.WordTrace]
  refine ⟨172631323923696707580381635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115087549282464471720254423 172631323923696707580381635)
  ·
    refine ⟨258946985885545061370572453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172631323923696707580381635 258946985885545061370572453)
    ·
      refine ⟨48552559853539699006982335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258946985885545061370572453 48552559853539699006982335)
      ·
        refine ⟨72828839780309548510473503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48552559853539699006982335 72828839780309548510473503)
        ·
          refine ⟨109243259670464322765710255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72828839780309548510473503 109243259670464322765710255)
          ·
            refine ⟨163864889505696484148565383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109243259670464322765710255 163864889505696484148565383)
            ·
              refine ⟨245797334258544726222848075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163864889505696484148565383 245797334258544726222848075)
              ·
                refine ⟨368696001387817089334272113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245797334258544726222848075 368696001387817089334272113)
                ·
                  refine ⟨276522001040862817000704085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368696001387817089334272113 276522001040862817000704085)
                  ·
                    refine ⟨3240492199697611136727001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 276522001040862817000704085 3240492199697611136727001)
                    ·
                      refine ⟨2430369149773208352545251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240492199697611136727001 2430369149773208352545251)
                      ·
                        rfl

theorem cell23_4733127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_4733127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733127 prefixEnd_4733127 := by exact prefixLift 4733127
  have htrace : WordTrace (prefixWord ++ tailWord_4733127) baseStart_4733127 baseEnd_4733127 := by
    simpa [prefixWord, tailWord_4733127, baseEnd_4733127] using wordTrace_append hprefix tailTrace_4733127
  have hstable : (prefixWord ++ tailWord_4733127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733127).length < 2 ^ (prefixWord ++ tailWord_4733127).sum := by decide
  have hdescent : baseEnd_4733127 < baseStart_4733127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733138 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4733138 : Nat := 118140960795 + 4733138 * 2 ^ 59
def prefixEnd_4733138 : Nat := 4983230072969 + 3 ^ 40 * 4733138 * 2
def baseEnd_4733138 : Nat := 2430374798060407809507701

theorem tailTrace_4733138 : CollatzResearch.WordTrace tailWord_4733138 prefixEnd_4733138 2430374798060407809507701 := by
  unfold tailWord_4733138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43157931281664214114758017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115087816751104570972688045 43157931281664214114758017)
  ·
    refine ⟨32368448461248160586068513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43157931281664214114758017 32368448461248160586068513)
    ·
      refine ⟨24276336345936120439551385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32368448461248160586068513 24276336345936120439551385)
      ·
        refine ⟨18207252259452090329663539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24276336345936120439551385 18207252259452090329663539)
        ·
          refine ⟨27310878389178135494495309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18207252259452090329663539 27310878389178135494495309)
          ·
            refine ⟨10241579395941800810435741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27310878389178135494495309 10241579395941800810435741)
            ·
              refine ⟨3840592273478175303913403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10241579395941800810435741 3840592273478175303913403)
              ·
                refine ⟨5760888410217262955870105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840592273478175303913403 5760888410217262955870105)
                ·
                  refine ⟨4320666307662947216902579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760888410217262955870105 4320666307662947216902579)
                  ·
                    refine ⟨6480999461494420825353869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320666307662947216902579 6480999461494420825353869)
                    ·
                      refine ⟨2430374798060407809507701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6480999461494420825353869 2430374798060407809507701)
                      ·
                        rfl

theorem cell23_4733138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4733138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733138 prefixEnd_4733138 := by exact prefixLift 4733138
  have htrace : WordTrace (prefixWord ++ tailWord_4733138) baseStart_4733138 baseEnd_4733138 := by
    simpa [prefixWord, tailWord_4733138, baseEnd_4733138] using wordTrace_append hprefix tailTrace_4733138
  have hstable : (prefixWord ++ tailWord_4733138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733138).length < 2 ^ (prefixWord ++ tailWord_4733138).sum := by decide
  have hdescent : baseEnd_4733138 < baseStart_4733138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733177 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4733177 : Nat := 118140960795 + 4733177 * 2 ^ 59
def prefixEnd_4733177 : Nat := 4983230072969 + 3 ^ 40 * 4733177 * 2
def baseEnd_4733177 : Nat := 2430394823805933156920021

theorem tailTrace_4733177 : CollatzResearch.WordTrace tailWord_4733177 prefixEnd_4733177 2430394823805933156920021 := by
  unfold tailWord_4733177
  simp only [CollatzResearch.WordTrace]
  refine ⟨172633147573515566119701785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115088765049010377413134523 172633147573515566119701785)
  ·
    refine ⟨129474860680136674589776339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172633147573515566119701785 129474860680136674589776339)
    ·
      refine ⟨194212291020205011884664509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129474860680136674589776339 194212291020205011884664509)
      ·
        refine ⟨72829609132576879456749191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194212291020205011884664509 72829609132576879456749191)
        ·
          refine ⟨109244413698865319185123787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72829609132576879456749191 109244413698865319185123787)
          ·
            refine ⟨163866620548297978777685681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109244413698865319185123787 163866620548297978777685681)
            ·
              refine ⟨122899965411223484083264261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163866620548297978777685681 122899965411223484083264261)
              ·
                refine ⟨23043743514604403265612049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122899965411223484083264261 23043743514604403265612049)
                ·
                  refine ⟨17282807635953302449209037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23043743514604403265612049 17282807635953302449209037)
                  ·
                    refine ⟨6481052863482488418453389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17282807635953302449209037 6481052863482488418453389)
                    ·
                      refine ⟨2430394823805933156920021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481052863482488418453389 2430394823805933156920021)
                      ·
                        rfl

theorem cell23_4733177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4733177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733177 prefixEnd_4733177 := by exact prefixLift 4733177
  have htrace : WordTrace (prefixWord ++ tailWord_4733177) baseStart_4733177 baseEnd_4733177 := by
    simpa [prefixWord, tailWord_4733177, baseEnd_4733177] using wordTrace_append hprefix tailTrace_4733177
  have hstable : (prefixWord ++ tailWord_4733177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733177).length < 2 ^ (prefixWord ++ tailWord_4733177).sum := by decide
  have hdescent : baseEnd_4733177 < baseStart_4733177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733217 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4733217 : Nat := 118140960795 + 4733217 * 2 ^ 59
def prefixEnd_4733217 : Nat := 4983230072969 + 3 ^ 40 * 4733217 * 2
def baseEnd_4733217 : Nat := 2430415363032113000419837

theorem tailTrace_4733217 : CollatzResearch.WordTrace tailWord_4733217 prefixEnd_4733217 2430415363032113000419837 := by
  unfold tailWord_4733217
  simp only [CollatzResearch.WordTrace]
  refine ⟨172634606493370652951157905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115089737662247101967438603 172634606493370652951157905)
  ·
    refine ⟨129475954870027989713368429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172634606493370652951157905 129475954870027989713368429)
    ·
      refine ⟨48553483076260496142513161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129475954870027989713368429 48553483076260496142513161)
      ·
        refine ⟨36415112307195372106884871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48553483076260496142513161 36415112307195372106884871)
        ·
          refine ⟨54622668460793058160327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36415112307195372106884871 54622668460793058160327307)
          ·
            refine ⟨81934002691189587240490961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54622668460793058160327307 81934002691189587240490961)
            ·
              refine ⟨61450502018392190430368221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81934002691189587240490961 61450502018392190430368221)
              ·
                refine ⟨23043938256897071411388083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61450502018392190430368221 23043938256897071411388083)
                ·
                  refine ⟨34565907385345607117082125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23043938256897071411388083 34565907385345607117082125)
                  ·
                    refine ⟨12962215269504602668905797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34565907385345607117082125 12962215269504602668905797)
                    ·
                      refine ⟨2430415363032113000419837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12962215269504602668905797 2430415363032113000419837)
                      ·
                        rfl

theorem cell23_4733217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4733217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733217 prefixEnd_4733217 := by exact prefixLift 4733217
  have htrace : WordTrace (prefixWord ++ tailWord_4733217) baseStart_4733217 baseEnd_4733217 := by
    simpa [prefixWord, tailWord_4733217, baseEnd_4733217] using wordTrace_append hprefix tailTrace_4733217
  have hstable : (prefixWord ++ tailWord_4733217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733217).length < 2 ^ (prefixWord ++ tailWord_4733217).sum := by decide
  have hdescent : baseEnd_4733217 < baseStart_4733217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733237 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4733237 : Nat := 118140960795 + 4733237 * 2 ^ 59
def prefixEnd_4733237 : Nat := 4983230072969 + 3 ^ 40 * 4733237 * 2
def baseEnd_4733237 : Nat := 2430425632645202922169745

theorem tailTrace_4733237 : CollatzResearch.WordTrace tailWord_4733237 prefixEnd_4733237 2430425632645202922169745 := by
  unfold tailWord_4733237
  simp only [CollatzResearch.WordTrace]
  refine ⟨172635335953298196366885965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115090223968865464244590643 172635335953298196366885965)
  ·
    refine ⟨64738250982486823637582237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172635335953298196366885965 64738250982486823637582237)
    ·
      refine ⟨24276844118432558864093339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64738250982486823637582237 24276844118432558864093339)
      ·
        refine ⟨36415266177648838296140009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24276844118432558864093339 36415266177648838296140009)
        ·
          refine ⟨27311449633236628722105007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36415266177648838296140009 27311449633236628722105007)
          ·
            refine ⟨40967174449854943083157511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27311449633236628722105007 40967174449854943083157511)
            ·
              refine ⟨61450761674782414624736267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40967174449854943083157511 61450761674782414624736267)
              ·
                refine ⟨92176142512173621937104401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61450761674782414624736267 92176142512173621937104401)
                ·
                  refine ⟨69132106884130216452828301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92176142512173621937104401 69132106884130216452828301)
                  ·
                    refine ⟨25924540081548831169810613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69132106884130216452828301 25924540081548831169810613)
                    ·
                      refine ⟨2430425632645202922169745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25924540081548831169810613 2430425632645202922169745)
                      ·
                        rfl

theorem cell23_4733237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4733237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733237 prefixEnd_4733237 := by exact prefixLift 4733237
  have htrace : WordTrace (prefixWord ++ tailWord_4733237) baseStart_4733237 baseEnd_4733237 := by
    simpa [prefixWord, tailWord_4733237, baseEnd_4733237] using wordTrace_append hprefix tailTrace_4733237
  have hstable : (prefixWord ++ tailWord_4733237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733237).length < 2 ^ (prefixWord ++ tailWord_4733237).sum := by decide
  have hdescent : baseEnd_4733237 < baseStart_4733237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733244 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_4733244 : Nat := 118140960795 + 4733244 * 2 ^ 59
def prefixEnd_4733244 : Nat := 4983230072969 + 3 ^ 40 * 4733244 * 2
def baseEnd_4733244 : Nat := 810143075669928131594071

theorem tailTrace_4733244 : CollatzResearch.WordTrace tailWord_4733244 prefixEnd_4733244 810143075669928131594071 := by
  unfold tailWord_4733244
  simp only [CollatzResearch.WordTrace]
  refine ⟨86317795632136418281195393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115090394176181891041593857 86317795632136418281195393)
  ·
    refine ⟨64738346724102313710896545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86317795632136418281195393 64738346724102313710896545)
    ·
      refine ⟨48553760043076735283172409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64738346724102313710896545 48553760043076735283172409)
      ·
        refine ⟨36415320032307551462379307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48553760043076735283172409 36415320032307551462379307)
        ·
          refine ⟨54622980048461327193568961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36415320032307551462379307 54622980048461327193568961)
          ·
            refine ⟨40967235036345995395176721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54622980048461327193568961 40967235036345995395176721)
            ·
              refine ⟨30725426277259496546382541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40967235036345995395176721 30725426277259496546382541)
              ·
                refine ⟨11522034853972311204893453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30725426277259496546382541 11522034853972311204893453)
                ·
                  refine ⟨4320763070239616701835045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11522034853972311204893453 4320763070239616701835045)
                  ·
                    refine ⟨810143075669928131594071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320763070239616701835045 810143075669928131594071)
                    ·
                      rfl

theorem cell23_4733244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_4733244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733244 prefixEnd_4733244 := by exact prefixLift 4733244
  have htrace : WordTrace (prefixWord ++ tailWord_4733244) baseStart_4733244 baseEnd_4733244 := by
    simpa [prefixWord, tailWord_4733244, baseEnd_4733244] using wordTrace_append hprefix tailTrace_4733244
  have hstable : (prefixWord ++ tailWord_4733244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733244).length < 2 ^ (prefixWord ++ tailWord_4733244).sum := by decide
  have hdescent : baseEnd_4733244 < baseStart_4733244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733267 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3]
def baseStart_4733267 : Nat := 118140960795 + 4733267 * 2 ^ 59
def prefixEnd_4733267 : Nat := 4983230072969 + 3 ^ 40 * 4733267 * 2
def baseEnd_4733267 : Nat := 2430441037064837804794607

theorem tailTrace_4733267 : CollatzResearch.WordTrace tailWord_4733267 prefixEnd_4733267 2430441037064837804794607 := by
  unfold tailWord_4733267
  simp only [CollatzResearch.WordTrace]
  refine ⟨172636430143189511490478055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115090953428793007660318703 172636430143189511490478055)
  ·
    refine ⟨258954645214784267235717083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172636430143189511490478055 258954645214784267235717083)
    ·
      refine ⟨388431967822176400853575625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258954645214784267235717083 388431967822176400853575625)
      ·
        refine ⟨291323975866632300640181719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388431967822176400853575625 291323975866632300640181719)
        ·
          refine ⟨436985963799948450960272579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291323975866632300640181719 436985963799948450960272579)
          ·
            refine ⟨655478945699922676440408869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436985963799948450960272579 655478945699922676440408869)
            ·
              refine ⟨122902302318735501832576663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 655478945699922676440408869 122902302318735501832576663)
              ·
                refine ⟨184353453478103252748864995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122902302318735501832576663 184353453478103252748864995)
                ·
                  refine ⟨276530180217154879123297493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184353453478103252748864995 276530180217154879123297493)
                  ·
                    refine ⟨6481176098839567479452285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 276530180217154879123297493 6481176098839567479452285)
                    ·
                      refine ⟨2430441037064837804794607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481176098839567479452285 2430441037064837804794607)
                      ·
                        rfl

theorem cell23_4733267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_4733267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733267 prefixEnd_4733267 := by exact prefixLift 4733267
  have htrace : WordTrace (prefixWord ++ tailWord_4733267) baseStart_4733267 baseEnd_4733267 := by
    simpa [prefixWord, tailWord_4733267, baseEnd_4733267] using wordTrace_append hprefix tailTrace_4733267
  have hstable : (prefixWord ++ tailWord_4733267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733267).length < 2 ^ (prefixWord ++ tailWord_4733267).sum := by decide
  have hdescent : baseEnd_4733267 < baseStart_4733267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733321 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_4733321 : Nat := 118140960795 + 4733321 * 2 ^ 59
def prefixEnd_4733321 : Nat := 4983230072969 + 3 ^ 40 * 4733321 * 2
def baseEnd_4733321 : Nat := 810156255006726864506453

theorem tailTrace_4733321 : CollatzResearch.WordTrace tailWord_4733321 prefixEnd_4733321 810156255006726864506453 := by
  unfold tailWord_4733321
  simp only [CollatzResearch.WordTrace]
  refine ⟨172638399684993878712943817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115092266456662585808629211 172638399684993878712943817)
  ·
    refine ⟨129478799763745409034707863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172638399684993878712943817 129478799763745409034707863)
    ·
      refine ⟨194218199645618113552061795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129478799763745409034707863 194218199645618113552061795)
      ·
        refine ⟨291327299468427170328092693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194218199645618113552061795 291327299468427170328092693)
        ·
          refine ⟨13655967162582523609129345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 291327299468427170328092693 13655967162582523609129345)
          ·
            refine ⟨10241975371936892706847009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13655967162582523609129345 10241975371936892706847009)
            ·
              refine ⟨7681481528952669530135257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10241975371936892706847009 7681481528952669530135257)
              ·
                refine ⟨5761111146714502147601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681481528952669530135257 5761111146714502147601443)
                ·
                  refine ⟨8641666720071753221402165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761111146714502147601443 8641666720071753221402165)
                  ·
                    refine ⟨810156255006726864506453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8641666720071753221402165 810156255006726864506453)
                    ·
                      rfl

theorem cell23_4733321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_4733321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733321 prefixEnd_4733321 := by exact prefixLift 4733321
  have htrace : WordTrace (prefixWord ++ tailWord_4733321) baseStart_4733321 baseEnd_4733321 := by
    simpa [prefixWord, tailWord_4733321, baseEnd_4733321] using wordTrace_append hprefix tailTrace_4733321
  have hstable : (prefixWord ++ tailWord_4733321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733321).length < 2 ^ (prefixWord ++ tailWord_4733321).sum := by decide
  have hdescent : baseEnd_4733321 < baseStart_4733321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733344 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4733344 : Nat := 118140960795 + 4733344 * 2 ^ 59
def prefixEnd_4733344 : Nat := 4983230072969 + 3 ^ 40 * 4733344 * 2
def baseEnd_4733344 : Nat := 2430480575075234003531753

theorem tailTrace_4733344 : CollatzResearch.WordTrace tailWord_4733344 prefixEnd_4733344 2430480575075234003531753 := by
  unfold tailWord_4733344
  simp only [CollatzResearch.WordTrace]
  refine ⟨86319619281955276820515543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115092825709273702427354057 86319619281955276820515543)
  ·
    refine ⟨129479428922932915230773315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86319619281955276820515543 129479428922932915230773315)
    ·
      refine ⟨194219143384399372846159973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129479428922932915230773315 194219143384399372846159973)
      ·
        refine ⟨36416089384574882408654995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194219143384399372846159973 36416089384574882408654995)
        ·
          refine ⟨54624134076862323612982493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36416089384574882408654995 54624134076862323612982493)
          ·
            refine ⟨20484050278823371354868435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54624134076862323612982493 20484050278823371354868435)
            ·
              refine ⟨30726075418235057032302653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20484050278823371354868435 30726075418235057032302653)
              ·
                refine ⟨11522278281838146387113495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30726075418235057032302653 11522278281838146387113495)
                ·
                  refine ⟨17283417422757219580670243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11522278281838146387113495 17283417422757219580670243)
                  ·
                    refine ⟨25925126134135829371005365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17283417422757219580670243 25925126134135829371005365)
                    ·
                      refine ⟨2430480575075234003531753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25925126134135829371005365 2430480575075234003531753)
                      ·
                        rfl

theorem cell23_4733344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4733344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733344 prefixEnd_4733344 := by exact prefixLift 4733344
  have htrace : WordTrace (prefixWord ++ tailWord_4733344) baseStart_4733344 baseEnd_4733344 := by
    simpa [prefixWord, tailWord_4733344, baseEnd_4733344] using wordTrace_append hprefix tailTrace_4733344
  have hstable : (prefixWord ++ tailWord_4733344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733344).length < 2 ^ (prefixWord ++ tailWord_4733344).sum := by decide
  have hdescent : baseEnd_4733344 < baseStart_4733344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733345 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4733345 : Nat := 118140960795 + 4733345 * 2 ^ 59
def prefixEnd_4733345 : Nat := 4983230072969 + 3 ^ 40 * 4733345 * 2
def baseEnd_4733345 : Nat := 2430481088555888499619249

theorem tailTrace_4733345 : CollatzResearch.WordTrace tailWord_4733345 prefixEnd_4733345 2430481088555888499619249 := by
  unfold tailWord_4733345
  simp only [CollatzResearch.WordTrace]
  refine ⟨172639275036906930811817489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115092850024604620541211659 172639275036906930811817489)
  ·
    refine ⟨129479456277680198108863117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172639275036906930811817489 129479456277680198108863117)
    ·
      refine ⟨48554796104130074290823669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129479456277680198108863117 48554796104130074290823669)
      ·
        refine ⟨4552012134762194464764719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48554796104130074290823669 4552012134762194464764719)
        ·
          refine ⟨6828018202143291697147079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552012134762194464764719 6828018202143291697147079)
          ·
            refine ⟨10242027303214937545720619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828018202143291697147079 10242027303214937545720619)
            ·
              refine ⟨15363040954822406318580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10242027303214937545720619 15363040954822406318580929)
              ·
                refine ⟨11522280716116804738935697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15363040954822406318580929 11522280716116804738935697)
                ·
                  refine ⟨8641710537087603554201773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11522280716116804738935697 8641710537087603554201773)
                  ·
                    refine ⟨3240641451407851332825665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8641710537087603554201773 3240641451407851332825665)
                    ·
                      refine ⟨2430481088555888499619249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240641451407851332825665 2430481088555888499619249)
                      ·
                        rfl

theorem cell23_4733345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4733345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733345 prefixEnd_4733345 := by exact prefixLift 4733345
  have htrace : WordTrace (prefixWord ++ tailWord_4733345) baseStart_4733345 baseEnd_4733345 := by
    simpa [prefixWord, tailWord_4733345, baseEnd_4733345] using wordTrace_append hprefix tailTrace_4733345
  have hstable : (prefixWord ++ tailWord_4733345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733345).length < 2 ^ (prefixWord ++ tailWord_4733345).sum := by decide
  have hdescent : baseEnd_4733345 < baseStart_4733345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733347 : List Nat := [1, 1, 1, 4, 1, 4, 11]
def baseStart_4733347 : Nat := 118140960795 + 4733347 * 2 ^ 59
def prefixEnd_4733347 : Nat := 4983230072969 + 3 ^ 40 * 4733347 * 2
def baseEnd_4733347 : Nat := 30005952043422191256719

theorem tailTrace_4733347 : CollatzResearch.WordTrace tailWord_4733347 prefixEnd_4733347 30005952043422191256719 := by
  unfold tailWord_4733347
  simp only [CollatzResearch.WordTrace]
  refine ⟨172639347982899685153390295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115092898655266456768926863 172639347982899685153390295)
  ·
    refine ⟨258959021974349527730085443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172639347982899685153390295 258959021974349527730085443)
    ·
      refine ⟨388438532961524291595128165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258959021974349527730085443 388438532961524291595128165)
      ·
        refine ⟨72832224930285804674086531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388438532961524291595128165 72832224930285804674086531)
        ·
          refine ⟨109248337395428707011129797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72832224930285804674086531 109248337395428707011129797)
          ·
            refine ⟨20484063261642882564586837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109248337395428707011129797 20484063261642882564586837)
            ·
              refine ⟨30005952043422191256719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20484063261642882564586837 30005952043422191256719)
              ·
                rfl

theorem cell23_4733347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 11].length) (baseStart_4733347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733347 prefixEnd_4733347 := by exact prefixLift 4733347
  have htrace : WordTrace (prefixWord ++ tailWord_4733347) baseStart_4733347 baseEnd_4733347 := by
    simpa [prefixWord, tailWord_4733347, baseEnd_4733347] using wordTrace_append hprefix tailTrace_4733347
  have hstable : (prefixWord ++ tailWord_4733347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733347).length < 2 ^ (prefixWord ++ tailWord_4733347).sum := by decide
  have hdescent : baseEnd_4733347 < baseStart_4733347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733351 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4733351 : Nat := 118140960795 + 4733351 * 2 ^ 59
def prefixEnd_4733351 : Nat := 4983230072969 + 3 ^ 40 * 4733351 * 2
def baseEnd_4733351 : Nat := 810161389813271825381407

theorem tailTrace_4733351 : CollatzResearch.WordTrace tailWord_4733351 prefixEnd_4733351 810161389813271825381407 := by
  unfold tailWord_4733351
  simp only [CollatzResearch.WordTrace]
  refine ⟨172639493874885193836535907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115092995916590129224357271 172639493874885193836535907)
  ·
    refine ⟨258959240812327790754803861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172639493874885193836535907 258959240812327790754803861)
    ·
      refine ⟨12138714413077865191631431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 258959240812327790754803861 12138714413077865191631431)
      ·
        refine ⟨18208071619616797787447147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12138714413077865191631431 18208071619616797787447147)
        ·
          refine ⟨27312107429425196681170721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208071619616797787447147 27312107429425196681170721)
          ·
            refine ⟨20484080572068897510878041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27312107429425196681170721 20484080572068897510878041)
            ·
              refine ⟨15363060429051673133158531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20484080572068897510878041 15363060429051673133158531)
              ·
                refine ⟨23044590643577509699737797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15363060429051673133158531 23044590643577509699737797)
                ·
                  refine ⟨4320860745670783068700837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23044590643577509699737797 4320860745670783068700837)
                  ·
                    refine ⟨810161389813271825381407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320860745670783068700837 810161389813271825381407)
                    ·
                      rfl

theorem cell23_4733351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4733351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733351 prefixEnd_4733351 := by exact prefixLift 4733351
  have htrace : WordTrace (prefixWord ++ tailWord_4733351) baseStart_4733351 baseEnd_4733351 := by
    simpa [prefixWord, tailWord_4733351, baseEnd_4733351] using wordTrace_append hprefix tailTrace_4733351
  have hstable : (prefixWord ++ tailWord_4733351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733351).length < 2 ^ (prefixWord ++ tailWord_4733351).sum := by decide
  have hdescent : baseEnd_4733351 < baseStart_4733351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733408 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_4733408 : Nat := 118140960795 + 4733408 * 2 ^ 59
def prefixEnd_4733408 : Nat := 4983230072969 + 3 ^ 40 * 4733408 * 2
def baseEnd_4733408 : Nat := 2430513437837121753131459

theorem tailTrace_4733408 : CollatzResearch.WordTrace tailWord_4733408 prefixEnd_4733408 2430513437837121753131459 := by
  unfold tailWord_4733408
  simp only [CollatzResearch.WordTrace]
  refine ⟨86320786417839346285680439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115094381890452461714240585 86320786417839346285680439)
  ·
    refine ⟨129481179626759019428520659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86320786417839346285680439 129481179626759019428520659)
    ·
      refine ⟨194221769440138529142780989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129481179626759019428520659 194221769440138529142780989)
      ·
        refine ⟨72833163540051948428542871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194221769440138529142780989 72833163540051948428542871)
        ·
          refine ⟨109249745310077922642814307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72833163540051948428542871 109249745310077922642814307)
          ·
            refine ⟨163874617965116883964221461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109249745310077922642814307 163874617965116883964221461)
            ·
              refine ⟨7681622717114853935822881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163874617965116883964221461 7681622717114853935822881)
              ·
                refine ⟨5761217037836140451867161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681622717114853935822881 5761217037836140451867161)
                ·
                  refine ⟨4320912778377105338900371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761217037836140451867161 4320912778377105338900371)
                  ·
                    refine ⟨6481369167565658008350557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320912778377105338900371 6481369167565658008350557)
                    ·
                      refine ⟨2430513437837121753131459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481369167565658008350557 2430513437837121753131459)
                      ·
                        rfl

theorem cell23_4733408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_4733408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733408 prefixEnd_4733408 := by exact prefixLift 4733408
  have htrace : WordTrace (prefixWord ++ tailWord_4733408) baseStart_4733408 baseEnd_4733408 := by
    simpa [prefixWord, tailWord_4733408, baseEnd_4733408] using wordTrace_append hprefix tailTrace_4733408
  have hstable : (prefixWord ++ tailWord_4733408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733408).length < 2 ^ (prefixWord ++ tailWord_4733408).sum := by decide
  have hdescent : baseEnd_4733408 < baseStart_4733408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733418 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_4733418 : Nat := 118140960795 + 4733418 * 2 ^ 59
def prefixEnd_4733418 : Nat := 4983230072969 + 3 ^ 40 * 4733418 * 2
def baseEnd_4733418 : Nat := 2430518572643666714006413

theorem tailTrace_4733418 : CollatzResearch.WordTrace tailWord_4733418 prefixEnd_4733418 2430518572643666714006413 := by
  unfold tailWord_4733418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43160484391410616069806227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115094625043761642852816605 43160484391410616069806227)
  ·
    refine ⟨64740726587115924104709341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43160484391410616069806227 64740726587115924104709341)
    ·
      refine ⟨24277772470168471539266003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64740726587115924104709341 24277772470168471539266003)
      ·
        refine ⟨36416658705252707308899005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24277772470168471539266003 36416658705252707308899005)
        ·
          refine ⟨13656247014469765240837127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36416658705252707308899005 13656247014469765240837127)
          ·
            refine ⟨20484370521704647861255691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656247014469765240837127 20484370521704647861255691)
            ·
              refine ⟨30726555782556971791883537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20484370521704647861255691 30726555782556971791883537)
              ·
                refine ⟨23044916836917728843912653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30726555782556971791883537 23044916836917728843912653)
                ·
                  refine ⟨8641843813844148316467245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23044916836917728843912653 8641843813844148316467245)
                  ·
                    refine ⟨3240691430191555618675217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8641843813844148316467245 3240691430191555618675217)
                    ·
                      refine ⟨2430518572643666714006413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240691430191555618675217 2430518572643666714006413)
                      ·
                        rfl

theorem cell23_4733418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_4733418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733418 prefixEnd_4733418 := by exact prefixLift 4733418
  have htrace : WordTrace (prefixWord ++ tailWord_4733418) baseStart_4733418 baseEnd_4733418 := by
    simpa [prefixWord, tailWord_4733418, baseEnd_4733418] using wordTrace_append hprefix tailTrace_4733418
  have hstable : (prefixWord ++ tailWord_4733418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733418).length < 2 ^ (prefixWord ++ tailWord_4733418).sum := by decide
  have hdescent : baseEnd_4733418 < baseStart_4733418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733424 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_4733424 : Nat := 118140960795 + 4733424 * 2 ^ 59
def prefixEnd_4733424 : Nat := 4983230072969 + 3 ^ 40 * 4733424 * 2
def baseEnd_4733424 : Nat := 810173884509197896843795

theorem tailTrace_4733424 : CollatzResearch.WordTrace tailWord_4733424 prefixEnd_4733424 810173884509197896843795 := by
  unfold tailWord_4733424
  simp only [CollatzResearch.WordTrace]
  refine ⟨86321078201810363651971663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115094770935747151535962217 86321078201810363651971663)
  ·
    refine ⟨129481617302715545477957495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86321078201810363651971663 129481617302715545477957495)
    ·
      refine ⟨194222425954073318216936243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129481617302715545477957495 194222425954073318216936243)
      ·
        refine ⟨291333638931109977325404365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194222425954073318216936243 291333638931109977325404365)
        ·
          refine ⟨109250114599166241497026637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291333638931109977325404365 109250114599166241497026637)
          ·
            refine ⟨40968792974687340561384989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109250114599166241497026637 40968792974687340561384989)
            ·
              refine ⟨15363297365507752710519371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40968792974687340561384989 15363297365507752710519371)
              ·
                refine ⟨23044946048261629065779057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15363297365507752710519371 23044946048261629065779057)
                ·
                  refine ⟨17283709536196221799334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23044946048261629065779057 17283709536196221799334293)
                  ·
                    refine ⟨810173884509197896843795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17283709536196221799334293 810173884509197896843795)
                    ·
                      rfl

theorem cell23_4733424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_4733424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733424 prefixEnd_4733424 := by exact prefixLift 4733424
  have htrace : WordTrace (prefixWord ++ tailWord_4733424) baseStart_4733424 baseEnd_4733424 := by
    simpa [prefixWord, tailWord_4733424, baseEnd_4733424] using wordTrace_append hprefix tailTrace_4733424
  have hstable : (prefixWord ++ tailWord_4733424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733424).length < 2 ^ (prefixWord ++ tailWord_4733424).sum := by decide
  have hdescent : baseEnd_4733424 < baseStart_4733424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733434 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_4733434 : Nat := 118140960795 + 4733434 * 2 ^ 59
def prefixEnd_4733434 : Nat := 4983230072969 + 3 ^ 40 * 4733434 * 2
def baseEnd_4733434 : Nat := 2430526788334138651406339

theorem tailTrace_4733434 : CollatzResearch.WordTrace tailWord_4733434 prefixEnd_4733434 2430526788334138651406339 := by
  unfold tailWord_4733434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43160630283396124752951839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115095014089056332674538237 43160630283396124752951839)
  ·
    refine ⟨64740945425094187129427759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43160630283396124752951839 64740945425094187129427759)
    ·
      refine ⟨97111418137641280694141639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64740945425094187129427759 97111418137641280694141639)
      ·
        refine ⟨145667127206461921041212459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97111418137641280694141639 145667127206461921041212459)
        ·
          refine ⟨218500690809692881561818689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145667127206461921041212459 218500690809692881561818689)
          ·
            refine ⟨163875518107269661171364017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218500690809692881561818689 163875518107269661171364017)
            ·
              refine ⟨122906638580452245878523013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163875518107269661171364017 122906638580452245878523013)
              ·
                refine ⟨23044994733834796102223065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122906638580452245878523013 23044994733834796102223065)
                ·
                  refine ⟨17283746050376097076667299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23044994733834796102223065 17283746050376097076667299)
                  ·
                    refine ⟨25925619075564145615000949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17283746050376097076667299 25925619075564145615000949)
                    ·
                      refine ⟨2430526788334138651406339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25925619075564145615000949 2430526788334138651406339)
                      ·
                        rfl

theorem cell23_4733434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_4733434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733434 prefixEnd_4733434 := by exact prefixLift 4733434
  have htrace : WordTrace (prefixWord ++ tailWord_4733434) baseStart_4733434 baseEnd_4733434 := by
    simpa [prefixWord, tailWord_4733434, baseEnd_4733434] using wordTrace_append hprefix tailTrace_4733434
  have hstable : (prefixWord ++ tailWord_4733434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733434).length < 2 ^ (prefixWord ++ tailWord_4733434).sum := by decide
  have hdescent : baseEnd_4733434 < baseStart_4733434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733446 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4733446 : Nat := 118140960795 + 4733446 * 2 ^ 59
def prefixEnd_4733446 : Nat := 4983230072969 + 3 ^ 40 * 4733446 * 2
def baseEnd_4733446 : Nat := 2430532950101992604456285

theorem tailTrace_4733446 : CollatzResearch.WordTrace tailWord_4733446 prefixEnd_4733446 2430532950101992604456285 := by
  unfold tailWord_4733446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395092462798157033163881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115095305873027350040829461 5395092462798157033163881)
  ·
    refine ⟨4046319347098617774872911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5395092462798157033163881 4046319347098617774872911)
    ·
      refine ⟨6069479020647926662309367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046319347098617774872911 6069479020647926662309367)
      ·
        refine ⟨9104218530971889993464051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069479020647926662309367 9104218530971889993464051)
        ·
          refine ⟨13656327796457834990196077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104218530971889993464051 13656327796457834990196077)
          ·
            refine ⟨5121122923671688121323529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13656327796457834990196077 5121122923671688121323529)
            ·
              refine ⟨3840842192753766090992647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121122923671688121323529 3840842192753766090992647)
              ·
                refine ⟨5761263289130649136488971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840842192753766090992647 5761263289130649136488971)
                ·
                  refine ⟨8641894933695973704733457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761263289130649136488971 8641894933695973704733457)
                  ·
                    refine ⟨6481421200271980278550093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8641894933695973704733457 6481421200271980278550093)
                    ·
                      refine ⟨2430532950101992604456285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481421200271980278550093 2430532950101992604456285)
                      ·
                        rfl

theorem cell23_4733446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4733446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733446 prefixEnd_4733446 := by exact prefixLift 4733446
  have htrace : WordTrace (prefixWord ++ tailWord_4733446) baseStart_4733446 baseEnd_4733446 := by
    simpa [prefixWord, tailWord_4733446, baseEnd_4733446] using wordTrace_append hprefix tailTrace_4733446
  have hstable : (prefixWord ++ tailWord_4733446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733446).length < 2 ^ (prefixWord ++ tailWord_4733446).sum := by decide
  have hdescent : baseEnd_4733446 < baseStart_4733446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733448 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_4733448 : Nat := 118140960795 + 4733448 * 2 ^ 59
def prefixEnd_4733448 : Nat := 4983230072969 + 3 ^ 40 * 4733448 * 2
def baseEnd_4733448 : Nat := 2430533977063301596631275

theorem tailTrace_4733448 : CollatzResearch.WordTrace tailWord_4733448 prefixEnd_4733448 2430533977063301596631275 := by
  unfold tailWord_4733448
  simp only [CollatzResearch.WordTrace]
  refine ⟨86321515877766889701408499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115095354503689186268544665 86321515877766889701408499)
  ·
    refine ⟨129482273816650334552112749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86321515877766889701408499 129482273816650334552112749)
    ·
      refine ⟨48555852681243875457042281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129482273816650334552112749 48555852681243875457042281)
      ·
        refine ⟨36416889510932906592781711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48555852681243875457042281 36416889510932906592781711)
        ·
          refine ⟨54625334266399359889172567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36416889510932906592781711 54625334266399359889172567)
          ·
            refine ⟨81938001399599039833758851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54625334266399359889172567 81938001399599039833758851)
            ·
              refine ⟨122907002099398559750638277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81938001399599039833758851 122907002099398559750638277)
              ·
                refine ⟨23045062893637229953244677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122907002099398559750638277 23045062893637229953244677)
                ·
                  refine ⟨4320949292556980616233377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23045062893637229953244677 4320949292556980616233377)
                  ·
                    refine ⟨3240711969417735462175033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4320949292556980616233377 3240711969417735462175033)
                    ·
                      refine ⟨2430533977063301596631275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240711969417735462175033 2430533977063301596631275)
                      ·
                        rfl

theorem cell23_4733448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_4733448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733448 prefixEnd_4733448 := by exact prefixLift 4733448
  have htrace : WordTrace (prefixWord ++ tailWord_4733448) baseStart_4733448 baseEnd_4733448 := by
    simpa [prefixWord, tailWord_4733448, baseEnd_4733448] using wordTrace_append hprefix tailTrace_4733448
  have hstable : (prefixWord ++ tailWord_4733448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733448).length < 2 ^ (prefixWord ++ tailWord_4733448).sum := by decide
  have hdescent : baseEnd_4733448 < baseStart_4733448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733452 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_4733452 : Nat := 118140960795 + 4733452 * 2 ^ 59
def prefixEnd_4733452 : Nat := 4983230072969 + 3 ^ 40 * 4733452 * 2
def baseEnd_4733452 : Nat := 2430536030985919580981257

theorem tailTrace_4733452 : CollatzResearch.WordTrace tailWord_4733452 prefixEnd_4733452 2430536030985919580981257 := by
  unfold tailWord_4733452
  simp only [CollatzResearch.WordTrace]
  refine ⟨86321588823759644042981305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115095451765012858723975073 86321588823759644042981305)
  ·
    refine ⟨64741191617819733032235979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86321588823759644042981305 64741191617819733032235979)
    ·
      refine ⟨97111787426729599548353969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64741191617819733032235979 97111787426729599548353969)
      ·
        refine ⟨72833840570047199661265477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97111787426729599548353969 72833840570047199661265477)
        ·
          refine ⟨13656345106883849936487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72833840570047199661265477 13656345106883849936487277)
          ·
            refine ⟨5121129415081443726182729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13656345106883849936487277 5121129415081443726182729)
            ·
              refine ⟨3840847061311082794637047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121129415081443726182729 3840847061311082794637047)
              ·
                refine ⟨5761270591966624191955571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840847061311082794637047 5761270591966624191955571)
                ·
                  refine ⟨8641905887949936287933357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761270591966624191955571 8641905887949936287933357)
                  ·
                    refine ⟨3240714707981226107975009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8641905887949936287933357 3240714707981226107975009)
                    ·
                      refine ⟨2430536030985919580981257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240714707981226107975009 2430536030985919580981257)
                      ·
                        rfl

theorem cell23_4733452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_4733452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733452 prefixEnd_4733452 := by exact prefixLift 4733452
  have htrace : WordTrace (prefixWord ++ tailWord_4733452) baseStart_4733452 baseEnd_4733452 := by
    simpa [prefixWord, tailWord_4733452, baseEnd_4733452] using wordTrace_append hprefix tailTrace_4733452
  have hstable : (prefixWord ++ tailWord_4733452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733452).length < 2 ^ (prefixWord ++ tailWord_4733452).sum := by decide
  have hdescent : baseEnd_4733452 < baseStart_4733452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733501 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4733501 : Nat := 118140960795 + 4733501 * 2 ^ 59
def prefixEnd_4733501 : Nat := 4983230072969 + 3 ^ 40 * 4733501 * 2
def baseEnd_4733501 : Nat := 810187063845996629756177

theorem tailTrace_4733501 : CollatzResearch.WordTrace tailWord_4733501 prefixEnd_4733501 810187063845996629756177 := by
  unfold tailWord_4733501
  simp only [CollatzResearch.WordTrace]
  refine ⟨172644964824341769454496357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115096643216227846302997571 172644964824341769454496357)
  ·
    refine ⟨32370930904564081772718067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172644964824341769454496357 32370930904564081772718067)
    ·
      refine ⟨48556396356846122659077101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32370930904564081772718067 48556396356846122659077101)
      ·
        refine ⟨18208648633817295997153913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48556396356846122659077101 18208648633817295997153913)
        ·
          refine ⟨13656486475362971997865435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18208648633817295997153913 13656486475362971997865435)
          ·
            refine ⟨20484729713044457996798153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656486475362971997865435 20484729713044457996798153)
            ·
              refine ⟨15363547284783343497598615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20484729713044457996798153 15363547284783343497598615)
              ·
                refine ⟨23045320927175015246397923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15363547284783343497598615 23045320927175015246397923)
                ·
                  refine ⟨34567981390762522869596885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23045320927175015246397923 34567981390762522869596885)
                  ·
                    refine ⟨810187063845996629756177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34567981390762522869596885 810187063845996629756177)
                    ·
                      rfl

theorem cell23_4733501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4733501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733501 prefixEnd_4733501 := by exact prefixLift 4733501
  have htrace : WordTrace (prefixWord ++ tailWord_4733501) baseStart_4733501 baseEnd_4733501 := by
    simpa [prefixWord, tailWord_4733501, baseEnd_4733501] using wordTrace_append hprefix tailTrace_4733501
  have hstable : (prefixWord ++ tailWord_4733501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733501).length < 2 ^ (prefixWord ++ tailWord_4733501).sum := by decide
  have hdescent : baseEnd_4733501 < baseStart_4733501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733505 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 5]
def baseStart_4733505 : Nat := 118140960795 + 4733505 * 2 ^ 59
def prefixEnd_4733505 : Nat := 4983230072969 + 3 ^ 40 * 4733505 * 2
def baseEnd_4733505 : Nat := 270062582828956430402057

theorem tailTrace_4733505 : CollatzResearch.WordTrace tailWord_4733505 prefixEnd_4733505 270062582828956430402057 := by
  unfold tailWord_4733505
  simp only [CollatzResearch.WordTrace]
  refine ⟨172645110716327278137641969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115096740477551518758427979 172645110716327278137641969)
  ·
    refine ⟨129483833037245458603231477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172645110716327278137641969 129483833037245458603231477)
    ·
      refine ⟨12139109347241761744052951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129483833037245458603231477 12139109347241761744052951)
      ·
        refine ⟨18208664020862642616079427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12139109347241761744052951 18208664020862642616079427)
        ·
          refine ⟨27312996031293963924119141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208664020862642616079427 27312996031293963924119141)
          ·
            refine ⟨5121186755867618235772339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27312996031293963924119141 5121186755867618235772339)
            ·
              refine ⟨7681780133801427353658509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121186755867618235772339 7681780133801427353658509)
              ·
                refine ⟨2880667550175535257621941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7681780133801427353658509 2880667550175535257621941)
                ·
                  refine ⟨270062582828956430402057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880667550175535257621941 270062582828956430402057)
                  ·
                    rfl

theorem cell23_4733505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 5].length) (baseStart_4733505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733505 prefixEnd_4733505 := by exact prefixLift 4733505
  have htrace : WordTrace (prefixWord ++ tailWord_4733505) baseStart_4733505 baseEnd_4733505 := by
    simpa [prefixWord, tailWord_4733505, baseEnd_4733505] using wordTrace_append hprefix tailTrace_4733505
  have hstable : (prefixWord ++ tailWord_4733505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733505).length < 2 ^ (prefixWord ++ tailWord_4733505).sum := by decide
  have hdescent : baseEnd_4733505 < baseStart_4733505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733521 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_4733521 : Nat := 118140960795 + 4733521 * 2 ^ 59
def prefixEnd_4733521 : Nat := 4983230072969 + 3 ^ 40 * 4733521 * 2
def baseEnd_4733521 : Nat := 2430571461151079811018439

theorem tailTrace_4733521 : CollatzResearch.WordTrace tailWord_4733521 prefixEnd_4733521 2430571461151079811018439 := by
  unfold tailWord_4733521
  simp only [CollatzResearch.WordTrace]
  refine ⟨172645694284269312870224417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115097129522846208580149611 172645694284269312870224417)
  ·
    refine ⟨129484270713201984652668313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172645694284269312870224417 129484270713201984652668313)
    ·
      refine ⟨97113203034901488489501235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129484270713201984652668313 97113203034901488489501235)
      ·
        refine ⟨145669804552352232734251853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97113203034901488489501235 145669804552352232734251853)
        ·
          refine ⟨54626176707132087275344445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145669804552352232734251853 54626176707132087275344445)
          ·
            refine ⟨20484816265174532728254167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54626176707132087275344445 20484816265174532728254167)
            ·
              refine ⟨30727224397761799092381251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20484816265174532728254167 30727224397761799092381251)
              ·
                refine ⟨46090836596642698638571877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30727224397761799092381251 46090836596642698638571877)
                ·
                  refine ⟨8642031861870505994732227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46090836596642698638571877 8642031861870505994732227)
                  ·
                    refine ⟨12963047792805758992098341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8642031861870505994732227 12963047792805758992098341)
                    ·
                      refine ⟨2430571461151079811018439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12963047792805758992098341 2430571461151079811018439)
                      ·
                        rfl

theorem cell23_4733521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_4733521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733521 prefixEnd_4733521 := by exact prefixLift 4733521
  have htrace : WordTrace (prefixWord ++ tailWord_4733521) baseStart_4733521 baseEnd_4733521 := by
    simpa [prefixWord, tailWord_4733521, baseEnd_4733521] using wordTrace_append hprefix tailTrace_4733521
  have hstable : (prefixWord ++ tailWord_4733521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733521).length < 2 ^ (prefixWord ++ tailWord_4733521).sum := by decide
  have hdescent : baseEnd_4733521 < baseStart_4733521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733591 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 5, 5]
def baseStart_4733591 : Nat := 118140960795 + 4733591 * 2 ^ 59
def prefixEnd_4733591 : Nat := 4983230072969 + 3 ^ 40 * 4733591 * 2
def baseEnd_4733591 : Nat := 810202468265631512381039

theorem tailTrace_4733591 : CollatzResearch.WordTrace tailWord_4733591 prefixEnd_4733591 810202468265631512381039 := by
  unfold tailWord_4733591
  simp only [CollatzResearch.WordTrace]
  refine ⟨172648247394015714825272627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115098831596010476550181751 172648247394015714825272627)
  ·
    refine ⟨258972371091023572237908941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172648247394015714825272627 258972371091023572237908941)
    ·
      refine ⟨97114639159133839589215853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258972371091023572237908941 97114639159133839589215853)
      ·
        refine ⟨36417989684675189845955945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97114639159133839589215853 36417989684675189845955945)
        ·
          refine ⟨27313492263506392384466959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36417989684675189845955945 27313492263506392384466959)
          ·
            refine ⟨40970238395259588576700439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27313492263506392384466959 40970238395259588576700439)
            ·
              refine ⟨61455357592889382865050659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40970238395259588576700439 61455357592889382865050659)
              ·
                refine ⟨92183036389334074297575989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61455357592889382865050659 92183036389334074297575989)
                ·
                  refine ⟨8642159661500069465397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92183036389334074297575989 8642159661500069465397749)
                  ·
                    refine ⟨810202468265631512381039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8642159661500069465397749 810202468265631512381039)
                    ·
                      rfl

theorem cell23_4733591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_4733591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733591 prefixEnd_4733591 := by exact prefixLift 4733591
  have htrace : WordTrace (prefixWord ++ tailWord_4733591) baseStart_4733591 baseEnd_4733591 := by
    simpa [prefixWord, tailWord_4733591, baseEnd_4733591] using wordTrace_append hprefix tailTrace_4733591
  have hstable : (prefixWord ++ tailWord_4733591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733591).length < 2 ^ (prefixWord ++ tailWord_4733591).sum := by decide
  have hdescent : baseEnd_4733591 < baseStart_4733591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733615 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 2, 3, 2]
def baseStart_4733615 : Nat := 118140960795 + 4733615 * 2 ^ 59
def prefixEnd_4733615 : Nat := 4983230072969 + 3 ^ 40 * 4733615 * 2
def baseEnd_4733615 : Nat := 2430619728332602443243007

theorem tailTrace_4733615 : CollatzResearch.WordTrace tailWord_4733615 prefixEnd_4733615 2430619728332602443243007 := by
  unfold tailWord_4733615
  simp only [CollatzResearch.WordTrace]
  refine ⟨172649122745928766924146299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115099415163952511282764199 172649122745928766924146299)
  ·
    refine ⟨258973684118893150386219449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172649122745928766924146299 258973684118893150386219449)
    ·
      refine ⟨194230263089169862789664587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258973684118893150386219449 194230263089169862789664587)
      ·
        refine ⟨291345394633754794184496881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194230263089169862789664587 291345394633754794184496881)
        ·
          refine ⟨218509045975316095638372661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291345394633754794184496881 218509045975316095638372661)
          ·
            refine ⟨20485223060185883966097437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218509045975316095638372661 20485223060185883966097437)
            ·
              refine ⟨7681958647569706487286539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20485223060185883966097437 7681958647569706487286539)
              ·
                refine ⟨11522937971354559730929809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7681958647569706487286539 11522937971354559730929809)
                ·
                  refine ⟨8642203478515919798197357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11522937971354559730929809 8642203478515919798197357)
                  ·
                    refine ⟨3240826304443469924324009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8642203478515919798197357 3240826304443469924324009)
                    ·
                      refine ⟨2430619728332602443243007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240826304443469924324009 2430619728332602443243007)
                      ·
                        rfl

theorem cell23_4733615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3, 2].length) (baseStart_4733615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733615 prefixEnd_4733615 := by exact prefixLift 4733615
  have htrace : WordTrace (prefixWord ++ tailWord_4733615) baseStart_4733615 baseEnd_4733615 := by
    simpa [prefixWord, tailWord_4733615, baseEnd_4733615] using wordTrace_append hprefix tailTrace_4733615
  have hstable : (prefixWord ++ tailWord_4733615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733615).length < 2 ^ (prefixWord ++ tailWord_4733615).sum := by decide
  have hdescent : baseEnd_4733615 < baseStart_4733615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733665 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_4733665 : Nat := 118140960795 + 4733665 * 2 ^ 59
def prefixEnd_4733665 : Nat := 4983230072969 + 3 ^ 40 * 4733665 * 2
def baseEnd_4733665 : Nat := 2430645402365327247617777

theorem tailTrace_4733665 : CollatzResearch.WordTrace tailWord_4733665 prefixEnd_4733665 2430645402365327247617777 := by
  unfold tailWord_4733665
  simp only [CollatzResearch.WordTrace]
  refine ⟨172650946395747625463466449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115100630930498416975644299 172650946395747625463466449)
  ·
    refine ⟨129488209796810719097599837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172650946395747625463466449 129488209796810719097599837)
    ·
      refine ⟨48558078673804019661599939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129488209796810719097599837 48558078673804019661599939)
      ·
        refine ⟨72837118010706029492399909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48558078673804019661599939 72837118010706029492399909)
        ·
          refine ⟨13656959627007380529824983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72837118010706029492399909 13656959627007380529824983)
          ·
            refine ⟨20485439440511070794737475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656959627007380529824983 20485439440511070794737475)
            ·
              refine ⟨30728159160766606192106213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20485439440511070794737475 30728159160766606192106213)
              ·
                refine ⟨5761529842643738661019915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30728159160766606192106213 5761529842643738661019915)
                ·
                  refine ⟨8642294763965607991529873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761529842643738661019915 8642294763965607991529873)
                  ·
                    refine ⟨6481721072974205993647405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8642294763965607991529873 6481721072974205993647405)
                    ·
                      refine ⟨2430645402365327247617777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481721072974205993647405 2430645402365327247617777)
                      ·
                        rfl

theorem cell23_4733665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_4733665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733665 prefixEnd_4733665 := by exact prefixLift 4733665
  have htrace : WordTrace (prefixWord ++ tailWord_4733665) baseStart_4733665 baseEnd_4733665 := by
    simpa [prefixWord, tailWord_4733665, baseEnd_4733665] using wordTrace_append hprefix tailTrace_4733665
  have hstable : (prefixWord ++ tailWord_4733665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733665).length < 2 ^ (prefixWord ++ tailWord_4733665).sum := by decide
  have hdescent : baseEnd_4733665 < baseStart_4733665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733668 : List Nat := [2, 3, 1, 1, 1, 4, 4, 7]
def baseStart_4733668 : Nat := 118140960795 + 4733668 * 2 ^ 59
def prefixEnd_4733668 : Nat := 4983230072969 + 3 ^ 40 * 4733668 * 2
def baseEnd_4733668 : Nat := 90023960844714471699269

theorem tailTrace_4733668 : CollatzResearch.WordTrace tailWord_4733668 prefixEnd_4733668 90023960844714471699269 := by
  unfold tailWord_4733668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86325527907368378487912829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115100703876491171317217105 86325527907368378487912829)
  ·
    refine ⟨32372072965263141932967311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86325527907368378487912829 32372072965263141932967311)
    ·
      refine ⟨48558109447894712899450967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32372072965263141932967311 48558109447894712899450967)
      ·
        refine ⟨72837164171842069349176451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48558109447894712899450967 72837164171842069349176451)
        ·
          refine ⟨109255746257763104023764677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72837164171842069349176451 109255746257763104023764677)
          ·
            refine ⟨20485452423330582004455877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109255746257763104023764677 20485452423330582004455877)
            ·
              refine ⟨3841022329374484125835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20485452423330582004455877 3841022329374484125835477)
              ·
                refine ⟨90023960844714471699269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3841022329374484125835477 90023960844714471699269)
                ·
                  rfl

theorem cell23_4733668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 7].length) (baseStart_4733668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733668 prefixEnd_4733668 := by exact prefixLift 4733668
  have htrace : WordTrace (prefixWord ++ tailWord_4733668) baseStart_4733668 baseEnd_4733668 := by
    simpa [prefixWord, tailWord_4733668, baseEnd_4733668] using wordTrace_append hprefix tailTrace_4733668
  have hstable : (prefixWord ++ tailWord_4733668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733668).length < 2 ^ (prefixWord ++ tailWord_4733668).sum := by decide
  have hdescent : baseEnd_4733668 < baseStart_4733668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733679 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 1, 2, 2]
def baseStart_4733679 : Nat := 118140960795 + 4733679 * 2 ^ 59
def prefixEnd_4733679 : Nat := 4983230072969 + 3 ^ 40 * 4733679 * 2
def baseEnd_4733679 : Nat := 2430652591094490192842713

theorem tailTrace_4733679 : CollatzResearch.WordTrace tailWord_4733679 prefixEnd_4733679 2430652591094490192842713 := by
  unfold tailWord_4733679
  simp only [CollatzResearch.WordTrace]
  refine ⟨172651457017696905854476091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115100971345131270569650727 172651457017696905854476091)
  ·
    refine ⟨258977185526545358781714137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172651457017696905854476091 258977185526545358781714137)
    ·
      refine ⟨194232889144909019086285603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258977185526545358781714137 194232889144909019086285603)
      ·
        refine ⟨291349333717363528629428405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194232889144909019086285603 291349333717363528629428405)
        ·
          refine ⟨27314000036002830809008913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 291349333717363528629428405 27314000036002830809008913)
          ·
            refine ⟨20485500027002123106756685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27314000036002830809008913 20485500027002123106756685)
            ·
              refine ⟨7682062510125796165033757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20485500027002123106756685 7682062510125796165033757)
              ·
                refine ⟨2880773441297173561887659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7682062510125796165033757 2880773441297173561887659)
                ·
                  refine ⟨4321160161945760342831489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880773441297173561887659 4321160161945760342831489)
                  ·
                    refine ⟨3240870121459320257123617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4321160161945760342831489 3240870121459320257123617)
                    ·
                      refine ⟨2430652591094490192842713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3240870121459320257123617 2430652591094490192842713)
                      ·
                        rfl

theorem cell23_4733679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 2, 2].length) (baseStart_4733679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733679 prefixEnd_4733679 := by exact prefixLift 4733679
  have htrace : WordTrace (prefixWord ++ tailWord_4733679) baseStart_4733679 baseEnd_4733679 := by
    simpa [prefixWord, tailWord_4733679, baseEnd_4733679] using wordTrace_append hprefix tailTrace_4733679
  have hstable : (prefixWord ++ tailWord_4733679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733679).length < 2 ^ (prefixWord ++ tailWord_4733679).sum := by decide
  have hdescent : baseEnd_4733679 < baseStart_4733679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733695 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_4733695 : Nat := 118140960795 + 4733695 * 2 ^ 59
def prefixEnd_4733695 : Nat := 4983230072969 + 3 ^ 40 * 4733695 * 2
def baseEnd_4733695 : Nat := 2430660806784962130242639

theorem tailTrace_4733695 : CollatzResearch.WordTrace tailWord_4733695 prefixEnd_4733695 2430660806784962130242639 := by
  unfold tailWord_4733695
  simp only [CollatzResearch.WordTrace]
  refine ⟨172652040585638940587058539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115101360390425960391372359 172652040585638940587058539)
  ·
    refine ⟨258978060878458410880587809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172652040585638940587058539 258978060878458410880587809)
    ·
      refine ⟨194233545658843808160440857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258978060878458410880587809 194233545658843808160440857)
      ·
        refine ⟨145675159244132856120330643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194233545658843808160440857 145675159244132856120330643)
        ·
          refine ⟨218512738866199284180495965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145675159244132856120330643 218512738866199284180495965)
          ·
            refine ⟨81942277074824731567685987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218512738866199284180495965 81942277074824731567685987)
            ·
              refine ⟨122913415612237097351528981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81942277074824731567685987 122913415612237097351528981)
              ·
                refine ⟨5761566356823613938352921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122913415612237097351528981 5761566356823613938352921)
                ·
                  refine ⟨4321174767617710453764691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761566356823613938352921 4321174767617710453764691)
                  ·
                    refine ⟨6481762151426565680647037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4321174767617710453764691 6481762151426565680647037)
                    ·
                      refine ⟨2430660806784962130242639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481762151426565680647037 2430660806784962130242639)
                      ·
                        rfl

theorem cell23_4733695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_4733695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733695 prefixEnd_4733695 := by exact prefixLift 4733695
  have htrace : WordTrace (prefixWord ++ tailWord_4733695) baseStart_4733695 baseEnd_4733695 := by
    simpa [prefixWord, tailWord_4733695, baseEnd_4733695] using wordTrace_append hprefix tailTrace_4733695
  have hstable : (prefixWord ++ tailWord_4733695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733695).length < 2 ^ (prefixWord ++ tailWord_4733695).sum := by decide
  have hdescent : baseEnd_4733695 < baseStart_4733695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733711 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 8]
def baseStart_4733711 : Nat := 118140960795 + 4733711 * 2 ^ 59
def prefixEnd_4733711 : Nat := 4983230072969 + 3 ^ 40 * 4733711 * 2
def baseEnd_4733711 : Nat := 810223007491811355880855

theorem tailTrace_4733711 : CollatzResearch.WordTrace tailWord_4733711 prefixEnd_4733711 810223007491811355880855 := by
  unfold tailWord_4733711
  simp only [CollatzResearch.WordTrace]
  refine ⟨172652624153580975319640987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115101749435720650213093991 172652624153580975319640987)
  ·
    refine ⟨258978936230371462979461481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172652624153580975319640987 258978936230371462979461481)
    ·
      refine ⟨194234202172778597234596111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258978936230371462979461481 194234202172778597234596111)
      ·
        refine ⟨291351303259167895851894167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194234202172778597234596111 291351303259167895851894167)
        ·
          refine ⟨437026954888751843777841251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291351303259167895851894167 437026954888751843777841251)
          ·
            refine ⟨655540432333127765666761877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437026954888751843777841251 655540432333127765666761877)
            ·
              refine ⟨30728457765615364015629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 655540432333127765666761877 30728457765615364015629463)
              ·
                refine ⟨46092686648423046023444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30728457765615364015629463 46092686648423046023444195)
                ·
                  refine ⟨69139029972634569035166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46092686648423046023444195 69139029972634569035166293)
                  ·
                    refine ⟨810223007491811355880855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69139029972634569035166293 810223007491811355880855)
                    ·
                      rfl

theorem cell23_4733711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_4733711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733711 prefixEnd_4733711 := by exact prefixLift 4733711
  have htrace : WordTrace (prefixWord ++ tailWord_4733711) baseStart_4733711 baseEnd_4733711 := by
    simpa [prefixWord, tailWord_4733711, baseEnd_4733711] using wordTrace_append hprefix tailTrace_4733711
  have hstable : (prefixWord ++ tailWord_4733711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733711).length < 2 ^ (prefixWord ++ tailWord_4733711).sum := by decide
  have hdescent : baseEnd_4733711 < baseStart_4733711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733835 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 3, 4]
def baseStart_4733835 : Nat := 118140960795 + 4733835 * 2 ^ 59
def prefixEnd_4733835 : Nat := 4983230072969 + 3 ^ 40 * 4733835 * 2
def baseEnd_4733835 : Nat := 810244231358863860830665

theorem tailTrace_4733835 : CollatzResearch.WordTrace tailWord_4733835 prefixEnd_4733835 810244231358863860830665 := by
  unfold tailWord_4733835
  simp only [CollatzResearch.WordTrace]
  refine ⟨172657146805131744497154959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115104764536754496331436639 172657146805131744497154959)
  ·
    refine ⟨258985720207697616745732439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172657146805131744497154959 258985720207697616745732439)
    ·
      refine ⟨388478580311546425118598659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258985720207697616745732439 388478580311546425118598659)
      ·
        refine ⟨582717870467319637677897989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388478580311546425118598659 582717870467319637677897989)
        ·
          refine ⟨109259600712622432064605873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 582717870467319637677897989 109259600712622432064605873)
          ·
            refine ⟨81944700534466824048454405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109259600712622432064605873 81944700534466824048454405)
            ·
              refine ⟨15364631350212529509085201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81944700534466824048454405 15364631350212529509085201)
              ·
                refine ⟨11523473512659397131813901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15364631350212529509085201 11523473512659397131813901)
                ·
                  refine ⟨4321302567247273924430213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11523473512659397131813901 4321302567247273924430213)
                  ·
                    refine ⟨810244231358863860830665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4321302567247273924430213 810244231358863860830665)
                    ·
                      rfl

theorem cell23_4733835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 4].length) (baseStart_4733835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733835 prefixEnd_4733835 := by exact prefixLift 4733835
  have htrace : WordTrace (prefixWord ++ tailWord_4733835) baseStart_4733835 baseEnd_4733835 := by
    simpa [prefixWord, tailWord_4733835, baseEnd_4733835] using wordTrace_append hprefix tailTrace_4733835
  have hstable : (prefixWord ++ tailWord_4733835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733835).length < 2 ^ (prefixWord ++ tailWord_4733835).sum := by decide
  have hdescent : baseEnd_4733835 < baseStart_4733835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733845 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_4733845 : Nat := 118140960795 + 4733845 * 2 ^ 59
def prefixEnd_4733845 : Nat := 4983230072969 + 3 ^ 40 * 4733845 * 2
def baseEnd_4733845 : Nat := 2430737828883136543366949

theorem tailTrace_4733845 : CollatzResearch.WordTrace tailWord_4733845 prefixEnd_4733845 2430737828883136543366949 := by
  unfold tailWord_4733845
  simp only [CollatzResearch.WordTrace]
  refine ⟨172657511535095516205018989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115105007690063677470012659 172657511535095516205018989)
  ·
    refine ⟨64746566825660818576882121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172657511535095516205018989 64746566825660818576882121)
    ·
      refine ⟨48559925119245613932661591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64746566825660818576882121 48559925119245613932661591)
      ·
        refine ⟨72839887678868420898992387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48559925119245613932661591 72839887678868420898992387)
        ·
          refine ⟨109259831518302631348488581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72839887678868420898992387 109259831518302631348488581)
          ·
            refine ⟨20486218409681743377841609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109259831518302631348488581 20486218409681743377841609)
            ·
              refine ⟨15364663807261307533381207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20486218409681743377841609 15364663807261307533381207)
              ·
                refine ⟨23046995710891961300071811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15364663807261307533381207 23046995710891961300071811)
                ·
                  refine ⟨34570493566337941950107717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23046995710891961300071811 34570493566337941950107717)
                  ·
                    refine ⟨6481967543688364115645197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34570493566337941950107717 6481967543688364115645197)
                    ·
                      refine ⟨2430737828883136543366949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6481967543688364115645197 2430737828883136543366949)
                      ·
                        rfl

theorem cell23_4733845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_4733845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733845 prefixEnd_4733845 := by exact prefixLift 4733845
  have htrace : WordTrace (prefixWord ++ tailWord_4733845) baseStart_4733845 baseEnd_4733845 := by
    simpa [prefixWord, tailWord_4733845, baseEnd_4733845] using wordTrace_append hprefix tailTrace_4733845
  have hstable : (prefixWord ++ tailWord_4733845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733845).length < 2 ^ (prefixWord ++ tailWord_4733845).sum := by decide
  have hdescent : baseEnd_4733845 < baseStart_4733845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733942 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_4733942 : Nat := 118140960795 + 4733942 * 2 ^ 59
def prefixEnd_4733942 : Nat := 4983230072969 + 3 ^ 40 * 4733942 * 2
def baseEnd_4733942 : Nat := 810262545502207554618001

theorem tailTrace_4733942 : CollatzResearch.WordTrace tailWord_4733942 prefixEnd_4733942 810262545502207554618001 := by
  unfold tailWord_4733942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791315588484006360706255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115107366277162734514200053 10791315588484006360706255)
  ·
    refine ⟨16186973382726009541059383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10791315588484006360706255 16186973382726009541059383)
    ·
      refine ⟨24280460074089014311589075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186973382726009541059383 24280460074089014311589075)
      ·
        refine ⟨36420690111133521467383613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24280460074089014311589075 36420690111133521467383613)
        ·
          refine ⟨13657758791675070550268855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36420690111133521467383613 13657758791675070550268855)
          ·
            refine ⟨20486638187512605825403283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13657758791675070550268855 20486638187512605825403283)
            ·
              refine ⟨30729957281268908738104925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20486638187512605825403283 30729957281268908738104925)
              ·
                refine ⟨11523733980475840776789347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30729957281268908738104925 11523733980475840776789347)
                ·
                  refine ⟨17285600970713761165184021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11523733980475840776789347 17285600970713761165184021)
                  ·
                    refine ⟨810262545502207554618001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17285600970713761165184021 810262545502207554618001)
                    ·
                      rfl

theorem cell23_4733942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_4733942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733942 prefixEnd_4733942 := by exact prefixLift 4733942
  have htrace : WordTrace (prefixWord ++ tailWord_4733942) baseStart_4733942 baseEnd_4733942 := by
    simpa [prefixWord, tailWord_4733942, baseEnd_4733942] using wordTrace_append hprefix tailTrace_4733942
  have hstable : (prefixWord ++ tailWord_4733942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733942).length < 2 ^ (prefixWord ++ tailWord_4733942).sum := by decide
  have hdescent : baseEnd_4733942 < baseStart_4733942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733962 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4733962 : Nat := 118140960795 + 4733962 * 2 ^ 59
def prefixEnd_4733962 : Nat := 4983230072969 + 3 ^ 40 * 4733962 * 2
def baseEnd_4733962 : Nat := 2430797906119712585603911

theorem tailTrace_4733962 : CollatzResearch.WordTrace tailWord_4733962 prefixEnd_4733962 2430797906119712585603911 := by
  unfold tailWord_4733962
  simp only [CollatzResearch.WordTrace]
  refine ⟨43165444718917911296757035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115107852583781096791352093 43165444718917911296757035)
  ·
    refine ⟨64748167078376866945135553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43165444718917911296757035 64748167078376866945135553)
    ·
      refine ⟨48561125308782650208851665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64748167078376866945135553 48561125308782650208851665)
      ·
        refine ⟨36420843981586987656638749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48561125308782650208851665 36420843981586987656638749)
        ·
          refine ⟨13657816493095120371239531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36420843981586987656638749 13657816493095120371239531)
          ·
            refine ⟨20486724739642680556859297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13657816493095120371239531 20486724739642680556859297)
            ·
              refine ⟨15365043554732010417644473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20486724739642680556859297 15365043554732010417644473)
              ·
                refine ⟨11523782666049007813233355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15365043554732010417644473 11523782666049007813233355)
                ·
                  refine ⟨17285673999073511719850033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11523782666049007813233355 17285673999073511719850033)
                  ·
                    refine ⟨12964255499305133789887525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17285673999073511719850033 12964255499305133789887525)
                    ·
                      refine ⟨2430797906119712585603911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12964255499305133789887525 2430797906119712585603911)
                      ·
                        rfl

theorem cell23_4733962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4733962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733962 prefixEnd_4733962 := by exact prefixLift 4733962
  have htrace : WordTrace (prefixWord ++ tailWord_4733962) baseStart_4733962 baseEnd_4733962 := by
    simpa [prefixWord, tailWord_4733962, baseEnd_4733962] using wordTrace_append hprefix tailTrace_4733962
  have hstable : (prefixWord ++ tailWord_4733962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733962).length < 2 ^ (prefixWord ++ tailWord_4733962).sum := by decide
  have hdescent : baseEnd_4733962 < baseStart_4733962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733966 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4733966 : Nat := 118140960795 + 4733966 * 2 ^ 59
def prefixEnd_4733966 : Nat := 4983230072969 + 3 ^ 40 * 4733966 * 2
def baseEnd_4733966 : Nat := 2430799960042330569953893

theorem tailTrace_4733966 : CollatzResearch.WordTrace tailWord_4733966 prefixEnd_4733966 2430799960042330569953893 := by
  unfold tailWord_4733966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21582740595957144233771719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115107949845104769246782501 21582740595957144233771719)
  ·
    refine ⟨32374110893935716350657579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21582740595957144233771719 32374110893935716350657579)
    ·
      refine ⟨48561166340903574525986369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32374110893935716350657579 48561166340903574525986369)
      ·
        refine ⟨36420874755677680894489777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48561166340903574525986369 36420874755677680894489777)
        ·
          refine ⟨27315656066758260670867333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36420874755677680894489777 27315656066758260670867333)
          ·
            refine ⟨5121685512517173875787625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27315656066758260670867333 5121685512517173875787625)
            ·
              refine ⟨3841264134387880406840719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121685512517173875787625 3841264134387880406840719)
              ·
                refine ⟨5761896201581820610261079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841264134387880406840719 5761896201581820610261079)
                ·
                  refine ⟨8642844302372730915391619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761896201581820610261079 8642844302372730915391619)
                  ·
                    refine ⟨12964266453559096373087429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8642844302372730915391619 12964266453559096373087429)
                    ·
                      refine ⟨2430799960042330569953893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12964266453559096373087429 2430799960042330569953893)
                      ·
                        rfl

theorem cell23_4733966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4733966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4733966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4733966 prefixEnd_4733966 := by exact prefixLift 4733966
  have htrace : WordTrace (prefixWord ++ tailWord_4733966) baseStart_4733966 baseEnd_4733966 := by
    simpa [prefixWord, tailWord_4733966, baseEnd_4733966] using wordTrace_append hprefix tailTrace_4733966
  have hstable : (prefixWord ++ tailWord_4733966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733966).length < 2 ^ (prefixWord ++ tailWord_4733966).sum := by decide
  have hdescent : baseEnd_4733966 < baseStart_4733966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734017 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4734017 : Nat := 118140960795 + 4734017 * 2 ^ 59
def prefixEnd_4734017 : Nat := 4983230072969 + 3 ^ 40 * 4734017 * 2
def baseEnd_4734017 : Nat := 2430826147555709870416159

theorem tailTrace_4734017 : CollatzResearch.WordTrace tailWord_4734017 prefixEnd_4734017 2430826147555709870416159 := by
  unfold tailWord_4734017
  simp only [CollatzResearch.WordTrace]
  refine ⟨172663784890472389580280305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115109189926981593053520203 172663784890472389580280305)
  ·
    refine ⟨129497838667854292185210229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172663784890472389580280305 129497838667854292185210229)
    ·
      refine ⟨12140422375111339892363459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129497838667854292185210229 12140422375111339892363459)
      ·
        refine ⟨18210633562667009838545189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12140422375111339892363459 18210633562667009838545189)
        ·
          refine ⟨3414493793000064344727223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18210633562667009838545189 3414493793000064344727223)
          ·
            refine ⟨5121740689500096517090835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414493793000064344727223 5121740689500096517090835)
            ·
              refine ⟨7682611034250144775636253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121740689500096517090835 7682611034250144775636253)
              ·
                refine ⟨2880979137843804290863595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7682611034250144775636253 2880979137843804290863595)
                ·
                  refine ⟨4321468706765706436295393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880979137843804290863595 4321468706765706436295393)
                  ·
                    refine ⟨3241101530074279827221545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4321468706765706436295393 3241101530074279827221545)
                    ·
                      refine ⟨2430826147555709870416159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241101530074279827221545 2430826147555709870416159)
                      ·
                        rfl

theorem cell23_4734017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4734017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734017 prefixEnd_4734017 := by exact prefixLift 4734017
  have htrace : WordTrace (prefixWord ++ tailWord_4734017) baseStart_4734017 baseEnd_4734017 := by
    simpa [prefixWord, tailWord_4734017, baseEnd_4734017] using wordTrace_append hprefix tailTrace_4734017
  have hstable : (prefixWord ++ tailWord_4734017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734017).length < 2 ^ (prefixWord ++ tailWord_4734017).sum := by decide
  have hdescent : baseEnd_4734017 < baseStart_4734017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734050 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4734050 : Nat := 118140960795 + 4734050 * 2 ^ 59
def prefixEnd_4734050 : Nat := 4983230072969 + 3 ^ 40 * 4734050 * 2
def baseEnd_4734050 : Nat := 2430843092417308241303507

theorem tailTrace_4734050 : CollatzResearch.WordTrace tailWord_4734050 prefixEnd_4734050 2430843092417308241303507 := by
  unfold tailWord_4734050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43166247124838209054057901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115109992332901890810821069 43166247124838209054057901)
  ·
    refine ⟨16187342671814328395271713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43166247124838209054057901 16187342671814328395271713)
    ·
      refine ⟨12140507003860746296453785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16187342671814328395271713 12140507003860746296453785)
      ·
        refine ⟨9105380252895559722340339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12140507003860746296453785 9105380252895559722340339)
        ·
          refine ⟨13658070379343339583510509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105380252895559722340339 13658070379343339583510509)
          ·
            refine ⟨5121776392253752343816441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13658070379343339583510509 5121776392253752343816441)
            ·
              refine ⟨3841332294190314257862331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121776392253752343816441 3841332294190314257862331)
              ·
                refine ⟨5761998441285471386793497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841332294190314257862331 5761998441285471386793497)
                ·
                  refine ⟨4321498830964103540095123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761998441285471386793497 4321498830964103540095123)
                  ·
                    refine ⟨6482248246446155310142685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4321498830964103540095123 6482248246446155310142685)
                    ·
                      refine ⟨2430843092417308241303507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6482248246446155310142685 2430843092417308241303507)
                      ·
                        rfl

theorem cell23_4734050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4734050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734050 prefixEnd_4734050 := by exact prefixLift 4734050
  have htrace : WordTrace (prefixWord ++ tailWord_4734050) baseStart_4734050 baseEnd_4734050 := by
    simpa [prefixWord, tailWord_4734050, baseEnd_4734050] using wordTrace_append hprefix tailTrace_4734050
  have hstable : (prefixWord ++ tailWord_4734050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734050).length < 2 ^ (prefixWord ++ tailWord_4734050).sum := by decide
  have hdescent : baseEnd_4734050 < baseStart_4734050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734075 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 7]
def baseStart_4734075 : Nat := 118140960795 + 4734075 * 2 ^ 59
def prefixEnd_4734075 : Nat := 4983230072969 + 3 ^ 40 * 4734075 * 2
def baseEnd_4734075 : Nat := 810285309811223547830297

theorem tailTrace_4734075 : CollatzResearch.WordTrace tailWord_4734075 prefixEnd_4734075 810285309811223547830297 := by
  unfold tailWord_4734075
  simp only [CollatzResearch.WordTrace]
  refine ⟨172665900324262265485891679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115110600216174843657261119 172665900324262265485891679)
  ·
    refine ⟨258998850486393398228837519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172665900324262265485891679 258998850486393398228837519)
    ·
      refine ⟨388498275729590097343256279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258998850486393398228837519 388498275729590097343256279)
      ·
        refine ⟨582747413594385146014884419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388498275729590097343256279 582747413594385146014884419)
        ·
          refine ⟨874121120391577719022326629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582747413594385146014884419 874121120391577719022326629)
          ·
            refine ⟨163897710073420822316686243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 874121120391577719022326629 163897710073420822316686243)
            ·
              refine ⟨245846565110131233475029365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163897710073420822316686243 245846565110131233475029365)
              ·
                refine ⟨23048115479074803138284003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 245846565110131233475029365 23048115479074803138284003)
                ·
                  refine ⟨34572173218612204707426005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23048115479074803138284003 34572173218612204707426005)
                  ·
                    refine ⟨810285309811223547830297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34572173218612204707426005 810285309811223547830297)
                    ·
                      rfl

theorem cell23_4734075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_4734075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734075 prefixEnd_4734075 := by exact prefixLift 4734075
  have htrace : WordTrace (prefixWord ++ tailWord_4734075) baseStart_4734075 baseEnd_4734075 := by
    simpa [prefixWord, tailWord_4734075, baseEnd_4734075] using wordTrace_append hprefix tailTrace_4734075
  have hstable : (prefixWord ++ tailWord_4734075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734075).length < 2 ^ (prefixWord ++ tailWord_4734075).sum := by decide
  have hdescent : baseEnd_4734075 < baseStart_4734075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734105 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_4734105 : Nat := 118140960795 + 4734105 * 2 ^ 59
def prefixEnd_4734105 : Nat := 4983230072969 + 3 ^ 40 * 4734105 * 2
def baseEnd_4734105 : Nat := 810290444617768508705251

theorem tailTrace_4734105 : CollatzResearch.WordTrace tailWord_4734105 prefixEnd_4734105 810290444617768508705251 := by
  unfold tailWord_4734105
  simp only [CollatzResearch.WordTrace]
  refine ⟨172666994514153580609483769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115111329676102387072989179 172666994514153580609483769)
  ·
    refine ⟨129500245885615185457112827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172666994514153580609483769 129500245885615185457112827)
    ·
      refine ⟨194250368828422778185669241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129500245885615185457112827 194250368828422778185669241)
      ·
        refine ⟨145687776621317083639251931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194250368828422778185669241 145687776621317083639251931)
        ·
          refine ⟨218531664931975625458877897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145687776621317083639251931 218531664931975625458877897)
          ·
            refine ⟨163898748698981719094158423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218531664931975625458877897 163898748698981719094158423)
            ·
              refine ⟨245848123048472578641237635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163898748698981719094158423 245848123048472578641237635)
              ·
                refine ⟨368772184572708867961856453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245848123048472578641237635 368772184572708867961856453)
                ·
                  refine ⟨69144784607382912742848085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368772184572708867961856453 69144784607382912742848085)
                  ·
                    refine ⟨810290444617768508705251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69144784607382912742848085 810290444617768508705251)
                    ·
                      rfl

theorem cell23_4734105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_4734105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734105 prefixEnd_4734105 := by exact prefixLift 4734105
  have htrace : WordTrace (prefixWord ++ tailWord_4734105) baseStart_4734105 baseEnd_4734105 := by
    simpa [prefixWord, tailWord_4734105, baseEnd_4734105] using wordTrace_append hprefix tailTrace_4734105
  have hstable : (prefixWord ++ tailWord_4734105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734105).length < 2 ^ (prefixWord ++ tailWord_4734105).sum := by decide
  have hdescent : baseEnd_4734105 < baseStart_4734105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734112 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4734112 : Nat := 118140960795 + 4734112 * 2 ^ 59
def prefixEnd_4734112 : Nat := 4983230072969 + 3 ^ 40 * 4734112 * 2
def baseEnd_4734112 : Nat := 2430874928217886998728221

theorem tailTrace_4734112 : CollatzResearch.WordTrace tailWord_4734112 prefixEnd_4734112 2430874928217886998728221 := by
  unfold tailWord_4734112
  simp only [CollatzResearch.WordTrace]
  refine ⟨86333624912564110402494295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115111499883418813869992393 86333624912564110402494295)
  ·
    refine ⟨129500437368846165603741443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86333624912564110402494295 129500437368846165603741443)
    ·
      refine ⟨194250656053269248405612165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129500437368846165603741443 194250656053269248405612165)
      ·
        refine ⟨36421998009987984076052281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194250656053269248405612165 36421998009987984076052281)
        ·
          refine ⟨27316498507490988057039211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36421998009987984076052281 27316498507490988057039211)
          ·
            refine ⟨40974747761236482085558817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27316498507490988057039211 40974747761236482085558817)
            ·
              refine ⟨30731060820927361564169113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40974747761236482085558817 30731060820927361564169113)
              ·
                refine ⟨23048295615695521173126835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30731060820927361564169113 23048295615695521173126835)
                ·
                  refine ⟨34572443423543281759690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23048295615695521173126835 34572443423543281759690253)
                  ·
                    refine ⟨12964666283828730659883845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34572443423543281759690253 12964666283828730659883845)
                    ·
                      refine ⟨2430874928217886998728221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12964666283828730659883845 2430874928217886998728221)
                      ·
                        rfl

theorem cell23_4734112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4734112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734112 prefixEnd_4734112 := by exact prefixLift 4734112
  have htrace : WordTrace (prefixWord ++ tailWord_4734112) baseStart_4734112 baseEnd_4734112 := by
    simpa [prefixWord, tailWord_4734112, baseEnd_4734112] using wordTrace_append hprefix tailTrace_4734112
  have hstable : (prefixWord ++ tailWord_4734112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734112).length < 2 ^ (prefixWord ++ tailWord_4734112).sum := by decide
  have hdescent : baseEnd_4734112 < baseStart_4734112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734129 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4734129 : Nat := 118140960795 + 4734129 * 2 ^ 59
def prefixEnd_4734129 : Nat := 4983230072969 + 3 ^ 40 * 4734129 * 2
def baseEnd_4734129 : Nat := 2430883657389013432215643

theorem tailTrace_4734129 : CollatzResearch.WordTrace tailWord_4734129 prefixEnd_4734129 2430883657389013432215643 := by
  unfold tailWord_4734129
  simp only [CollatzResearch.WordTrace]
  refine ⟨172667869866066632708357441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115111913244044421805571627 172667869866066632708357441)
  ·
    refine ⟨129500902399549974531268081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172667869866066632708357441 129500902399549974531268081)
    ·
      refine ⟨97125676799662480898451061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129500902399549974531268081 97125676799662480898451061)
      ·
        refine ⟨9105532199968357584229787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97125676799662480898451061 9105532199968357584229787)
        ·
          refine ⟨13658298299952536376344681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105532199968357584229787 13658298299952536376344681)
          ·
            refine ⟨10243723724964402282258511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13658298299952536376344681 10243723724964402282258511)
            ·
              refine ⟨15365585587446603423387767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10243723724964402282258511 15365585587446603423387767)
              ·
                refine ⟨23048378381169905135081651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15365585587446603423387767 23048378381169905135081651)
                ·
                  refine ⟨34572567571754857702622477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23048378381169905135081651 34572567571754857702622477)
                  ·
                    refine ⟨12964712839408071638483429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34572567571754857702622477 12964712839408071638483429)
                    ·
                      refine ⟨2430883657389013432215643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12964712839408071638483429 2430883657389013432215643)
                      ·
                        rfl

theorem cell23_4734129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4734129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734129 prefixEnd_4734129 := by exact prefixLift 4734129
  have htrace : WordTrace (prefixWord ++ tailWord_4734129) baseStart_4734129 baseEnd_4734129 := by
    simpa [prefixWord, tailWord_4734129, baseEnd_4734129] using wordTrace_append hprefix tailTrace_4734129
  have hstable : (prefixWord ++ tailWord_4734129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734129).length < 2 ^ (prefixWord ++ tailWord_4734129).sum := by decide
  have hdescent : baseEnd_4734129 < baseStart_4734129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734236 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4734236 : Nat := 118140960795 + 4734236 * 2 ^ 59
def prefixEnd_4734236 : Nat := 4983230072969 + 3 ^ 40 * 4734236 * 2
def baseEnd_4734236 : Nat := 2430938599819044513577651

theorem tailTrace_4734236 : CollatzResearch.WordTrace tailWord_4734236 prefixEnd_4734236 2430938599819044513577651 := by
  unfold tailWord_4734236
  simp only [CollatzResearch.WordTrace]
  refine ⟨86335886238339494991251281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115114514984452659988335041 86335886238339494991251281)
  ·
    refine ⟨64751914678754621243438461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86335886238339494991251281 64751914678754621243438461)
    ·
      refine ⟨24281968004532982966289423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64751914678754621243438461 24281968004532982966289423)
      ·
        refine ⟨36422952006799474449434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24281968004532982966289423 36422952006799474449434135)
        ·
          refine ⟨54634428010199211674151203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36422952006799474449434135 54634428010199211674151203)
          ·
            refine ⟨81951642015298817511226805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54634428010199211674151203 81951642015298817511226805)
            ·
              refine ⟨7682966438934264141677513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81951642015298817511226805 7682966438934264141677513)
              ·
                refine ⟨5762224829200698106258135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7682966438934264141677513 5762224829200698106258135)
                ·
                  refine ⟨8643337243801047159387203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5762224829200698106258135 8643337243801047159387203)
                  ·
                    refine ⟨12965005865701570739080805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8643337243801047159387203 12965005865701570739080805)
                    ·
                      refine ⟨2430938599819044513577651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12965005865701570739080805 2430938599819044513577651)
                      ·
                        rfl

theorem cell23_4734236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4734236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734236 prefixEnd_4734236 := by exact prefixLift 4734236
  have htrace : WordTrace (prefixWord ++ tailWord_4734236) baseStart_4734236 baseEnd_4734236 := by
    simpa [prefixWord, tailWord_4734236, baseEnd_4734236] using wordTrace_append hprefix tailTrace_4734236
  have hstable : (prefixWord ++ tailWord_4734236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734236).length < 2 ^ (prefixWord ++ tailWord_4734236).sum := by decide
  have hdescent : baseEnd_4734236 < baseStart_4734236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734272 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_4734272 : Nat := 118140960795 + 4734272 * 2 ^ 59
def prefixEnd_4734272 : Nat := 4983230072969 + 3 ^ 40 * 4734272 * 2
def baseEnd_4734272 : Nat := 810319028374202124242495

theorem tailTrace_4734272 : CollatzResearch.WordTrace tailWord_4734272 prefixEnd_4734272 810319028374202124242495 := by
  unfold tailWord_4734272
  simp only [CollatzResearch.WordTrace]
  refine ⟨86336542752274284065406535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115115390336365712087208713 86336542752274284065406535)
  ·
    refine ⟨129504814128411426098109803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86336542752274284065406535 129504814128411426098109803)
    ·
      refine ⟨194257221192617139147164705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129504814128411426098109803 194257221192617139147164705)
      ·
        refine ⟨145692915894462854360373529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194257221192617139147164705 145692915894462854360373529)
        ·
          refine ⟨109269686920847140770280147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145692915894462854360373529 109269686920847140770280147)
          ·
            refine ⟨163904530381270711155420221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109269686920847140770280147 163904530381270711155420221)
            ·
              refine ⟨61464198892976516683282583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163904530381270711155420221 61464198892976516683282583)
              ·
                refine ⟨92196298339464775024923875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61464198892976516683282583 92196298339464775024923875)
                ·
                  refine ⟨138294447509197162537385813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92196298339464775024923875 138294447509197162537385813)
                  ·
                    refine ⟨810319028374202124242495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138294447509197162537385813 810319028374202124242495)
                    ·
                      rfl

theorem cell23_4734272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_4734272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734272 prefixEnd_4734272 := by exact prefixLift 4734272
  have htrace : WordTrace (prefixWord ++ tailWord_4734272) baseStart_4734272 baseEnd_4734272 := by
    simpa [prefixWord, tailWord_4734272, baseEnd_4734272] using wordTrace_append hprefix tailTrace_4734272
  have hstable : (prefixWord ++ tailWord_4734272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734272).length < 2 ^ (prefixWord ++ tailWord_4734272).sum := by decide
  have hdescent : baseEnd_4734272 < baseStart_4734272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734276 : List Nat := [2, 3, 4, 1, 1, 1, 3, 8]
def baseStart_4734276 : Nat := 118140960795 + 4734276 * 2 ^ 59
def prefixEnd_4734276 : Nat := 4983230072969 + 3 ^ 40 * 4734276 * 2
def baseEnd_4734276 : Nat := 90035523668341642854721

theorem tailTrace_4734276 : CollatzResearch.WordTrace tailWord_4734276 prefixEnd_4734276 90035523668341642854721 := by
  unfold tailWord_4734276
  simp only [CollatzResearch.WordTrace]
  refine ⟨86336615698267038406979341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115115487597689384542639121 86336615698267038406979341)
  ·
    refine ⟨32376230886850139402617253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86336615698267038406979341 32376230886850139402617253)
    ·
      refine ⟨6070543291284401137990735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32376230886850139402617253 6070543291284401137990735)
      ·
        refine ⟨9105814936926601706986103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070543291284401137990735 9105814936926601706986103)
        ·
          refine ⟨13658722405389902560479155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105814936926601706986103 13658722405389902560479155)
          ·
            refine ⟨20488083608084853840718733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13658722405389902560479155 20488083608084853840718733)
            ·
              refine ⟨7683031353031820190269525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20488083608084853840718733 7683031353031820190269525)
              ·
                refine ⟨90035523668341642854721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7683031353031820190269525 90035523668341642854721)
                ·
                  rfl

theorem cell23_4734276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 8].length) (baseStart_4734276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734276 prefixEnd_4734276 := by exact prefixLift 4734276
  have htrace : WordTrace (prefixWord ++ tailWord_4734276) baseStart_4734276 baseEnd_4734276 := by
    simpa [prefixWord, tailWord_4734276, baseEnd_4734276] using wordTrace_append hprefix tailTrace_4734276
  have hstable : (prefixWord ++ tailWord_4734276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734276).length < 2 ^ (prefixWord ++ tailWord_4734276).sum := by decide
  have hdescent : baseEnd_4734276 < baseStart_4734276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734286 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_4734286 : Nat := 118140960795 + 4734286 * 2 ^ 59
def prefixEnd_4734286 : Nat := 4983230072969 + 3 ^ 40 * 4734286 * 2
def baseEnd_4734286 : Nat := 2430964273851769317952421

theorem tailTrace_4734286 : CollatzResearch.WordTrace tailWord_4734286 prefixEnd_4734286 2430964273851769317952421 := by
  unfold tailWord_4734286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21584199515812231065227839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115115730750998565681215141 21584199515812231065227839)
  ·
    refine ⟨32376299273718346597841759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21584199515812231065227839 32376299273718346597841759)
    ·
      refine ⟨48564448910577519896762639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32376299273718346597841759 48564448910577519896762639)
      ·
        refine ⟨72846673365866279845143959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48564448910577519896762639 72846673365866279845143959)
        ·
          refine ⟨109270010048799419767715939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72846673365866279845143959 109270010048799419767715939)
          ·
            refine ⟨163905015073199129651573909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109270010048799419767715939 163905015073199129651573909)
            ·
              refine ⟨7683047581556209202417527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163905015073199129651573909 7683047581556209202417527)
              ·
                refine ⟨11524571372334313803626291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7683047581556209202417527 11524571372334313803626291)
                ·
                  refine ⟨17286857058501470705439437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11524571372334313803626291 17286857058501470705439437)
                  ·
                    refine ⟨6482571396938051514539789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17286857058501470705439437 6482571396938051514539789)
                    ·
                      refine ⟨2430964273851769317952421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6482571396938051514539789 2430964273851769317952421)
                      ·
                        rfl

theorem cell23_4734286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_4734286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734286 prefixEnd_4734286 := by exact prefixLift 4734286
  have htrace : WordTrace (prefixWord ++ tailWord_4734286) baseStart_4734286 baseEnd_4734286 := by
    simpa [prefixWord, tailWord_4734286, baseEnd_4734286] using wordTrace_append hprefix tailTrace_4734286
  have hstable : (prefixWord ++ tailWord_4734286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734286).length < 2 ^ (prefixWord ++ tailWord_4734286).sum := by decide
  have hdescent : baseEnd_4734286 < baseStart_4734286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734296 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_4734296 : Nat := 118140960795 + 4734296 * 2 ^ 59
def prefixEnd_4734296 : Nat := 4983230072969 + 3 ^ 40 * 4734296 * 2
def baseEnd_4734296 : Nat := 2430969408658314278827375

theorem tailTrace_4734296 : CollatzResearch.WordTrace tailWord_4734296 prefixEnd_4734296 2430969408658314278827375 := by
  unfold tailWord_4734296
  simp only [CollatzResearch.WordTrace]
  refine ⟨86336980428230810114843371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115115973904307746819791161 86336980428230810114843371)
  ·
    refine ⟨129505470642346215172265057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86336980428230810114843371 129505470642346215172265057)
    ·
      refine ⟨97129102981759661379198793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129505470642346215172265057 97129102981759661379198793)
      ·
        refine ⟨72846827236319746034399095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97129102981759661379198793 72846827236319746034399095)
        ·
          refine ⟨109270240854479619051598643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72846827236319746034399095 109270240854479619051598643)
          ·
            refine ⟨163905361281719428577397965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109270240854479619051598643 163905361281719428577397965)
            ·
              refine ⟨61464510480644785716524237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163905361281719428577397965 61464510480644785716524237)
              ·
                refine ⟨23049191430241794643696589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61464510480644785716524237 23049191430241794643696589)
                ·
                  refine ⟨8643446786340672991386221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23049191430241794643696589 8643446786340672991386221)
                  ·
                    refine ⟨3241292544877752371769833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8643446786340672991386221 3241292544877752371769833)
                    ·
                      refine ⟨2430969408658314278827375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241292544877752371769833 2430969408658314278827375)
                      ·
                        rfl

theorem cell23_4734296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_4734296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734296 prefixEnd_4734296 := by exact prefixLift 4734296
  have htrace : WordTrace (prefixWord ++ tailWord_4734296) baseStart_4734296 baseEnd_4734296 := by
    simpa [prefixWord, tailWord_4734296, baseEnd_4734296] using wordTrace_append hprefix tailTrace_4734296
  have hstable : (prefixWord ++ tailWord_4734296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734296).length < 2 ^ (prefixWord ++ tailWord_4734296).sum := by decide
  have hdescent : baseEnd_4734296 < baseStart_4734296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734329 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4734329 : Nat := 118140960795 + 4734329 * 2 ^ 59
def prefixEnd_4734329 : Nat := 4983230072969 + 3 ^ 40 * 4734329 * 2
def baseEnd_4734329 : Nat := 2430986353519912649714723

theorem tailTrace_4734329 : CollatzResearch.WordTrace tailWord_4734329 prefixEnd_4734329 2430986353519912649714723 := by
  unfold tailWord_4734329
  simp only [CollatzResearch.WordTrace]
  refine ⟨172675164465342066865638041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115116776310228044577092027 172675164465342066865638041)
  ·
    refine ⟨129506373349006550149228531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172675164465342066865638041 129506373349006550149228531)
    ·
      refine ⟨194259560023509825223842797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129506373349006550149228531 194259560023509825223842797)
      ·
        refine ⟨72847335008816184458941049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194259560023509825223842797 72847335008816184458941049)
        ·
          refine ⟨54635501256612138344205787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72847335008816184458941049 54635501256612138344205787)
          ·
            refine ⟨81953251884918207516308681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54635501256612138344205787 81953251884918207516308681)
            ·
              refine ⟨61464938913688655637231511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81953251884918207516308681 61464938913688655637231511)
              ·
                refine ⟨92197408370532983455847267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61464938913688655637231511 92197408370532983455847267)
                ·
                  refine ⟨138296112555799475183770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92197408370532983455847267 138296112555799475183770901)
                  ·
                    refine ⟨6482630276053100399239261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 138296112555799475183770901 6482630276053100399239261)
                    ·
                      refine ⟨2430986353519912649714723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6482630276053100399239261 2430986353519912649714723)
                      ·
                        rfl

theorem cell23_4734329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4734329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734329 prefixEnd_4734329 := by exact prefixLift 4734329
  have htrace : WordTrace (prefixWord ++ tailWord_4734329) baseStart_4734329 baseEnd_4734329 := by
    simpa [prefixWord, tailWord_4734329, baseEnd_4734329] using wordTrace_append hprefix tailTrace_4734329
  have hstable : (prefixWord ++ tailWord_4734329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734329).length < 2 ^ (prefixWord ++ tailWord_4734329).sum := by decide
  have hdescent : baseEnd_4734329 < baseStart_4734329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734337 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4734337 : Nat := 118140960795 + 4734337 * 2 ^ 59
def prefixEnd_4734337 : Nat := 4983230072969 + 3 ^ 40 * 4734337 * 2
def baseEnd_4734337 : Nat := 2430990461365148618414687

theorem tailTrace_4734337 : CollatzResearch.WordTrace tailWord_4734337 prefixEnd_4734337 2430990461365148618414687 := by
  unfold tailWord_4734337
  simp only [CollatzResearch.WordTrace]
  refine ⟨172675456249313084231929265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115116970832875389487952843 172675456249313084231929265)
  ·
    refine ⟨129506592186984813173946949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172675456249313084231929265 129506592186984813173946949)
    ·
      refine ⟨24282486035059652470115053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129506592186984813173946949 24282486035059652470115053)
      ·
        refine ⟨9105932263147369676293145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24282486035059652470115053 9105932263147369676293145)
        ·
          refine ⟨6829449197360527257219859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9105932263147369676293145 6829449197360527257219859)
          ·
            refine ⟨10244173796040790885829789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6829449197360527257219859 10244173796040790885829789)
            ·
              refine ⟨3841565173515296582186171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10244173796040790885829789 3841565173515296582186171)
              ·
                refine ⟨5762347760272944873279257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841565173515296582186171 5762347760272944873279257)
                ·
                  refine ⟨4321760820204708654959443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5762347760272944873279257 4321760820204708654959443)
                  ·
                    refine ⟨6482641230307062982439165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4321760820204708654959443 6482641230307062982439165)
                    ·
                      refine ⟨2430990461365148618414687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6482641230307062982439165 2430990461365148618414687)
                      ·
                        rfl

theorem cell23_4734337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4734337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734337 prefixEnd_4734337 := by exact prefixLift 4734337
  have htrace : WordTrace (prefixWord ++ tailWord_4734337) baseStart_4734337 baseEnd_4734337 := by
    simpa [prefixWord, tailWord_4734337, baseEnd_4734337] using wordTrace_append hprefix tailTrace_4734337
  have hstable : (prefixWord ++ tailWord_4734337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734337).length < 2 ^ (prefixWord ++ tailWord_4734337).sum := by decide
  have hdescent : baseEnd_4734337 < baseStart_4734337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734343 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_4734343 : Nat := 118140960795 + 4734343 * 2 ^ 59
def prefixEnd_4734343 : Nat := 4983230072969 + 3 ^ 40 * 4734343 * 2
def baseEnd_4734343 : Nat := 2430993542249075594939659

theorem tailTrace_4734343 : CollatzResearch.WordTrace tailWord_4734343 prefixEnd_4734343 2430993542249075594939659 := by
  unfold tailWord_4734343
  simp only [CollatzResearch.WordTrace]
  refine ⟨172675675087291347256647683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115117116724860898171098455 172675675087291347256647683)
  ·
    refine ⟨259013512630937020884971525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172675675087291347256647683 259013512630937020884971525)
    ·
      refine ⟨48565033618300691415932161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259013512630937020884971525 48565033618300691415932161)
      ·
        refine ⟨36423775213725518561949121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48565033618300691415932161 36423775213725518561949121)
        ·
          refine ⟨27317831410294138921461841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36423775213725518561949121 27317831410294138921461841)
          ·
            refine ⟨20488373557720604191096381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27317831410294138921461841 20488373557720604191096381)
            ·
              refine ⟨7683140084145226571661143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20488373557720604191096381 7683140084145226571661143)
              ·
                refine ⟨11524710126217839857491715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7683140084145226571661143 11524710126217839857491715)
                ·
                  refine ⟨17287065189326759786237573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11524710126217839857491715 17287065189326759786237573)
                  ·
                    refine ⟨3241324722998767459919545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17287065189326759786237573 3241324722998767459919545)
                    ·
                      refine ⟨2430993542249075594939659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241324722998767459919545 2430993542249075594939659)
                      ·
                        rfl

theorem cell23_4734343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_4734343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734343 prefixEnd_4734343 := by exact prefixLift 4734343
  have htrace : WordTrace (prefixWord ++ tailWord_4734343) baseStart_4734343 baseEnd_4734343 := by
    simpa [prefixWord, tailWord_4734343, baseEnd_4734343] using wordTrace_append hprefix tailTrace_4734343
  have hstable : (prefixWord ++ tailWord_4734343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734343).length < 2 ^ (prefixWord ++ tailWord_4734343).sum := by decide
  have hdescent : baseEnd_4734343 < baseStart_4734343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734399 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_4734399 : Nat := 118140960795 + 4734399 * 2 ^ 59
def prefixEnd_4734399 : Nat := 4983230072969 + 3 ^ 40 * 4734399 * 2
def baseEnd_4734399 : Nat := 2431022297165727375839401

theorem tailTrace_4734399 : CollatzResearch.WordTrace tailWord_4734399 prefixEnd_4734399 2431022297165727375839401 := by
  unfold tailWord_4734399
  simp only [CollatzResearch.WordTrace]
  refine ⟨172677717575088468820686251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115118478383392312547124167 172677717575088468820686251)
  ·
    refine ⟨259016576362632703231029377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172677717575088468820686251 259016576362632703231029377)
    ·
      refine ⟨194262432271974527423272033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259016576362632703231029377 194262432271974527423272033)
      ·
        refine ⟨145696824203980895567454025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194262432271974527423272033 145696824203980895567454025)
        ·
          refine ⟨109272618152985671675590519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145696824203980895567454025 109272618152985671675590519)
          ·
            refine ⟨163908927229478507513385779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109272618152985671675590519 163908927229478507513385779)
            ·
              refine ⟨245863390844217761270078669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163908927229478507513385779 245863390844217761270078669)
              ·
                refine ⟨92198771566581660476279501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245863390844217761270078669 92198771566581660476279501)
                ·
                  refine ⟨34574539337468122678604813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92198771566581660476279501 34574539337468122678604813)
                  ·
                    refine ⟨12965452251550546004476805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34574539337468122678604813 12965452251550546004476805)
                    ·
                      refine ⟨2431022297165727375839401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12965452251550546004476805 2431022297165727375839401)
                      ·
                        rfl

theorem cell23_4734399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_4734399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734399 prefixEnd_4734399 := by exact prefixLift 4734399
  have htrace : WordTrace (prefixWord ++ tailWord_4734399) baseStart_4734399 baseEnd_4734399 := by
    simpa [prefixWord, tailWord_4734399, baseEnd_4734399] using wordTrace_append hprefix tailTrace_4734399
  have hstable : (prefixWord ++ tailWord_4734399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734399).length < 2 ^ (prefixWord ++ tailWord_4734399).sum := by decide
  have hdescent : baseEnd_4734399 < baseStart_4734399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734416 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2]
def baseStart_4734416 : Nat := 118140960795 + 4734416 * 2 ^ 59
def prefixEnd_4734416 : Nat := 4983230072969 + 3 ^ 40 * 4734416 * 2
def baseEnd_4734416 : Nat := 2431031026336853809326823

theorem tailTrace_4734416 : CollatzResearch.WordTrace tailWord_4734416 prefixEnd_4734416 2431031026336853809326823 := by
  unfold tailWord_4734416
  simp only [CollatzResearch.WordTrace]
  refine ⟨86339168808013440362027551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115118891744017920482703401 86339168808013440362027551)
  ·
    refine ⟨129508753212020160543041327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86339168808013440362027551 129508753212020160543041327)
    ·
      refine ⟨194263129818030240814561991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129508753212020160543041327 194263129818030240814561991)
      ·
        refine ⟨291394694727045361221842987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194263129818030240814561991 291394694727045361221842987)
        ·
          refine ⟨437092042090568041832764481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291394694727045361221842987 437092042090568041832764481)
          ·
            refine ⟨327819031567926031374573361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437092042090568041832764481 327819031567926031374573361)
            ·
              refine ⟨245864273675944523530930021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327819031567926031374573361 245864273675944523530930021)
              ·
                refine ⟨46099551314239598162049379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245864273675944523530930021 46099551314239598162049379)
                ·
                  refine ⟨69149326971359397243074069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46099551314239598162049379 69149326971359397243074069)
                  ·
                    refine ⟨3241374701782471745769097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69149326971359397243074069 3241374701782471745769097)
                    ·
                      refine ⟨2431031026336853809326823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241374701782471745769097 2431031026336853809326823)
                      ·
                        rfl

theorem cell23_4734416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2].length) (baseStart_4734416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734416 prefixEnd_4734416 := by exact prefixLift 4734416
  have htrace : WordTrace (prefixWord ++ tailWord_4734416) baseStart_4734416 baseEnd_4734416 := by
    simpa [prefixWord, tailWord_4734416, baseEnd_4734416] using wordTrace_append hprefix tailTrace_4734416
  have hstable : (prefixWord ++ tailWord_4734416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734416).length < 2 ^ (prefixWord ++ tailWord_4734416).sum := by decide
  have hdescent : baseEnd_4734416 < baseStart_4734416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734450 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4734450 : Nat := 118140960795 + 4734450 * 2 ^ 59
def prefixEnd_4734450 : Nat := 4983230072969 + 3 ^ 40 * 4734450 * 2
def baseEnd_4734450 : Nat := 2431048484679106676301667

theorem tailTrace_4734450 : CollatzResearch.WordTrace tailWord_4734450 prefixEnd_4734450 2431048484679106676301667 := by
  unfold tailWord_4734450
  simp only [CollatzResearch.WordTrace]
  refine ⟨43169894424475926132698201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115119718465269136353861869 43169894424475926132698201)
  ·
    refine ⟨32377420818356944599523651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43169894424475926132698201 32377420818356944599523651)
    ·
      refine ⟨48566131227535416899285477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32377420818356944599523651 48566131227535416899285477)
      ·
        refine ⟨9106149605162890668616027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48566131227535416899285477 9106149605162890668616027)
        ·
          refine ⟨13659224407744336002924041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106149605162890668616027 13659224407744336002924041)
          ·
            refine ⟨10244418305808252002193031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13659224407744336002924041 10244418305808252002193031)
            ·
              refine ⟨15366627458712378003289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10244418305808252002193031 15366627458712378003289547)
              ·
                refine ⟨23049941188068567004934321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15366627458712378003289547 23049941188068567004934321)
                ·
                  refine ⟨17287455891051425253700741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23049941188068567004934321 17287455891051425253700741)
                  ·
                    refine ⟨3241397979572142235068889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17287455891051425253700741 3241397979572142235068889)
                    ·
                      refine ⟨2431048484679106676301667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241397979572142235068889 2431048484679106676301667)
                      ·
                        rfl

theorem cell23_4734450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4734450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734450 prefixEnd_4734450 := by exact prefixLift 4734450
  have htrace : WordTrace (prefixWord ++ tailWord_4734450) baseStart_4734450 baseEnd_4734450 := by
    simpa [prefixWord, tailWord_4734450, baseEnd_4734450] using wordTrace_append hprefix tailTrace_4734450
  have hstable : (prefixWord ++ tailWord_4734450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734450).length < 2 ^ (prefixWord ++ tailWord_4734450).sum := by decide
  have hdescent : baseEnd_4734450 < baseStart_4734450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734456 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 6]
def baseStart_4734456 : Nat := 118140960795 + 4734456 * 2 ^ 59
def prefixEnd_4734456 : Nat := 4983230072969 + 3 ^ 40 * 4734456 * 2
def baseEnd_4734456 : Nat := 270116840618114850314071

theorem tailTrace_4734456 : CollatzResearch.WordTrace tailWord_4734456 prefixEnd_4734456 270116840618114850314071 := by
  unfold tailWord_4734456
  simp only [CollatzResearch.WordTrace]
  refine ⟨86339898267940983777755611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115119864357254645037007481 86339898267940983777755611)
  ·
    refine ⟨129509847401911475666633417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86339898267940983777755611 129509847401911475666633417)
    ·
      refine ⟨97132385551433606749975063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129509847401911475666633417 97132385551433606749975063)
      ·
        refine ⟨145698578327150410124962595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97132385551433606749975063 145698578327150410124962595)
        ·
          refine ⟨218547867490725615187443893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145698578327150410124962595 218547867490725615187443893)
          ·
            refine ⟨20488862577255526423822865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218547867490725615187443893 20488862577255526423822865)
            ·
              refine ⟨15366646932941644817867149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20488862577255526423822865 15366646932941644817867149)
              ·
                refine ⟨5762492599853116806700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15366646932941644817867149 5762492599853116806700181)
                ·
                  refine ⟨270116840618114850314071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5762492599853116806700181 270116840618114850314071)
                  ·
                    rfl

theorem cell23_4734456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_4734456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734456 prefixEnd_4734456 := by exact prefixLift 4734456
  have htrace : WordTrace (prefixWord ++ tailWord_4734456) baseStart_4734456 baseEnd_4734456 := by
    simpa [prefixWord, tailWord_4734456, baseEnd_4734456] using wordTrace_append hprefix tailTrace_4734456
  have hstable : (prefixWord ++ tailWord_4734456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734456).length < 2 ^ (prefixWord ++ tailWord_4734456).sum := by decide
  have hdescent : baseEnd_4734456 < baseStart_4734456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734459 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_4734459 : Nat := 118140960795 + 4734459 * 2 ^ 59
def prefixEnd_4734459 : Nat := 4983230072969 + 3 ^ 40 * 4734459 * 2
def baseEnd_4734459 : Nat := 2431053106004997141089125

theorem tailTrace_4734459 : CollatzResearch.WordTrace tailWord_4734459 prefixEnd_4734459 2431053106004997141089125 := by
  unfold tailWord_4734459
  simp only [CollatzResearch.WordTrace]
  refine ⟨172679905954871099067870431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115119937303247399378580287 172679905954871099067870431)
  ·
    refine ⟨259019858932306648601805647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172679905954871099067870431 259019858932306648601805647)
    ·
      refine ⟨388529788398459972902708471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259019858932306648601805647 388529788398459972902708471)
      ·
        refine ⟨582794682597689959354062707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388529788398459972902708471 582794682597689959354062707)
        ·
          refine ⟨874192023896534939031094061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582794682597689959354062707 874192023896534939031094061)
          ·
            refine ⟨327822008961200602136660273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 874192023896534939031094061 327822008961200602136660273)
            ·
              refine ⟨245866506720900451602495205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327822008961200602136660273 245866506720900451602495205)
              ·
                refine ⟨46099970010168834675467851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245866506720900451602495205 46099970010168834675467851)
                ·
                  refine ⟨69149955015253252013201777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46099970010168834675467851 69149955015253252013201777)
                  ·
                    refine ⟨51862466261439939009901333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69149955015253252013201777 51862466261439939009901333)
                    ·
                      refine ⟨2431053106004997141089125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51862466261439939009901333 2431053106004997141089125)
                      ·
                        rfl

theorem cell23_4734459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_4734459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734459 prefixEnd_4734459 := by exact prefixLift 4734459
  have htrace : WordTrace (prefixWord ++ tailWord_4734459) baseStart_4734459 baseEnd_4734459 := by
    simpa [prefixWord, tailWord_4734459, baseEnd_4734459] using wordTrace_append hprefix tailTrace_4734459
  have hstable : (prefixWord ++ tailWord_4734459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734459).length < 2 ^ (prefixWord ++ tailWord_4734459).sum := by decide
  have hdescent : baseEnd_4734459 < baseStart_4734459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734479 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_4734479 : Nat := 118140960795 + 4734479 * 2 ^ 59
def prefixEnd_4734479 : Nat := 4983230072969 + 3 ^ 40 * 4734479 * 2
def baseEnd_4734479 : Nat := 2431063375618087062839033

theorem tailTrace_4734479 : CollatzResearch.WordTrace tailWord_4734479 prefixEnd_4734479 2431063375618087062839033 := by
  unfold tailWord_4734479
  simp only [CollatzResearch.WordTrace]
  refine ⟨172680635414798642483598491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115120423609865761655732327 172680635414798642483598491)
  ·
    refine ⟨259020953122197963725397737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172680635414798642483598491 259020953122197963725397737)
    ·
      refine ⟨194265714841648472794048303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259020953122197963725397737 194265714841648472794048303)
      ·
        refine ⟨291398572262472709191072455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194265714841648472794048303 291398572262472709191072455)
        ·
          refine ⟨437097858393709063786608683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291398572262472709191072455 437097858393709063786608683)
          ·
            refine ⟨655646787590563595679913025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437097858393709063786608683 655646787590563595679913025)
            ·
              refine ⟨491735090692922696759934769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655646787590563595679913025 491735090692922696759934769)
              ·
                refine ⟨368801318019692022569951077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491735090692922696759934769 368801318019692022569951077)
                ·
                  refine ⟨69150247128692254231865827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368801318019692022569951077 69150247128692254231865827)
                  ·
                    refine ⟨103725370693038381347798741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69150247128692254231865827 103725370693038381347798741)
                    ·
                      refine ⟨2431063375618087062839033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103725370693038381347798741 2431063375618087062839033)
                      ·
                        rfl

theorem cell23_4734479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_4734479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734479 prefixEnd_4734479 := by exact prefixLift 4734479
  have htrace : WordTrace (prefixWord ++ tailWord_4734479) baseStart_4734479 baseEnd_4734479 := by
    simpa [prefixWord, tailWord_4734479, baseEnd_4734479] using wordTrace_append hprefix tailTrace_4734479
  have hstable : (prefixWord ++ tailWord_4734479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734479).length < 2 ^ (prefixWord ++ tailWord_4734479).sum := by decide
  have hdescent : baseEnd_4734479 < baseStart_4734479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734510 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4734510 : Nat := 118140960795 + 4734510 * 2 ^ 59
def prefixEnd_4734510 : Nat := 4983230072969 + 3 ^ 40 * 4734510 * 2
def baseEnd_4734510 : Nat := 2431079293518376441551391

theorem tailTrace_4734510 : CollatzResearch.WordTrace tailWord_4734510 prefixEnd_4734510 2431079293518376441551391 := by
  unfold tailWord_4734510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585220759710791847247123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115121177385124223185317989 21585220759710791847247123)
  ·
    refine ⟨32377831139566187770870685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585220759710791847247123 32377831139566187770870685)
    ·
      refine ⟨12141686677337320414076507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32377831139566187770870685 12141686677337320414076507)
      ·
        refine ⟨18212530016005980621114761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12141686677337320414076507 18212530016005980621114761)
        ·
          refine ⟨13659397512004485465836071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18212530016005980621114761 13659397512004485465836071)
          ·
            refine ⟨20489096268006728198754107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13659397512004485465836071 20489096268006728198754107)
            ·
              refine ⟨30733644402010092298131161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20489096268006728198754107 30733644402010092298131161)
              ·
                refine ⟨23050233301507569223598371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30733644402010092298131161 23050233301507569223598371)
                ·
                  refine ⟨34575349952261353835397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23050233301507569223598371 34575349952261353835397557)
                  ·
                    refine ⟨3241439058024501922068521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34575349952261353835397557 3241439058024501922068521)
                    ·
                      refine ⟨2431079293518376441551391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241439058024501922068521 2431079293518376441551391)
                      ·
                        rfl

theorem cell23_4734510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4734510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734510 prefixEnd_4734510 := by exact prefixLift 4734510
  have htrace : WordTrace (prefixWord ++ tailWord_4734510) baseStart_4734510 baseEnd_4734510 := by
    simpa [prefixWord, tailWord_4734510, baseEnd_4734510] using wordTrace_append hprefix tailTrace_4734510
  have hstable : (prefixWord ++ tailWord_4734510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734510).length < 2 ^ (prefixWord ++ tailWord_4734510).sum := by decide
  have hdescent : baseEnd_4734510 < baseStart_4734510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734546 : List Nat := [3, 2, 2, 1, 2, 2, 11]
def baseStart_4734546 : Nat := 118140960795 + 4734546 * 2 ^ 59
def prefixEnd_4734546 : Nat := 4983230072969 + 3 ^ 40 * 4734546 * 2
def baseEnd_4734546 : Nat := 30013552824962201243225

theorem tailTrace_4734546 : CollatzResearch.WordTrace tailWord_4734546 prefixEnd_4734546 30013552824962201243225 := by
  unfold tailWord_4734546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43170769776388978231571873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115122052737037275284191661 43170769776388978231571873)
  ·
    refine ⟨32378077332291733673678905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43170769776388978231571873 32378077332291733673678905)
    ·
      refine ⟨24283557999218800255259179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32378077332291733673678905 24283557999218800255259179)
      ·
        refine ⟨36425336998828200382888769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24283557999218800255259179 36425336998828200382888769)
        ·
          refine ⟨27319002749121150287166577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36425336998828200382888769 27319002749121150287166577)
          ·
            refine ⟨20489252061840862715374933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27319002749121150287166577 20489252061840862715374933)
            ·
              refine ⟨30013552824962201243225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20489252061840862715374933 30013552824962201243225)
              ·
                rfl

theorem cell23_4734546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 11].length) (baseStart_4734546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734546 prefixEnd_4734546 := by exact prefixLift 4734546
  have htrace : WordTrace (prefixWord ++ tailWord_4734546) baseStart_4734546 baseEnd_4734546 := by
    simpa [prefixWord, tailWord_4734546, baseEnd_4734546] using wordTrace_append hprefix tailTrace_4734546
  have hstable : (prefixWord ++ tailWord_4734546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734546).length < 2 ^ (prefixWord ++ tailWord_4734546).sum := by decide
  have hdescent : baseEnd_4734546 < baseStart_4734546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734574 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4734574 : Nat := 118140960795 + 4734574 * 2 ^ 59
def prefixEnd_4734574 : Nat := 4983230072969 + 3 ^ 40 * 4734574 * 2
def baseEnd_4734574 : Nat := 2431112156280264191151097

theorem tailTrace_4734574 : CollatzResearch.WordTrace tailWord_4734574 prefixEnd_4734574 2431112156280264191151097 := by
  unfold tailWord_4734574
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585512543681809213538347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115122733566302982472204517 21585512543681809213538347)
  ·
    refine ⟨32378268815522713820307521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585512543681809213538347 32378268815522713820307521)
    ·
      refine ⟨24283701611642035365230641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32378268815522713820307521 24283701611642035365230641)
      ·
        refine ⟨18212776208731526523922981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24283701611642035365230641 18212776208731526523922981)
        ·
          refine ⟨3414895539137161223235559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18212776208731526523922981 3414895539137161223235559)
          ·
            refine ⟨5122343308705741834853339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414895539137161223235559 5122343308705741834853339)
            ·
              refine ⟨7683514963058612752280009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122343308705741834853339 7683514963058612752280009)
              ·
                refine ⟨5762636222293959564210007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7683514963058612752280009 5762636222293959564210007)
                ·
                  refine ⟨8643954333440939346315011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5762636222293959564210007 8643954333440939346315011)
                  ·
                    refine ⟨12965931500161409019472517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8643954333440939346315011 12965931500161409019472517)
                    ·
                      refine ⟨2431112156280264191151097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12965931500161409019472517 2431112156280264191151097)
                      ·
                        rfl

theorem cell23_4734574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4734574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734574 prefixEnd_4734574 := by exact prefixLift 4734574
  have htrace : WordTrace (prefixWord ++ tailWord_4734574) baseStart_4734574 baseEnd_4734574 := by
    simpa [prefixWord, tailWord_4734574, baseEnd_4734574] using wordTrace_append hprefix tailTrace_4734574
  have hstable : (prefixWord ++ tailWord_4734574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734574).length < 2 ^ (prefixWord ++ tailWord_4734574).sum := by decide
  have hdescent : baseEnd_4734574 < baseStart_4734574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734586 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_4734586 : Nat := 118140960795 + 4734586 * 2 ^ 59
def prefixEnd_4734586 : Nat := 4983230072969 + 3 ^ 40 * 4734586 * 2
def baseEnd_4734586 : Nat := 2431118318048118144201041

theorem tailTrace_4734586 : CollatzResearch.WordTrace tailWord_4734586 prefixEnd_4734586 2431118318048118144201041 := by
  unfold tailWord_4734586
  simp only [CollatzResearch.WordTrace]
  refine ⟨43171134506352749939435903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115123025350273999838495741 43171134506352749939435903)
  ·
    refine ⟨64756701759529124909153855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43171134506352749939435903 64756701759529124909153855)
    ·
      refine ⟨97135052639293687363730783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64756701759529124909153855 97135052639293687363730783)
      ·
        refine ⟨145702578958940531045596175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97135052639293687363730783 145702578958940531045596175)
        ·
          refine ⟨218553868438410796568394263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145702578958940531045596175 218553868438410796568394263)
          ·
            refine ⟨327830802657616194852591395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218553868438410796568394263 327830802657616194852591395)
            ·
              refine ⟨491746203986424292278887093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327830802657616194852591395 491746203986424292278887093)
              ·
                refine ⟨46101206623727277401145665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491746203986424292278887093 46101206623727277401145665)
                ·
                  refine ⟨34575904967795458050859249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46101206623727277401145665 34575904967795458050859249)
                  ·
                    refine ⟨25931928725846593538144437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34575904967795458050859249 25931928725846593538144437)
                    ·
                      refine ⟨2431118318048118144201041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25931928725846593538144437 2431118318048118144201041)
                      ·
                        rfl

theorem cell23_4734586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_4734586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734586 prefixEnd_4734586 := by exact prefixLift 4734586
  have htrace : WordTrace (prefixWord ++ tailWord_4734586) baseStart_4734586 baseEnd_4734586 := by
    simpa [prefixWord, tailWord_4734586, baseEnd_4734586] using wordTrace_append hprefix tailTrace_4734586
  have hstable : (prefixWord ++ tailWord_4734586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734586).length < 2 ^ (prefixWord ++ tailWord_4734586).sum := by decide
  have hdescent : baseEnd_4734586 < baseStart_4734586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734663 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_4734663 : Nat := 118140960795 + 4734663 * 2 ^ 59
def prefixEnd_4734663 : Nat := 4983230072969 + 3 ^ 40 * 4734663 * 2
def baseEnd_4734663 : Nat := 2431157856058514342938187

theorem tailTrace_4734663 : CollatzResearch.WordTrace tailWord_4734663 prefixEnd_4734663 2431157856058514342938187 := by
  unfold tailWord_4734663
  simp only [CollatzResearch.WordTrace]
  refine ⟨172687346446132041908296643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115124897630754694605531095 172687346446132041908296643)
  ·
    refine ⟨259031019669198062862444965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172687346446132041908296643 259031019669198062862444965)
    ·
      refine ⟨48568316187974636786708431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259031019669198062862444965 48568316187974636786708431)
      ·
        refine ⟨72852474281961955180062647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48568316187974636786708431 72852474281961955180062647)
        ·
          refine ⟨109278711422942932770093971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72852474281961955180062647 109278711422942932770093971)
          ·
            refine ⟨163918067134414399155140957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109278711422942932770093971 163918067134414399155140957)
            ·
              refine ⟨61469275175405399683177859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163918067134414399155140957 61469275175405399683177859)
              ·
                refine ⟨92203912763108099524766789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61469275175405399683177859 92203912763108099524766789)
                ·
                  refine ⟨17288233643082768660893773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92203912763108099524766789 17288233643082768660893773)
                  ·
                    refine ⟨6483087616156038247835165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17288233643082768660893773 6483087616156038247835165)
                    ·
                      refine ⟨2431157856058514342938187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483087616156038247835165 2431157856058514342938187)
                      ·
                        rfl

theorem cell23_4734663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_4734663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734663 prefixEnd_4734663 := by exact prefixLift 4734663
  have htrace : WordTrace (prefixWord ++ tailWord_4734663) baseStart_4734663 baseEnd_4734663 := by
    simpa [prefixWord, tailWord_4734663, baseEnd_4734663] using wordTrace_append hprefix tailTrace_4734663
  have hstable : (prefixWord ++ tailWord_4734663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734663).length < 2 ^ (prefixWord ++ tailWord_4734663).sum := by decide
  have hdescent : baseEnd_4734663 < baseStart_4734663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734670 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_4734670 : Nat := 118140960795 + 4734670 * 2 ^ 59
def prefixEnd_4734670 : Nat := 4983230072969 + 3 ^ 40 * 4734670 * 2
def baseEnd_4734670 : Nat := 270129050047010646172295

theorem tailTrace_4734670 : CollatzResearch.WordTrace tailWord_4734670 prefixEnd_4734670 270129050047010646172295 := by
  unfold tailWord_4734670
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585950219638335262975183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115125067838071121402534309 21585950219638335262975183)
  ·
    refine ⟨32378925329457502894462775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585950219638335262975183 32378925329457502894462775)
    ·
      refine ⟨48568387994186254341694163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32378925329457502894462775 48568387994186254341694163)
      ·
        refine ⟨72852581991279381512541245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48568387994186254341694163 72852581991279381512541245)
        ·
          refine ⟨27319718246729768067202967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72852581991279381512541245 27319718246729768067202967)
          ·
            refine ⟨40979577370094652100804451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27319718246729768067202967 40979577370094652100804451)
            ·
              refine ⟨61469366055141978151206677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40979577370094652100804451 61469366055141978151206677)
              ·
                refine ⟨2881376533834780225837813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61469366055141978151206677 2881376533834780225837813)
                ·
                  refine ⟨270129050047010646172295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2881376533834780225837813 270129050047010646172295)
                  ·
                    rfl

theorem cell23_4734670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_4734670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734670 prefixEnd_4734670 := by exact prefixLift 4734670
  have htrace : WordTrace (prefixWord ++ tailWord_4734670) baseStart_4734670 baseEnd_4734670 := by
    simpa [prefixWord, tailWord_4734670, baseEnd_4734670] using wordTrace_append hprefix tailTrace_4734670
  have hstable : (prefixWord ++ tailWord_4734670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734670).length < 2 ^ (prefixWord ++ tailWord_4734670).sum := by decide
  have hdescent : baseEnd_4734670 < baseStart_4734670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734703 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_4734703 : Nat := 118140960795 + 4734703 * 2 ^ 59
def prefixEnd_4734703 : Nat := 4983230072969 + 3 ^ 40 * 4734703 * 2
def baseEnd_4734703 : Nat := 2431178395284694186438003

theorem tailTrace_4734703 : CollatzResearch.WordTrace tailWord_4734703 prefixEnd_4734703 2431178395284694186438003 := by
  unfold tailWord_4734703
  simp only [CollatzResearch.WordTrace]
  refine ⟨172688805365987128739752763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115125870243991419159835175 172688805365987128739752763)
  ·
    refine ⟨259033208048980693109629145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172688805365987128739752763 259033208048980693109629145)
    ·
      refine ⟨194274906036735519832221859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259033208048980693109629145 194274906036735519832221859)
      ·
        refine ⟨291412359055103279748332789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194274906036735519832221859 291412359055103279748332789)
        ·
          refine ⟨27319908661415932476406199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 291412359055103279748332789 27319908661415932476406199)
          ·
            refine ⟨40979862992123898714609299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27319908661415932476406199 40979862992123898714609299)
            ·
              refine ⟨61469794488185848071913949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40979862992123898714609299 61469794488185848071913949)
              ·
                refine ⟨23051172933069693026967731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61469794488185848071913949 23051172933069693026967731)
                ·
                  refine ⟨34576759399604539540451597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23051172933069693026967731 34576759399604539540451597)
                  ·
                    refine ⟨12966284774851702327669349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34576759399604539540451597 12966284774851702327669349)
                    ·
                      refine ⟨2431178395284694186438003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12966284774851702327669349 2431178395284694186438003)
                      ·
                        rfl

theorem cell23_4734703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_4734703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734703 prefixEnd_4734703 := by exact prefixLift 4734703
  have htrace : WordTrace (prefixWord ++ tailWord_4734703) baseStart_4734703 baseEnd_4734703 := by
    simpa [prefixWord, tailWord_4734703, baseEnd_4734703] using wordTrace_append hprefix tailTrace_4734703
  have hstable : (prefixWord ++ tailWord_4734703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734703).length < 2 ^ (prefixWord ++ tailWord_4734703).sum := by decide
  have hdescent : baseEnd_4734703 < baseStart_4734703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734757 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_4734757 : Nat := 118140960795 + 4734757 * 2 ^ 59
def prefixEnd_4734757 : Nat := 4983230072969 + 3 ^ 40 * 4734757 * 2
def baseEnd_4734757 : Nat := 2431206123240036975162755

theorem tailTrace_4734757 : CollatzResearch.WordTrace tailWord_4734757 prefixEnd_4734757 2431206123240036975162755 := by
  unfold tailWord_4734757
  simp only [CollatzResearch.WordTrace]
  refine ⟨172690774907791495962218525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115127183271860997308145683 172690774907791495962218525)
  ·
    refine ⟨64759040590421810985831947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172690774907791495962218525 64759040590421810985831947)
    ·
      refine ⟨97138560885632716478747921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64759040590421810985831947 97138560885632716478747921)
      ·
        refine ⟨72853920664224537359060941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97138560885632716478747921 72853920664224537359060941)
        ·
          refine ⟨27320220249084201509647853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72853920664224537359060941 27320220249084201509647853)
          ·
            refine ⟨10245082593406575566117945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27320220249084201509647853 10245082593406575566117945)
            ·
              refine ⟨7683811945054931674588459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10245082593406575566117945 7683811945054931674588459)
              ·
                refine ⟨11525717917582397511882689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7683811945054931674588459 11525717917582397511882689)
                ·
                  refine ⟨8644288438186798133912017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11525717917582397511882689 8644288438186798133912017)
                  ·
                    refine ⟨6483216328640098600434013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8644288438186798133912017 6483216328640098600434013)
                    ·
                      refine ⟨2431206123240036975162755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483216328640098600434013 2431206123240036975162755)
                      ·
                        rfl

theorem cell23_4734757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_4734757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734757 prefixEnd_4734757 := by exact prefixLift 4734757
  have htrace : WordTrace (prefixWord ++ tailWord_4734757) baseStart_4734757 baseEnd_4734757 := by
    simpa [prefixWord, tailWord_4734757, baseEnd_4734757] using wordTrace_append hprefix tailTrace_4734757
  have hstable : (prefixWord ++ tailWord_4734757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734757).length < 2 ^ (prefixWord ++ tailWord_4734757).sum := by decide
  have hdescent : baseEnd_4734757 < baseStart_4734757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734774 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4734774 : Nat := 118140960795 + 4734774 * 2 ^ 59
def prefixEnd_4734774 : Nat := 4983230072969 + 3 ^ 40 * 4734774 * 2
def baseEnd_4734774 : Nat := 2431214852411163408650177

theorem tailTrace_4734774 : CollatzResearch.WordTrace tailWord_4734774 prefixEnd_4734774 2431214852411163408650177 := by
  unfold tailWord_4734774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10793212184295619241599211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115127596632486605243724917 10793212184295619241599211)
  ·
    refine ⟨16189818276443428862398817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10793212184295619241599211 16189818276443428862398817)
    ·
      refine ⟨12142363707332571646799113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16189818276443428862398817 12142363707332571646799113)
      ·
        refine ⟨9106772780499428735099335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12142363707332571646799113 9106772780499428735099335)
        ·
          refine ⟨13660159170749143102649003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106772780499428735099335 13660159170749143102649003)
          ·
            refine ⟨20490238756123714653973505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13660159170749143102649003 20490238756123714653973505)
            ·
              refine ⟨15367679067092785990480129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20490238756123714653973505 15367679067092785990480129)
              ·
                refine ⟨11525759300319589492860097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15367679067092785990480129 11525759300319589492860097)
                ·
                  refine ⟨8644319475239692119645073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11525759300319589492860097 8644319475239692119645073)
                  ·
                    refine ⟨6483239606429769089733805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8644319475239692119645073 6483239606429769089733805)
                    ·
                      refine ⟨2431214852411163408650177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483239606429769089733805 2431214852411163408650177)
                      ·
                        rfl

theorem cell23_4734774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4734774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734774 prefixEnd_4734774 := by exact prefixLift 4734774
  have htrace : WordTrace (prefixWord ++ tailWord_4734774) baseStart_4734774 baseEnd_4734774 := by
    simpa [prefixWord, tailWord_4734774, baseEnd_4734774] using wordTrace_append hprefix tailTrace_4734774
  have hstable : (prefixWord ++ tailWord_4734774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734774).length < 2 ^ (prefixWord ++ tailWord_4734774).sum := by decide
  have hdescent : baseEnd_4734774 < baseStart_4734774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734781 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_4734781 : Nat := 118140960795 + 4734781 * 2 ^ 59
def prefixEnd_4734781 : Nat := 4983230072969 + 3 ^ 40 * 4734781 * 2
def baseEnd_4734781 : Nat := 810406148925248293754215

theorem tailTrace_4734781 : CollatzResearch.WordTrace tailWord_4734781 prefixEnd_4734781 810406148925248293754215 := by
  unfold tailWord_4734781
  simp only [CollatzResearch.WordTrace]
  refine ⟨172691650259704548061092197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115127766839803032040728131 172691650259704548061092197)
  ·
    refine ⟨32379684423694602761454787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172691650259704548061092197 32379684423694602761454787)
    ·
      refine ⟨48569526635541904142182181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32379684423694602761454787 48569526635541904142182181)
      ·
        refine ⟨9106786244164107026659159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48569526635541904142182181 9106786244164107026659159)
        ·
          refine ⟨13660179366246160539988739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106786244164107026659159 13660179366246160539988739)
          ·
            refine ⟨20490269049369240809983109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13660179366246160539988739 20490269049369240809983109)
            ·
              refine ⟨3841925446756732651871833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20490269049369240809983109 3841925446756732651871833)
              ·
                refine ⟨2881444085067549488903875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841925446756732651871833 2881444085067549488903875)
                ·
                  refine ⟨4322166127601324233355813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881444085067549488903875 4322166127601324233355813)
                  ·
                    refine ⟨810406148925248293754215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322166127601324233355813 810406148925248293754215)
                    ·
                      rfl

theorem cell23_4734781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_4734781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734781 prefixEnd_4734781 := by exact prefixLift 4734781
  have htrace : WordTrace (prefixWord ++ tailWord_4734781) baseStart_4734781 baseEnd_4734781 := by
    simpa [prefixWord, tailWord_4734781, baseEnd_4734781] using wordTrace_append hprefix tailTrace_4734781
  have hstable : (prefixWord ++ tailWord_4734781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734781).length < 2 ^ (prefixWord ++ tailWord_4734781).sum := by decide
  have hdescent : baseEnd_4734781 < baseStart_4734781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734804 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_4734804 : Nat := 118140960795 + 4734804 * 2 ^ 59
def prefixEnd_4734804 : Nat := 4983230072969 + 3 ^ 40 * 4734804 * 2
def baseEnd_4734804 : Nat := 2431230256830798291275039

theorem tailTrace_4734804 : CollatzResearch.WordTrace tailWord_4734804 prefixEnd_4734804 2431230256830798291275039 := by
  unfold tailWord_4734804
  simp only [CollatzResearch.WordTrace]
  refine ⟨86346244569310611494589733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115128326092414148659452977 86346244569310611494589733)
  ·
    refine ⟨16189920856745739655235575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86346244569310611494589733 16189920856745739655235575)
    ·
      refine ⟨24284881285118609482853363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16189920856745739655235575 24284881285118609482853363)
      ·
        refine ⟨36427321927677914224280045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24284881285118609482853363 36427321927677914224280045)
        ·
          refine ⟨13660245722879217834105017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36427321927677914224280045 13660245722879217834105017)
          ·
            refine ⟨10245184292159413375578763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13660245722879217834105017 10245184292159413375578763)
            ·
              refine ⟨15367776438239120063368145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10245184292159413375578763 15367776438239120063368145)
              ·
                refine ⟨11525832328679340047526109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15367776438239120063368145 11525832328679340047526109)
                ·
                  refine ⟨4322187123254752517822291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11525832328679340047526109 4322187123254752517822291)
                  ·
                    refine ⟨6483280684882128776733437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4322187123254752517822291 6483280684882128776733437)
                    ·
                      refine ⟨2431230256830798291275039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483280684882128776733437 2431230256830798291275039)
                      ·
                        rfl

theorem cell23_4734804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_4734804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734804 prefixEnd_4734804 := by exact prefixLift 4734804
  have htrace : WordTrace (prefixWord ++ tailWord_4734804) baseStart_4734804 baseEnd_4734804 := by
    simpa [prefixWord, tailWord_4734804, baseEnd_4734804] using wordTrace_append hprefix tailTrace_4734804
  have hstable : (prefixWord ++ tailWord_4734804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734804).length < 2 ^ (prefixWord ++ tailWord_4734804).sum := by decide
  have hdescent : baseEnd_4734804 < baseStart_4734804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734810 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_4734810 : Nat := 118140960795 + 4734810 * 2 ^ 59
def prefixEnd_4734810 : Nat := 4983230072969 + 3 ^ 40 * 4734810 * 2
def baseEnd_4734810 : Nat := 2431233337714725267800011

theorem tailTrace_4734810 : CollatzResearch.WordTrace tailWord_4734810 prefixEnd_4734810 2431233337714725267800011 := by
  unfold tailWord_4734810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43173176994149871503474471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115128471984399657342598589 43173176994149871503474471)
  ·
    refine ⟨64759765491224807255211707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43173176994149871503474471 64759765491224807255211707)
    ·
      refine ⟨97139648236837210882817561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64759765491224807255211707 97139648236837210882817561)
      ·
        refine ⟨72854736177627908162113171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97139648236837210882817561 72854736177627908162113171)
        ·
          refine ⟨109282104266441862243169757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72854736177627908162113171 109282104266441862243169757)
          ·
            refine ⟨40980789099915698341188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109282104266441862243169757 40980789099915698341188659)
            ·
              refine ⟨61471183649873547511782989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40980789099915698341188659 61471183649873547511782989)
              ·
                refine ⟨23051693868702580316918621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61471183649873547511782989 23051693868702580316918621)
                ·
                  refine ⟨8644385200763467618844483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23051693868702580316918621 8644385200763467618844483)
                  ·
                    refine ⟨12966577801145201428266725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8644385200763467618844483 12966577801145201428266725)
                    ·
                      refine ⟨2431233337714725267800011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12966577801145201428266725 2431233337714725267800011)
                      ·
                        rfl

theorem cell23_4734810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_4734810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734810 prefixEnd_4734810 := by exact prefixLift 4734810
  have htrace : WordTrace (prefixWord ++ tailWord_4734810) baseStart_4734810 baseEnd_4734810 := by
    simpa [prefixWord, tailWord_4734810, baseEnd_4734810] using wordTrace_append hprefix tailTrace_4734810
  have hstable : (prefixWord ++ tailWord_4734810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734810).length < 2 ^ (prefixWord ++ tailWord_4734810).sum := by decide
  have hdescent : baseEnd_4734810 < baseStart_4734810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734827 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 7, 2, 2]
def baseStart_4734827 : Nat := 118140960795 + 4734827 * 2 ^ 59
def prefixEnd_4734827 : Nat := 4983230072969 + 3 ^ 40 * 4734827 * 2
def baseEnd_4734827 : Nat := 2431242066885851701287433

theorem tailTrace_4734827 : CollatzResearch.WordTrace tailWord_4734827 prefixEnd_4734827 2431242066885851701287433 := by
  unfold tailWord_4734827
  simp only [CollatzResearch.WordTrace]
  refine ⟨172693328017537897917266735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115128885345025265278177823 172693328017537897917266735)
  ·
    refine ⟨259039992026306846875900103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172693328017537897917266735 259039992026306846875900103)
    ·
      refine ⟨388559988039460270313850155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259039992026306846875900103 388559988039460270313850155)
      ·
        refine ⟨582839982059190405470775233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388559988039460270313850155 582839982059190405470775233)
        ·
          refine ⟨437129986544392804103081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582839982059190405470775233 437129986544392804103081425)
          ·
            refine ⟨327847489908294603077311069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437129986544392804103081425 327847489908294603077311069)
            ·
              refine ⟨122942808715610476153991651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327847489908294603077311069 122942808715610476153991651)
              ·
                refine ⟨184414213073415714230987477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122942808715610476153991651 184414213073415714230987477)
                ·
                  refine ⟨4322208118908180802288769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184414213073415714230987477 4322208118908180802288769)
                  ·
                    refine ⟨3241656089181135601716577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4322208118908180802288769 3241656089181135601716577)
                    ·
                      refine ⟨2431242066885851701287433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241656089181135601716577 2431242066885851701287433)
                      ·
                        rfl

theorem cell23_4734827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2, 2].length) (baseStart_4734827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734827 prefixEnd_4734827 := by exact prefixLift 4734827
  have htrace : WordTrace (prefixWord ++ tailWord_4734827) baseStart_4734827 baseEnd_4734827 := by
    simpa [prefixWord, tailWord_4734827, baseEnd_4734827] using wordTrace_append hprefix tailTrace_4734827
  have hstable : (prefixWord ++ tailWord_4734827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734827).length < 2 ^ (prefixWord ++ tailWord_4734827).sum := by decide
  have hdescent : baseEnd_4734827 < baseStart_4734827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734833 : List Nat := [1, 2, 2, 2, 1, 3, 12]
def baseStart_4734833 : Nat := 118140960795 + 4734833 * 2 ^ 59
def prefixEnd_4734833 : Nat := 4983230072969 + 3 ^ 40 * 4734833 * 2
def baseEnd_4734833 : Nat := 30015372194688625652005

theorem tailTrace_4734833 : CollatzResearch.WordTrace tailWord_4734833 prefixEnd_4734833 30015372194688625652005 := by
  unfold tailWord_4734833
  simp only [CollatzResearch.WordTrace]
  refine ⟨172693546855516160941985153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115129031237010773961323435 172693546855516160941985153)
  ·
    refine ⟨129520160141637120706488865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172693546855516160941985153 129520160141637120706488865)
    ·
      refine ⟨97140120106227840529866649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129520160141637120706488865 97140120106227840529866649)
      ·
        refine ⟨72855090079670880397399987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97140120106227840529866649 72855090079670880397399987)
        ·
          refine ⟨109282635119506320596099981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72855090079670880397399987 109282635119506320596099981)
          ·
            refine ⟨40980988169814870223537493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109282635119506320596099981 40980988169814870223537493)
            ·
              refine ⟨30015372194688625652005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40980988169814870223537493 30015372194688625652005)
              ·
                rfl

theorem cell23_4734833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 12].length) (baseStart_4734833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734833 prefixEnd_4734833 := by exact prefixLift 4734833
  have htrace : WordTrace (prefixWord ++ tailWord_4734833) baseStart_4734833 baseEnd_4734833 := by
    simpa [prefixWord, tailWord_4734833, baseEnd_4734833] using wordTrace_append hprefix tailTrace_4734833
  have hstable : (prefixWord ++ tailWord_4734833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734833).length < 2 ^ (prefixWord ++ tailWord_4734833).sum := by decide
  have hdescent : baseEnd_4734833 < baseStart_4734833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734837 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4734837 : Nat := 118140960795 + 4734837 * 2 ^ 59
def prefixEnd_4734837 : Nat := 4983230072969 + 3 ^ 40 * 4734837 * 2
def baseEnd_4734837 : Nat := 810415733897465554054129

theorem tailTrace_4734837 : CollatzResearch.WordTrace tailWord_4734837 prefixEnd_4734837 810415733897465554054129 := by
  unfold tailWord_4734837
  simp only [CollatzResearch.WordTrace]
  refine ⟨172693692747501669625130765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115129128498334446416753843 172693692747501669625130765)
  ·
    refine ⟨64760134780313126109424037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172693692747501669625130765 64760134780313126109424037)
    ·
      refine ⟨12142525271308711145517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64760134780313126109424037 12142525271308711145517007)
      ·
        refine ⟨18213787906963066718275511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12142525271308711145517007 18213787906963066718275511)
        ·
          refine ⟨27320681860444600077413267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18213787906963066718275511 27320681860444600077413267)
          ·
            refine ⟨40981022790666900116119901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27320681860444600077413267 40981022790666900116119901)
            ·
              refine ⟨15367883546500087543544963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40981022790666900116119901 15367883546500087543544963)
              ·
                refine ⟨23051825319750131315317445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15367883546500087543544963 23051825319750131315317445)
                ·
                  refine ⟨4322217247453149621622021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23051825319750131315317445 4322217247453149621622021)
                  ·
                    refine ⟨810415733897465554054129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322217247453149621622021 810415733897465554054129)
                    ·
                      rfl

theorem cell23_4734837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4734837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734837 prefixEnd_4734837 := by exact prefixLift 4734837
  have htrace : WordTrace (prefixWord ++ tailWord_4734837) baseStart_4734837 baseEnd_4734837 := by
    simpa [prefixWord, tailWord_4734837, baseEnd_4734837] using wordTrace_append hprefix tailTrace_4734837
  have hstable : (prefixWord ++ tailWord_4734837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734837).length < 2 ^ (prefixWord ++ tailWord_4734837).sum := by decide
  have hdescent : baseEnd_4734837 < baseStart_4734837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_4734843 : Nat := 118140960795 + 4734843 * 2 ^ 59
def prefixEnd_4734843 : Nat := 4983230072969 + 3 ^ 40 * 4734843 * 2
def baseEnd_4734843 : Nat := 2431250282576323638687359

theorem tailTrace_4734843 : CollatzResearch.WordTrace tailWord_4734843 prefixEnd_4734843 2431250282576323638687359 := by
  unfold tailWord_4734843
  simp only [CollatzResearch.WordTrace]
  refine ⟨172693911585479932649849183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115129274390319955099899455 172693911585479932649849183)
  ·
    refine ⟨259040867378219898974773775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172693911585479932649849183 259040867378219898974773775)
    ·
      refine ⟨388561301067329848462160663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259040867378219898974773775 388561301067329848462160663)
      ·
        refine ⟨582841951600994772693240995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388561301067329848462160663 582841951600994772693240995)
        ·
          refine ⟨874262927401492159039861493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582841951600994772693240995 874262927401492159039861493)
          ·
            refine ⟨81962149443889889909987015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 874262927401492159039861493 81962149443889889909987015)
            ·
              refine ⟨122943224165834834864980523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81962149443889889909987015 122943224165834834864980523)
              ·
                refine ⟨184414836248752252297470785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122943224165834834864980523 184414836248752252297470785)
                ·
                  refine ⟨138311127186564189223103089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184414836248752252297470785 138311127186564189223103089)
                  ·
                    refine ⟨103733345389923141917327317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138311127186564189223103089 103733345389923141917327317)
                    ·
                      refine ⟨2431250282576323638687359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103733345389923141917327317 2431250282576323638687359)
                      ·
                        rfl

theorem cell23_4734843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_4734843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734843 prefixEnd_4734843 := by exact prefixLift 4734843
  have htrace : WordTrace (prefixWord ++ tailWord_4734843) baseStart_4734843 baseEnd_4734843 := by
    simpa [prefixWord, tailWord_4734843, baseEnd_4734843] using wordTrace_append hprefix tailTrace_4734843
  have hstable : (prefixWord ++ tailWord_4734843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734843).length < 2 ^ (prefixWord ++ tailWord_4734843).sum := by decide
  have hdescent : baseEnd_4734843 < baseStart_4734843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734863 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 9]
def baseStart_4734863 : Nat := 118140960795 + 4734863 * 2 ^ 59
def prefixEnd_4734863 : Nat := 4983230072969 + 3 ^ 40 * 4734863 * 2
def baseEnd_4734863 : Nat := 810420184063137853479089

theorem tailTrace_4734863 : CollatzResearch.WordTrace tailWord_4734863 prefixEnd_4734863 810420184063137853479089 := by
  unfold tailWord_4734863
  simp only [CollatzResearch.WordTrace]
  refine ⟨172694641045407476065577243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115129760696938317377051495 172694641045407476065577243)
  ·
    refine ⟨259041961568111214098365865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172694641045407476065577243 259041961568111214098365865)
    ·
      refine ⟨194281471176083410573774399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259041961568111214098365865 194281471176083410573774399)
      ·
        refine ⟨291422206764125115860661599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194281471176083410573774399 291422206764125115860661599)
        ·
          refine ⟨437133310146187673790992399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291422206764125115860661599 437133310146187673790992399)
          ·
            refine ⟨655699965219281510686488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437133310146187673790992399 655699965219281510686488599)
            ·
              refine ⟨983549947828922266029732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655699965219281510686488599 983549947828922266029732899)
              ·
                refine ⟨1475324921743383399044599349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983549947828922266029732899 1475324921743383399044599349)
                ·
                  refine ⟨138311711413442193660431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1475324921743383399044599349 138311711413442193660431189)
                  ·
                    refine ⟨810420184063137853479089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138311711413442193660431189 810420184063137853479089)
                    ·
                      rfl

theorem cell23_4734863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_4734863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734863 prefixEnd_4734863 := by exact prefixLift 4734863
  have htrace : WordTrace (prefixWord ++ tailWord_4734863) baseStart_4734863 baseEnd_4734863 := by
    simpa [prefixWord, tailWord_4734863, baseEnd_4734863] using wordTrace_append hprefix tailTrace_4734863
  have hstable : (prefixWord ++ tailWord_4734863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734863).length < 2 ^ (prefixWord ++ tailWord_4734863).sum := by decide
  have hdescent : baseEnd_4734863 < baseStart_4734863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734938 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_4734938 : Nat := 118140960795 + 4734938 * 2 ^ 59
def prefixEnd_4734938 : Nat := 4983230072969 + 3 ^ 40 * 4734938 * 2
def baseEnd_4734938 : Nat := 2431299063238500766999423

theorem tailTrace_4734938 : CollatzResearch.WordTrace tailWord_4734938 prefixEnd_4734938 2431299063238500766999423 := by
  unfold tailWord_4734938
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174344130033940968639367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115131584346757175916371645 43174344130033940968639367)
  ·
    refine ⟨64761516195050911452959051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43174344130033940968639367 64761516195050911452959051)
    ·
      refine ⟨97142274292576367179438577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64761516195050911452959051 97142274292576367179438577)
      ·
        refine ⟨72856705719432275384578933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97142274292576367179438577 72856705719432275384578933)
        ·
          refine ⟨6830316161196775817304275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72856705719432275384578933 6830316161196775817304275)
          ·
            refine ⟨10245474241795163725956413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830316161196775817304275 10245474241795163725956413)
            ·
              refine ⟨3842052840673186397233655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10245474241795163725956413 3842052840673186397233655)
              ·
                refine ⟨5763079261009779595850483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842052840673186397233655 5763079261009779595850483)
                ·
                  refine ⟨8644618891514669393775725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763079261009779595850483 8644618891514669393775725)
                  ·
                    refine ⟨3241732084318001022665897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8644618891514669393775725 3241732084318001022665897)
                    ·
                      refine ⟨2431299063238500766999423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241732084318001022665897 2431299063238500766999423)
                      ·
                        rfl

theorem cell23_4734938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_4734938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734938 prefixEnd_4734938 := by exact prefixLift 4734938
  have htrace : WordTrace (prefixWord ++ tailWord_4734938) baseStart_4734938 baseEnd_4734938 := by
    simpa [prefixWord, tailWord_4734938, baseEnd_4734938] using wordTrace_append hprefix tailTrace_4734938
  have hstable : (prefixWord ++ tailWord_4734938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734938).length < 2 ^ (prefixWord ++ tailWord_4734938).sum := by decide
  have hdescent : baseEnd_4734938 < baseStart_4734938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734974 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_4734974 : Nat := 118140960795 + 4734974 * 2 ^ 59
def prefixEnd_4734974 : Nat := 4983230072969 + 3 ^ 40 * 4734974 * 2
def baseEnd_4734974 : Nat := 270146394282451402905473

theorem tailTrace_4734974 : CollatzResearch.WordTrace tailWord_4734974 prefixEnd_4734974 270146394282451402905473 := by
  unfold tailWord_4734974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21587336193500667752858497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115132459698670228015245317 21587336193500667752858497)
  ·
    refine ⟨16190502145125500814643873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21587336193500667752858497 16190502145125500814643873)
    ·
      refine ⟨12142876608844125610982905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16190502145125500814643873 12142876608844125610982905)
      ·
        refine ⟨9107157456633094208237179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12142876608844125610982905 9107157456633094208237179)
        ·
          refine ⟨13660736184949641312355769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9107157456633094208237179 13660736184949641312355769)
          ·
            refine ⟨10245552138712230984266827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13660736184949641312355769 10245552138712230984266827)
            ·
              refine ⟨15368328208068346476400241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10245552138712230984266827 15368328208068346476400241)
              ·
                refine ⟨11526246156051259857300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15368328208068346476400241 11526246156051259857300181)
                ·
                  refine ⟨270146394282451402905473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11526246156051259857300181 270146394282451402905473)
                  ·
                    rfl

theorem cell23_4734974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_4734974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734974 prefixEnd_4734974 := by exact prefixLift 4734974
  have htrace : WordTrace (prefixWord ++ tailWord_4734974) baseStart_4734974 baseEnd_4734974 := by
    simpa [prefixWord, tailWord_4734974, baseEnd_4734974] using wordTrace_append hprefix tailTrace_4734974
  have hstable : (prefixWord ++ tailWord_4734974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734974).length < 2 ^ (prefixWord ++ tailWord_4734974).sum := by decide
  have hdescent : baseEnd_4734974 < baseStart_4734974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4734989 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4734989 : Nat := 118140960795 + 4734989 * 2 ^ 59
def prefixEnd_4734989 : Nat := 4983230072969 + 3 ^ 40 * 4734989 * 2
def baseEnd_4734989 : Nat := 2431325250751880067461689

theorem tailTrace_4734989 : CollatzResearch.WordTrace tailWord_4734989 prefixEnd_4734989 2431325250751880067461689 := by
  unfold tailWord_4734989
  simp only [CollatzResearch.WordTrace]
  refine ⟨172699236642950999584664021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115132824428633999723109347 172699236642950999584664021)
  ·
    refine ⟨4047638358819164052765563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 172699236642950999584664021 4047638358819164052765563)
    ·
      refine ⟨6071457538228746079148345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047638358819164052765563 6071457538228746079148345)
      ·
        refine ⟨4553593153671559559361259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6071457538228746079148345 4553593153671559559361259)
        ·
          refine ⟨6830389730507339339041889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4553593153671559559361259 6830389730507339339041889)
          ·
            refine ⟨5122792297880504504281417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6830389730507339339041889 5122792297880504504281417)
            ·
              refine ⟨3842094223410378378211063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5122792297880504504281417 3842094223410378378211063)
              ·
                refine ⟨5763141335115567567316595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842094223410378378211063 5763141335115567567316595)
                ·
                  refine ⟨8644712002673351350974893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763141335115567567316595 8644712002673351350974893)
                  ·
                    refine ⟨3241767001002506756615585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8644712002673351350974893 3241767001002506756615585)
                    ·
                      refine ⟨2431325250751880067461689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241767001002506756615585 2431325250751880067461689)
                      ·
                        rfl

theorem cell23_4734989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4734989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4734989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4734989 prefixEnd_4734989 := by exact prefixLift 4734989
  have htrace : WordTrace (prefixWord ++ tailWord_4734989) baseStart_4734989 baseEnd_4734989 := by
    simpa [prefixWord, tailWord_4734989, baseEnd_4734989] using wordTrace_append hprefix tailTrace_4734989
  have hstable : (prefixWord ++ tailWord_4734989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4734989).length < 2 ^ (prefixWord ++ tailWord_4734989).sum := by decide
  have hdescent : baseEnd_4734989 < baseStart_4734989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4734989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735007 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4735007 : Nat := 118140960795 + 4735007 * 2 ^ 59
def prefixEnd_4735007 : Nat := 4983230072969 + 3 ^ 40 * 4735007 * 2
def baseEnd_4735007 : Nat := 2431334493403660997036605

theorem tailTrace_4735007 : CollatzResearch.WordTrace tailWord_4735007 prefixEnd_4735007 2431334493403660997036605 := by
  unfold tailWord_4735007
  simp only [CollatzResearch.WordTrace]
  refine ⟨172699893156885788658819275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115133262104590525772546183 172699893156885788658819275)
  ·
    refine ⟨259049839735328682988228913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172699893156885788658819275 259049839735328682988228913)
    ·
      refine ⟨194287379801496512241171685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259049839735328682988228913 194287379801496512241171685)
      ·
        refine ⟨36428883712780596045219691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194287379801496512241171685 36428883712780596045219691)
        ·
          refine ⟨54643325569170894067829537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36428883712780596045219691 54643325569170894067829537)
          ·
            refine ⟨40982494176878170550872153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54643325569170894067829537 40982494176878170550872153)
            ·
              refine ⟨30736870632658627913154115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40982494176878170550872153 30736870632658627913154115)
              ·
                refine ⟨46105305948987941869731173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30736870632658627913154115 46105305948987941869731173)
                ·
                  refine ⟨8644744865435239100574595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46105305948987941869731173 8644744865435239100574595)
                  ·
                    refine ⟨12967117298152858650861893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8644744865435239100574595 12967117298152858650861893)
                    ·
                      refine ⟨2431334493403660997036605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12967117298152858650861893 2431334493403660997036605)
                      ·
                        rfl

theorem cell23_4735007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4735007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735007 prefixEnd_4735007 := by exact prefixLift 4735007
  have htrace : WordTrace (prefixWord ++ tailWord_4735007) baseStart_4735007 baseEnd_4735007 := by
    simpa [prefixWord, tailWord_4735007, baseEnd_4735007] using wordTrace_append hprefix tailTrace_4735007
  have hstable : (prefixWord ++ tailWord_4735007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735007).length < 2 ^ (prefixWord ++ tailWord_4735007).sum := by decide
  have hdescent : baseEnd_4735007 < baseStart_4735007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735024 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2]
def baseStart_4735024 : Nat := 118140960795 + 4735024 * 2 ^ 59
def prefixEnd_4735024 : Nat := 4983230072969 + 3 ^ 40 * 4735024 * 2
def baseEnd_4735024 : Nat := 2431343222574787430524027

theorem tailTrace_4735024 : CollatzResearch.WordTrace tailWord_4735024 prefixEnd_4735024 2431343222574787430524027 := by
  unfold tailWord_4735024
  simp only [CollatzResearch.WordTrace]
  refine ⟨86350256598912100281094063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115133675465216133708125417 86350256598912100281094063)
  ·
    refine ⟨129525384898368150421641095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86350256598912100281094063 129525384898368150421641095)
    ·
      refine ⟨194288077347552225632461643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129525384898368150421641095 194288077347552225632461643)
      ·
        refine ⟨291432116021328338448692465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194288077347552225632461643 291432116021328338448692465)
        ·
          refine ⟨218574087015996253836519349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291432116021328338448692465 218574087015996253836519349)
          ·
            refine ⟨20491320657749648797173689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218574087015996253836519349 20491320657749648797173689)
            ·
              refine ⟨15368490493312236597880267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20491320657749648797173689 15368490493312236597880267)
              ·
                refine ⟨23052735739968354896820401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15368490493312236597880267 23052735739968354896820401)
                ·
                  refine ⟨17289551804976266172615301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23052735739968354896820401 17289551804976266172615301)
                  ·
                    refine ⟨3241790963433049907365369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17289551804976266172615301 3241790963433049907365369)
                    ·
                      refine ⟨2431343222574787430524027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241790963433049907365369 2431343222574787430524027)
                      ·
                        rfl

theorem cell23_4735024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2].length) (baseStart_4735024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735024 prefixEnd_4735024 := by exact prefixLift 4735024
  have htrace : WordTrace (prefixWord ++ tailWord_4735024) baseStart_4735024 baseEnd_4735024 := by
    simpa [prefixWord, tailWord_4735024, baseEnd_4735024] using wordTrace_append hprefix tailTrace_4735024
  have hstable : (prefixWord ++ tailWord_4735024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735024).length < 2 ^ (prefixWord ++ tailWord_4735024).sum := by decide
  have hdescent : baseEnd_4735024 < baseStart_4735024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735027 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3]
def baseStart_4735027 : Nat := 118140960795 + 4735027 * 2 ^ 59
def prefixEnd_4735027 : Nat := 4983230072969 + 3 ^ 40 * 4735027 * 2
def baseEnd_4735027 : Nat := 2431344763016750918786513

theorem tailTrace_4735027 : CollatzResearch.WordTrace tailWord_4735027 prefixEnd_4735027 2431344763016750918786513 := by
  unfold tailWord_4735027
  simp only [CollatzResearch.WordTrace]
  refine ⟨172700622616813332074547335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115133748411208888049698223 172700622616813332074547335)
  ·
    refine ⟨259050933925219998111821003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172700622616813332074547335 259050933925219998111821003)
    ·
      refine ⟨388576400887829997167731505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259050933925219998111821003 388576400887829997167731505)
      ·
        refine ⟨291432300665872497875798629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388576400887829997167731505 291432300665872497875798629)
        ·
          refine ⟨54643556374851093351712243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291432300665872497875798629 54643556374851093351712243)
          ·
            refine ⟨81965334562276640027568365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54643556374851093351712243 81965334562276640027568365)
            ·
              refine ⟨30737000460853740010338137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81965334562276640027568365 30737000460853740010338137)
              ·
                refine ⟨23052750345640305007753603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30737000460853740010338137 23052750345640305007753603)
                ·
                  refine ⟨34579125518460457511630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23052750345640305007753603 34579125518460457511630405)
                  ·
                    refine ⟨6483586034711335783430701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34579125518460457511630405 6483586034711335783430701)
                    ·
                      refine ⟨2431344763016750918786513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483586034711335783430701 2431344763016750918786513)
                      ·
                        rfl

theorem cell23_4735027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_4735027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735027 prefixEnd_4735027 := by exact prefixLift 4735027
  have htrace : WordTrace (prefixWord ++ tailWord_4735027) baseStart_4735027 baseEnd_4735027 := by
    simpa [prefixWord, tailWord_4735027, baseEnd_4735027] using wordTrace_append hprefix tailTrace_4735027
  have hstable : (prefixWord ++ tailWord_4735027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735027).length < 2 ^ (prefixWord ++ tailWord_4735027).sum := by decide
  have hdescent : baseEnd_4735027 < baseStart_4735027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735037 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4735037 : Nat := 118140960795 + 4735037 * 2 ^ 59
def prefixEnd_4735037 : Nat := 4983230072969 + 3 ^ 40 * 4735037 * 2
def baseEnd_4735037 : Nat := 2431349897823295879661467

theorem tailTrace_4735037 : CollatzResearch.WordTrace tailWord_4735037 prefixEnd_4735037 2431349897823295879661467 := by
  unfold tailWord_4735037
  simp only [CollatzResearch.WordTrace]
  refine ⟨172700987346777103782411365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115133991564518069188274243 172700987346777103782411365)
  ·
    refine ⟨32381435127520706959202131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172700987346777103782411365 32381435127520706959202131)
    ·
      refine ⟨48572152691281060438803197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32381435127520706959202131 48572152691281060438803197)
      ·
        refine ⟨18214557259230397664551199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48572152691281060438803197 18214557259230397664551199)
        ·
          refine ⟨27321835888845596496826799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18214557259230397664551199 27321835888845596496826799)
          ·
            refine ⟨40982753833268394745240199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27321835888845596496826799 40982753833268394745240199)
            ·
              refine ⟨61474130749902592117860299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40982753833268394745240199 61474130749902592117860299)
              ·
                refine ⟨92211196124853888176790449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61474130749902592117860299 92211196124853888176790449)
                ·
                  refine ⟨69158397093640416132592837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92211196124853888176790449 69158397093640416132592837)
                  ·
                    refine ⟨12967199455057578024861157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69158397093640416132592837 12967199455057578024861157)
                    ·
                      refine ⟨2431349897823295879661467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12967199455057578024861157 2431349897823295879661467)
                      ·
                        rfl

theorem cell23_4735037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4735037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735037 prefixEnd_4735037 := by exact prefixLift 4735037
  have htrace : WordTrace (prefixWord ++ tailWord_4735037) baseStart_4735037 baseEnd_4735037 := by
    simpa [prefixWord, tailWord_4735037, baseEnd_4735037] using wordTrace_append hprefix tailTrace_4735037
  have hstable : (prefixWord ++ tailWord_4735037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735037).length < 2 ^ (prefixWord ++ tailWord_4735037).sum := by decide
  have hdescent : baseEnd_4735037 < baseStart_4735037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735101 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_4735101 : Nat := 118140960795 + 4735101 * 2 ^ 59
def prefixEnd_4735101 : Nat := 4983230072969 + 3 ^ 40 * 4735101 * 2
def baseEnd_4735101 : Nat := 2431382760585183629261173

theorem tailTrace_4735101 : CollatzResearch.WordTrace tailWord_4735101 prefixEnd_4735101 2431382760585183629261173 := by
  unfold tailWord_4735101
  simp only [CollatzResearch.WordTrace]
  refine ⟨172703321618545242712741157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115135547745696828475160771 172703321618545242712741157)
  ·
    refine ⟨32381872803477233008638967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172703321618545242712741157 32381872803477233008638967)
    ·
      refine ⟨48572809205215849512958451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32381872803477233008638967 48572809205215849512958451)
      ·
        refine ⟨72859213807823774269437677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48572809205215849512958451 72859213807823774269437677)
        ·
          refine ⟨27322205177933915351039129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72859213807823774269437677 27322205177933915351039129)
          ·
            refine ⟨20491653883450436513279347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27322205177933915351039129 20491653883450436513279347)
            ·
              refine ⟨30737480825175654769919021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20491653883450436513279347 30737480825175654769919021)
              ·
                refine ⟨11526555309440870538719633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30737480825175654769919021 11526555309440870538719633)
                ·
                  refine ⟨8644916482080652904039725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11526555309440870538719633 8644916482080652904039725)
                  ·
                    refine ⟨3241843680780244839014897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8644916482080652904039725 3241843680780244839014897)
                    ·
                      refine ⟨2431382760585183629261173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241843680780244839014897 2431382760585183629261173)
                      ·
                        rfl

theorem cell23_4735101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_4735101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735101 prefixEnd_4735101 := by exact prefixLift 4735101
  have htrace : WordTrace (prefixWord ++ tailWord_4735101) baseStart_4735101 baseEnd_4735101 := by
    simpa [prefixWord, tailWord_4735101, baseEnd_4735101] using wordTrace_append hprefix tailTrace_4735101
  have hstable : (prefixWord ++ tailWord_4735101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735101).length < 2 ^ (prefixWord ++ tailWord_4735101).sum := by decide
  have hdescent : baseEnd_4735101 < baseStart_4735101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735107 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 6]
def baseStart_4735107 : Nat := 118140960795 + 4735107 * 2 ^ 59
def prefixEnd_4735107 : Nat := 4983230072969 + 3 ^ 40 * 4735107 * 2
def baseEnd_4735107 : Nat := 810461947156370201928715

theorem tailTrace_4735107 : CollatzResearch.WordTrace tailWord_4735107 prefixEnd_4735107 810461947156370201928715 := by
  unfold tailWord_4735107
  simp only [CollatzResearch.WordTrace]
  refine ⟨172703540456523505737459575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115135693637682337158306383 172703540456523505737459575)
  ·
    refine ⟨259055310684785258606189363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172703540456523505737459575 259055310684785258606189363)
    ·
      refine ⟨388582966027177887909284045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259055310684785258606189363 388582966027177887909284045)
      ·
        refine ⟨145718612260191707965981517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388582966027177887909284045 145718612260191707965981517)
        ·
          refine ⟨54644479597571890487243069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145718612260191707965981517 54644479597571890487243069)
          ·
            refine ⟨20491679849089458932716151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54644479597571890487243069 20491679849089458932716151)
            ·
              refine ⟨30737519773634188399074227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20491679849089458932716151 30737519773634188399074227)
              ·
                refine ⟨46106279660451282598611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30737519773634188399074227 46106279660451282598611341)
                ·
                  refine ⟨17289854872669230974479253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46106279660451282598611341 17289854872669230974479253)
                  ·
                    refine ⟨810461947156370201928715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17289854872669230974479253 810461947156370201928715)
                    ·
                      rfl

theorem cell23_4735107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_4735107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735107 prefixEnd_4735107 := by exact prefixLift 4735107
  have htrace : WordTrace (prefixWord ++ tailWord_4735107) baseStart_4735107 baseEnd_4735107 := by
    simpa [prefixWord, tailWord_4735107, baseEnd_4735107] using wordTrace_append hprefix tailTrace_4735107
  have hstable : (prefixWord ++ tailWord_4735107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735107).length < 2 ^ (prefixWord ++ tailWord_4735107).sum := by decide
  have hdescent : baseEnd_4735107 < baseStart_4735107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735108 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4735108 : Nat := 118140960795 + 4735108 * 2 ^ 59
def prefixEnd_4735108 : Nat := 4983230072969 + 3 ^ 40 * 4735108 * 2
def baseEnd_4735108 : Nat := 2431386354949765101873641

theorem tailTrace_4735108 : CollatzResearch.WordTrace tailWord_4735108 prefixEnd_4735108 2431386354949765101873641 := by
  unfold tailWord_4735108
  simp only [CollatzResearch.WordTrace]
  refine ⟨86351788464759941454122989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115135717953013255272163985 86351788464759941454122989)
  ·
    refine ⟨32381920674284978045296121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86351788464759941454122989 32381920674284978045296121)
    ·
      refine ⟨24286440505713733533972091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32381920674284978045296121 24286440505713733533972091)
      ·
        refine ⟨36429660758570600300958137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24286440505713733533972091 36429660758570600300958137)
        ·
          refine ⟨27322245568927950225718603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36429660758570600300958137 27322245568927950225718603)
          ·
            refine ⟨40983368353391925338577905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27322245568927950225718603 40983368353391925338577905)
            ·
              refine ⟨30737526265043944003933429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40983368353391925338577905 30737526265043944003933429)
              ·
                refine ⟨2881643087347869750368759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30737526265043944003933429 2881643087347869750368759)
                ·
                  refine ⟨4322464631021804625553139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881643087347869750368759 4322464631021804625553139)
                  ·
                    refine ⟨6483696946532706938329709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4322464631021804625553139 6483696946532706938329709)
                    ·
                      refine ⟨2431386354949765101873641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483696946532706938329709 2431386354949765101873641)
                      ·
                        rfl

theorem cell23_4735108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4735108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735108 prefixEnd_4735108 := by exact prefixLift 4735108
  have htrace : WordTrace (prefixWord ++ tailWord_4735108) baseStart_4735108 baseEnd_4735108 := by
    simpa [prefixWord, tailWord_4735108, baseEnd_4735108] using wordTrace_append hprefix tailTrace_4735108
  have hstable : (prefixWord ++ tailWord_4735108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735108).length < 2 ^ (prefixWord ++ tailWord_4735108).sum := by decide
  have hdescent : baseEnd_4735108 < baseStart_4735108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735154 : List Nat := [3, 2, 1, 1, 1, 3, 5, 7]
def baseStart_4735154 : Nat := 118140960795 + 4735154 * 2 ^ 59
def prefixEnd_4735154 : Nat := 4983230072969 + 3 ^ 40 * 4735154 * 2
def baseEnd_4735154 : Nat := 90052221298513774885127

theorem tailTrace_4735154 : CollatzResearch.WordTrace tailWord_4735154 prefixEnd_4735154 90052221298513774885127 := by
  unfold tailWord_4735154
  simp only [CollatzResearch.WordTrace]
  refine ⟨43176313671838308191105129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115136836458235488509613677 43176313671838308191105129)
  ·
    refine ⟨32382235253878731143328847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43176313671838308191105129 32382235253878731143328847)
    ·
      refine ⟨48573352880818096714993271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32382235253878731143328847 48573352880818096714993271)
      ·
        refine ⟨72860029321227145072489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48573352880818096714993271 72860029321227145072489907)
        ·
          refine ⟨109290043981840717608734861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72860029321227145072489907 109290043981840717608734861)
          ·
            refine ⟨40983766493190269103275573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109290043981840717608734861 40983766493190269103275573)
            ·
              refine ⟨3842228108736587728432085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40983766493190269103275573 3842228108736587728432085)
              ·
                refine ⟨90052221298513774885127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3842228108736587728432085 90052221298513774885127)
                ·
                  rfl

theorem cell23_4735154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_4735154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735154 prefixEnd_4735154 := by exact prefixLift 4735154
  have htrace : WordTrace (prefixWord ++ tailWord_4735154) baseStart_4735154 baseEnd_4735154 := by
    simpa [prefixWord, tailWord_4735154, baseEnd_4735154] using wordTrace_append hprefix tailTrace_4735154
  have hstable : (prefixWord ++ tailWord_4735154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735154).length < 2 ^ (prefixWord ++ tailWord_4735154).sum := by decide
  have hdescent : baseEnd_4735154 < baseStart_4735154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735168 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3]
def baseStart_4735168 : Nat := 118140960795 + 4735168 * 2 ^ 59
def prefixEnd_4735168 : Nat := 4983230072969 + 3 ^ 40 * 4735168 * 2
def baseEnd_4735168 : Nat := 2431417163789034867123365

theorem tailTrace_4735168 : CollatzResearch.WordTrace tailWord_4735168 prefixEnd_4735168 2431417163789034867123365 := by
  unfold tailWord_4735168
  simp only [CollatzResearch.WordTrace]
  refine ⟨86352882654651256577715079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115137176872868342103620105 86352882654651256577715079)
  ·
    refine ⟨129529323981976884866572619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86352882654651256577715079 129529323981976884866572619)
    ·
      refine ⟨194293985972965327299858929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129529323981976884866572619 194293985972965327299858929)
      ·
        refine ⟨145720489479723995474894197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194293985972965327299858929 145720489479723995474894197)
        ·
          refine ⟨13661295888724124575771331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145720489479723995474894197 13661295888724124575771331)
          ·
            refine ⟨20491943833086186863656997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13661295888724124575771331 20491943833086186863656997)
            ·
              refine ⟨3842239468703660036935687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20491943833086186863656997 3842239468703660036935687)
              ·
                refine ⟨5763359203055490055403531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842239468703660036935687 5763359203055490055403531)
                ·
                  refine ⟨8645038804583235083105297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763359203055490055403531 8645038804583235083105297)
                  ·
                    refine ⟨6483779103437426312328973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8645038804583235083105297 6483779103437426312328973)
                    ·
                      refine ⟨2431417163789034867123365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6483779103437426312328973 2431417163789034867123365)
                      ·
                        rfl

theorem cell23_4735168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_4735168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735168 prefixEnd_4735168 := by exact prefixLift 4735168
  have htrace : WordTrace (prefixWord ++ tailWord_4735168) baseStart_4735168 baseEnd_4735168 := by
    simpa [prefixWord, tailWord_4735168, baseEnd_4735168] using wordTrace_append hprefix tailTrace_4735168
  have hstable : (prefixWord ++ tailWord_4735168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735168).length < 2 ^ (prefixWord ++ tailWord_4735168).sum := by decide
  have hdescent : baseEnd_4735168 < baseStart_4735168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735177 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_4735177 : Nat := 118140960795 + 4735177 * 2 ^ 59
def prefixEnd_4735177 : Nat := 4983230072969 + 3 ^ 40 * 4735177 * 2
def baseEnd_4735177 : Nat := 2431421785114925331910823

theorem tailTrace_4735177 : CollatzResearch.WordTrace tailWord_4735177 prefixEnd_4735177 2431421785114925331910823 := by
  unfold tailWord_4735177
  simp only [CollatzResearch.WordTrace]
  refine ⟨172706093566269907692507785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115137395710846605128338523 172706093566269907692507785)
  ·
    refine ⟨129529570174702430769380839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172706093566269907692507785 129529570174702430769380839)
    ·
      refine ⟨194294355262053646154071259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129529570174702430769380839 194294355262053646154071259)
      ·
        refine ⟨291441532893080469231106889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194294355262053646154071259 291441532893080469231106889)
        ·
          refine ⟨218581149669810351923330167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291441532893080469231106889 218581149669810351923330167)
          ·
            refine ⟨327871724504715527884995251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218581149669810351923330167 327871724504715527884995251)
            ·
              refine ⟨491807586757073291827492877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327871724504715527884995251 491807586757073291827492877)
              ·
                refine ⟨184427845033902484435309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491807586757073291827492877 184427845033902484435309829)
                ·
                  refine ⟨34580220943856715831620593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184427845033902484435309829 34580220943856715831620593)
                  ·
                    refine ⟨25935165707892536873715445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34580220943856715831620593 25935165707892536873715445)
                    ·
                      refine ⟨2431421785114925331910823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25935165707892536873715445 2431421785114925331910823)
                      ·
                        rfl

theorem cell23_4735177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_4735177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735177 prefixEnd_4735177 := by exact prefixLift 4735177
  have htrace : WordTrace (prefixWord ++ tailWord_4735177) baseStart_4735177 baseEnd_4735177 := by
    simpa [prefixWord, tailWord_4735177, baseEnd_4735177] using wordTrace_append hprefix tailTrace_4735177
  have hstable : (prefixWord ++ tailWord_4735177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735177).length < 2 ^ (prefixWord ++ tailWord_4735177).sum := by decide
  have hdescent : baseEnd_4735177 < baseStart_4735177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735208 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4735208 : Nat := 118140960795 + 4735208 * 2 ^ 59
def prefixEnd_4735208 : Nat := 4983230072969 + 3 ^ 40 * 4735208 * 2
def baseEnd_4735208 : Nat := 2431437703015214710623181

theorem tailTrace_4735208 : CollatzResearch.WordTrace tailWord_4735208 prefixEnd_4735208 2431437703015214710623181 := by
  unfold tailWord_4735208
  simp only [CollatzResearch.WordTrace]
  refine ⟨86353612114578799993443139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115138149486105066657924185 86353612114578799993443139)
  ·
    refine ⟨129530418171868199990164709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86353612114578799993443139 129530418171868199990164709)
    ·
      refine ⟨24286953407225287498155883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129530418171868199990164709 24286953407225287498155883)
      ·
        refine ⟨36430430110837931247233825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24286953407225287498155883 36430430110837931247233825)
        ·
          refine ⟨27322822583128448435425369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36430430110837931247233825 27322822583128448435425369)
          ·
            refine ⟨20492116937346336326569027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27322822583128448435425369 20492116937346336326569027)
            ·
              refine ⟨30738175406019504489853541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20492116937346336326569027 30738175406019504489853541)
              ·
                refine ⟨5763407888628657091847539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30738175406019504489853541 5763407888628657091847539)
                ·
                  refine ⟨8645111832942985637771309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763407888628657091847539 8645111832942985637771309)
                  ·
                    refine ⟨3241916937353619614164241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8645111832942985637771309 3241916937353619614164241)
                    ·
                      refine ⟨2431437703015214710623181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241916937353619614164241 2431437703015214710623181)
                      ·
                        rfl

theorem cell23_4735208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4735208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735208 prefixEnd_4735208 := by exact prefixLift 4735208
  have htrace : WordTrace (prefixWord ++ tailWord_4735208) baseStart_4735208 baseEnd_4735208 := by
    simpa [prefixWord, tailWord_4735208, baseEnd_4735208] using wordTrace_append hprefix tailTrace_4735208
  have hstable : (prefixWord ++ tailWord_4735208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735208).length < 2 ^ (prefixWord ++ tailWord_4735208).sum := by decide
  have hdescent : baseEnd_4735208 < baseStart_4735208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735255 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4735255 : Nat := 118140960795 + 4735255 * 2 ^ 59
def prefixEnd_4735255 : Nat := 4983230072969 + 3 ^ 40 * 4735255 * 2
def baseEnd_4735255 : Nat := 2431461836605976026735465

theorem tailTrace_4735255 : CollatzResearch.WordTrace tailWord_4735255 prefixEnd_4735255 2431461836605976026735465 := by
  unfold tailWord_4735255
  simp only [CollatzResearch.WordTrace]
  refine ⟨172708938459987327013847219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115139292306658218009231479 172708938459987327013847219)
  ·
    refine ⟨259063407689980990520770829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172708938459987327013847219 259063407689980990520770829)
    ·
      refine ⟨97148777883742871445289061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259063407689980990520770829 97148777883742871445289061)
      ·
        refine ⟨18215395853201788395991699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97148777883742871445289061 18215395853201788395991699)
        ·
          refine ⟨27323093779802682593987549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18215395853201788395991699 27323093779802682593987549)
          ·
            refine ⟨10246160167426005972745331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27323093779802682593987549 10246160167426005972745331)
            ·
              refine ⟨15369240251139008959117997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10246160167426005972745331 15369240251139008959117997)
              ·
                refine ⟨5763465094177128359669249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15369240251139008959117997 5763465094177128359669249)
                ·
                  refine ⟨4322598820632846269751937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5763465094177128359669249 4322598820632846269751937)
                  ·
                    refine ⟨3241949115474634702313953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4322598820632846269751937 3241949115474634702313953)
                    ·
                      refine ⟨2431461836605976026735465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3241949115474634702313953 2431461836605976026735465)
                      ·
                        rfl

theorem cell23_4735255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4735255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735255 prefixEnd_4735255 := by exact prefixLift 4735255
  have htrace : WordTrace (prefixWord ++ tailWord_4735255) baseStart_4735255 baseEnd_4735255 := by
    simpa [prefixWord, tailWord_4735255, baseEnd_4735255] using wordTrace_append hprefix tailTrace_4735255
  have hstable : (prefixWord ++ tailWord_4735255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735255).length < 2 ^ (prefixWord ++ tailWord_4735255).sum := by decide
  have hdescent : baseEnd_4735255 < baseStart_4735255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735331 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4735331 : Nat := 118140960795 + 4735331 * 2 ^ 59
def prefixEnd_4735331 : Nat := 4983230072969 + 3 ^ 40 * 4735331 * 2
def baseEnd_4735331 : Nat := 2431500861135717729385115

theorem tailTrace_4735331 : CollatzResearch.WordTrace tailWord_4735331 prefixEnd_4735331 2431500861135717729385115 := by
  unfold tailWord_4735331
  simp only [CollatzResearch.WordTrace]
  refine ⟨172711710407711991993613847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115141140271807994662409231 172711710407711991993613847)
  ·
    refine ⟨259067565611567987990420771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172711710407711991993613847 259067565611567987990420771)
    ·
      refine ⟨388601348417351981985631157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259067565611567987990420771 388601348417351981985631157)
      ·
        refine ⟨36431376414126748311152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 388601348417351981985631157 36431376414126748311152921)
        ·
          refine ⟨27323532310595061233364691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36431376414126748311152921 27323532310595061233364691)
          ·
            refine ⟨40985298465892591850047037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27323532310595061233364691 40985298465892591850047037)
            ·
              refine ⟨15369486924709721943767639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40985298465892591850047037 15369486924709721943767639)
              ·
                refine ⟨23054230387064582915651459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15369486924709721943767639 23054230387064582915651459)
                ·
                  refine ⟨34581345580596874373477189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23054230387064582915651459 34581345580596874373477189)
                  ·
                    refine ⟨6484002296361913945026973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34581345580596874373477189 6484002296361913945026973)
                    ·
                      refine ⟨2431500861135717729385115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6484002296361913945026973 2431500861135717729385115)
                      ·
                        rfl

theorem cell23_4735331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4735331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735331 prefixEnd_4735331 := by exact prefixLift 4735331
  have htrace : WordTrace (prefixWord ++ tailWord_4735331) baseStart_4735331 baseEnd_4735331 := by
    simpa [prefixWord, tailWord_4735331, baseEnd_4735331] using wordTrace_append hprefix tailTrace_4735331
  have hstable : (prefixWord ++ tailWord_4735331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735331).length < 2 ^ (prefixWord ++ tailWord_4735331).sum := by decide
  have hdescent : baseEnd_4735331 < baseStart_4735331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735368 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 6]
def baseStart_4735368 : Nat := 118140960795 + 4735368 * 2 ^ 59
def prefixEnd_4735368 : Nat := 4983230072969 + 3 ^ 40 * 4735368 * 2
def baseEnd_4735368 : Nat := 270168873324437120513605

theorem tailTrace_4735368 : CollatzResearch.WordTrace tailWord_4735368 prefixEnd_4735368 270168873324437120513605 := by
  unfold tailWord_4735368
  simp only [CollatzResearch.WordTrace]
  refine ⟨86356529954288973656355379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115142039939051964875140505 86356529954288973656355379)
  ·
    refine ⟨129534794931433460484533069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86356529954288973656355379 129534794931433460484533069)
    ·
      refine ⟨48575548099287547681699901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129534794931433460484533069 48575548099287547681699901)
      ·
        refine ⟨18215830537232830380637463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48575548099287547681699901 18215830537232830380637463)
        ·
          refine ⟨27323745805849245570956195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18215830537232830380637463 27323745805849245570956195)
          ·
            refine ⟨40985618708773868356434293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27323745805849245570956195 40985618708773868356434293)
            ·
              refine ⟨3842401753947550158415715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40985618708773868356434293 3842401753947550158415715)
              ·
                refine ⟨5763602630921325237623573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842401753947550158415715 5763602630921325237623573)
                ·
                  refine ⟨270168873324437120513605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5763602630921325237623573 270168873324437120513605)
                  ·
                    rfl

theorem cell23_4735368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_4735368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735368 prefixEnd_4735368 := by exact prefixLift 4735368
  have htrace : WordTrace (prefixWord ++ tailWord_4735368) baseStart_4735368 baseEnd_4735368 := by
    simpa [prefixWord, tailWord_4735368, baseEnd_4735368] using wordTrace_append hprefix tailTrace_4735368
  have hstable : (prefixWord ++ tailWord_4735368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735368).length < 2 ^ (prefixWord ++ tailWord_4735368).sum := by decide
  have hdescent : baseEnd_4735368 < baseStart_4735368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735389 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_4735389 : Nat := 118140960795 + 4735389 * 2 ^ 59
def prefixEnd_4735389 : Nat := 4983230072969 + 3 ^ 40 * 4735389 * 2
def baseEnd_4735389 : Nat := 810510214337892834153283

theorem tailTrace_4735389 : CollatzResearch.WordTrace tailWord_4735389 prefixEnd_4735389 810510214337892834153283 := by
  unfold tailWord_4735389
  simp only [CollatzResearch.WordTrace]
  refine ⟨172713825841501867899225221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115142550561001245266150147 172713825841501867899225221)
  ·
    refine ⟨32383842345281600231104729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172713825841501867899225221 32383842345281600231104729)
    ·
      refine ⟨24287881758961200173328547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32383842345281600231104729 24287881758961200173328547)
      ·
        refine ⟨36431822638441800259992821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24287881758961200173328547 36431822638441800259992821)
        ·
          refine ⟨3415483372353918774374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36431822638441800259992821 3415483372353918774374327)
          ·
            refine ⟨5123225058530878161561491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415483372353918774374327 5123225058530878161561491)
            ·
              refine ⟨7684837587796317242342237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123225058530878161561491 7684837587796317242342237)
              ·
                refine ⟨2881814095423618965878339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7684837587796317242342237 2881814095423618965878339)
                ·
                  refine ⟨4322721143135428448817509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881814095423618965878339 4322721143135428448817509)
                  ·
                    refine ⟨810510214337892834153283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322721143135428448817509 810510214337892834153283)
                    ·
                      rfl

theorem cell23_4735389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_4735389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735389 prefixEnd_4735389 := by exact prefixLift 4735389
  have htrace : WordTrace (prefixWord ++ tailWord_4735389) baseStart_4735389 baseEnd_4735389 := by
    simpa [prefixWord, tailWord_4735389, baseEnd_4735389] using wordTrace_append hprefix tailTrace_4735389
  have hstable : (prefixWord ++ tailWord_4735389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735389).length < 2 ^ (prefixWord ++ tailWord_4735389).sum := by decide
  have hdescent : baseEnd_4735389 < baseStart_4735389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735431 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_4735431 : Nat := 118140960795 + 4735431 * 2 ^ 59
def prefixEnd_4735431 : Nat := 4983230072969 + 3 ^ 40 * 4735431 * 2
def baseEnd_4735431 : Nat := 2431552209201167338134655

theorem tailTrace_4735431 : CollatzResearch.WordTrace tailWord_4735431 prefixEnd_4735431 2431552209201167338134655 := by
  unfold tailWord_4735431
  simp only [CollatzResearch.WordTrace]
  refine ⟨172715357707349709072254147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115143571804899806048169431 172715357707349709072254147)
  ·
    refine ⟨259073036561024563608381221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172715357707349709072254147 259073036561024563608381221)
    ·
      refine ⟨48576194355192105676571479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259073036561024563608381221 48576194355192105676571479)
      ·
        refine ⟨72864291532788158514857219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48576194355192105676571479 72864291532788158514857219)
        ·
          refine ⟨109296437299182237772285829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72864291532788158514857219 109296437299182237772285829)
          ·
            refine ⟨20493081993596669582303593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109296437299182237772285829 20493081993596669582303593)
            ·
              refine ⟨15369811495197502186727695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20493081993596669582303593 15369811495197502186727695)
              ·
                refine ⟨23054717242796253280091543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15369811495197502186727695 23054717242796253280091543)
                ·
                  refine ⟨34582075864194379920137315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23054717242796253280091543 34582075864194379920137315)
                  ·
                    refine ⟨51873113796291569880205973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34582075864194379920137315 51873113796291569880205973)
                    ·
                      refine ⟨2431552209201167338134655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51873113796291569880205973 2431552209201167338134655)
                      ·
                        rfl

theorem cell23_4735431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_4735431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735431 prefixEnd_4735431 := by exact prefixLift 4735431
  have htrace : WordTrace (prefixWord ++ tailWord_4735431) baseStart_4735431 baseEnd_4735431 := by
    simpa [prefixWord, tailWord_4735431, baseEnd_4735431] using wordTrace_append hprefix tailTrace_4735431
  have hstable : (prefixWord ++ tailWord_4735431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735431).length < 2 ^ (prefixWord ++ tailWord_4735431).sum := by decide
  have hdescent : baseEnd_4735431 < baseStart_4735431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735458 : List Nat := [3, 3, 3, 2, 12]
def baseStart_4735458 : Nat := 118140960795 + 4735458 * 2 ^ 59
def prefixEnd_4735458 : Nat := 4983230072969 + 3 ^ 40 * 4735458 * 2
def baseEnd_4735458 : Nat := 3335481581863976313439

theorem tailTrace_4735458 : CollatzResearch.WordTrace tailWord_4735458 prefixEnd_4735458 3335481581863976313439 := by
  unfold tailWord_4735458
  simp only [CollatzResearch.WordTrace]
  refine ⟨43179085619562973170871757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115144228318834595122324685 43179085619562973170871757)
  ·
    refine ⟨16192157107336114939076909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43179085619562973170871757 16192157107336114939076909)
    ·
      refine ⟨6072058915251043102153841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16192157107336114939076909 6072058915251043102153841)
      ·
        refine ⟨4554044186438282326615381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6072058915251043102153841 4554044186438282326615381)
        ·
          refine ⟨3335481581863976313439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4554044186438282326615381 3335481581863976313439)
          ·
            rfl

theorem cell23_4735458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 12].length) (baseStart_4735458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735458 prefixEnd_4735458 := by exact prefixLift 4735458
  have htrace : WordTrace (prefixWord ++ tailWord_4735458) baseStart_4735458 baseEnd_4735458 := by
    simpa [prefixWord, tailWord_4735458, baseEnd_4735458] using wordTrace_append hprefix tailTrace_4735458
  have hstable : (prefixWord ++ tailWord_4735458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735458).length < 2 ^ (prefixWord ++ tailWord_4735458).sum := by decide
  have hdescent : baseEnd_4735458 < baseStart_4735458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735485 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_4735485 : Nat := 118140960795 + 4735485 * 2 ^ 59
def prefixEnd_4735485 : Nat := 4983230072969 + 3 ^ 40 * 4735485 * 2
def baseEnd_4735485 : Nat := 2431579937156510126859407

theorem tailTrace_4735485 : CollatzResearch.WordTrace tailWord_4735485 prefixEnd_4735485 2431579937156510126859407 := by
  unfold tailWord_4735485
  simp only [CollatzResearch.WordTrace]
  refine ⟨172717327249154076294719909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115144884832769384196479939 172717327249154076294719909)
  ·
    refine ⟨32384498859216389305259983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172717327249154076294719909 32384498859216389305259983)
    ·
      refine ⟨48576748288824583957889975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32384498859216389305259983 48576748288824583957889975)
      ·
        refine ⟨72865122433236875936834963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48576748288824583957889975 72865122433236875936834963)
        ·
          refine ⟨109297683649855313905252445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72865122433236875936834963 109297683649855313905252445)
          ·
            refine ⟨40986631368695742714469667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109297683649855313905252445 40986631368695742714469667)
            ·
              refine ⟨61479947053043614071704501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40986631368695742714469667 61479947053043614071704501)
              ·
                refine ⟨5763745036222838819222297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61479947053043614071704501 5763745036222838819222297)
                ·
                  refine ⟨4322808777167129114416723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5763745036222838819222297 4322808777167129114416723)
                  ·
                    refine ⟨6484213165750693671625085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4322808777167129114416723 6484213165750693671625085)
                    ·
                      refine ⟨2431579937156510126859407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6484213165750693671625085 2431579937156510126859407)
                      ·
                        rfl

theorem cell23_4735485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_4735485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735485 prefixEnd_4735485 := by exact prefixLift 4735485
  have htrace : WordTrace (prefixWord ++ tailWord_4735485) baseStart_4735485 baseEnd_4735485 := by
    simpa [prefixWord, tailWord_4735485, baseEnd_4735485] using wordTrace_append hprefix tailTrace_4735485
  have hstable : (prefixWord ++ tailWord_4735485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735485).length < 2 ^ (prefixWord ++ tailWord_4735485).sum := by decide
  have hdescent : baseEnd_4735485 < baseStart_4735485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735491 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4735491 : Nat := 118140960795 + 4735491 * 2 ^ 59
def prefixEnd_4735491 : Nat := 4983230072969 + 3 ^ 40 * 4735491 * 2
def baseEnd_4735491 : Nat := 2431583018040437103384379

theorem tailTrace_4735491 : CollatzResearch.WordTrace tailWord_4735491 prefixEnd_4735491 2431583018040437103384379 := by
  unfold tailWord_4735491
  simp only [CollatzResearch.WordTrace]
  refine ⟨172717546087132339319438327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115145030724754892879625551 172717546087132339319438327)
  ·
    refine ⟨259076319130698508979157491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172717546087132339319438327 259076319130698508979157491)
    ·
      refine ⟨388614478696047763468736237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259076319130698508979157491 388614478696047763468736237)
      ·
        refine ⟨145730429511017911300776089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388614478696047763468736237 145730429511017911300776089)
        ·
          refine ⟨109297822133263433475582067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145730429511017911300776089 109297822133263433475582067)
          ·
            refine ⟨163946733199895150213373101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109297822133263433475582067 163946733199895150213373101)
            ·
              refine ⟨61480024949960681330014913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163946733199895150213373101 61480024949960681330014913)
              ·
                refine ⟨46110018712470510997511185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61480024949960681330014913 46110018712470510997511185)
                ·
                  refine ⟨34582514034352883248133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46110018712470510997511185 34582514034352883248133389)
                  ·
                    refine ⟨12968442762882331218050021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34582514034352883248133389 12968442762882331218050021)
                    ·
                      refine ⟨2431583018040437103384379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12968442762882331218050021 2431583018040437103384379)
                      ·
                        rfl

theorem cell23_4735491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4735491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735491 prefixEnd_4735491 := by exact prefixLift 4735491
  have htrace : WordTrace (prefixWord ++ tailWord_4735491) baseStart_4735491 baseEnd_4735491 := by
    simpa [prefixWord, tailWord_4735491, baseEnd_4735491] using wordTrace_append hprefix tailTrace_4735491
  have hstable : (prefixWord ++ tailWord_4735491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735491).length < 2 ^ (prefixWord ++ tailWord_4735491).sum := by decide
  have hdescent : baseEnd_4735491 < baseStart_4735491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735512 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_4735512 : Nat := 118140960795 + 4735512 * 2 ^ 59
def prefixEnd_4735512 : Nat := 4983230072969 + 3 ^ 40 * 4735512 * 2
def baseEnd_4735512 : Nat := 2431593801134181521221783

theorem tailTrace_4735512 : CollatzResearch.WordTrace tailWord_4735512 prefixEnd_4735512 2431593801134181521221783 := by
  unfold tailWord_4735512
  simp only [CollatzResearch.WordTrace]
  refine ⟨86359156010028129952976395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115145541346704173270635193 86359156010028129952976395)
  ·
    refine ⟨129538734015042194929464593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86359156010028129952976395 129538734015042194929464593)
    ·
      refine ⟨97154050511281646197098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129538734015042194929464593 97154050511281646197098445)
      ·
        refine ⟨36432768941730617323911917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97154050511281646197098445 36432768941730617323911917)
        ·
          refine ⟨13662288353148981496466969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36432768941730617323911917 13662288353148981496466969)
          ·
            refine ⟨10246716264861736122350227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13662288353148981496466969 10246716264861736122350227)
            ·
              refine ⟨15370074397292604183525341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10246716264861736122350227 15370074397292604183525341)
              ·
                refine ⟨5763777898984726568822003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15370074397292604183525341 5763777898984726568822003)
                ·
                  refine ⟨8645666848477089853233005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763777898984726568822003 8645666848477089853233005)
                  ·
                    refine ⟨3242125068178908694962377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8645666848477089853233005 3242125068178908694962377)
                    ·
                      refine ⟨2431593801134181521221783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242125068178908694962377 2431593801134181521221783)
                      ·
                        rfl

theorem cell23_4735512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_4735512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735512 prefixEnd_4735512 := by exact prefixLift 4735512
  have htrace : WordTrace (prefixWord ++ tailWord_4735512) baseStart_4735512 baseEnd_4735512 := by
    simpa [prefixWord, tailWord_4735512, baseEnd_4735512] using wordTrace_append hprefix tailTrace_4735512
  have hstable : (prefixWord ++ tailWord_4735512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735512).length < 2 ^ (prefixWord ++ tailWord_4735512).sum := by decide
  have hdescent : baseEnd_4735512 < baseStart_4735512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735538 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_4735538 : Nat := 118140960795 + 4735538 * 2 ^ 59
def prefixEnd_4735538 : Nat := 4983230072969 + 3 ^ 40 * 4735538 * 2
def baseEnd_4735538 : Nat := 2431607151631198419496663

theorem tailTrace_4735538 : CollatzResearch.WordTrace tailWord_4735538 prefixEnd_4735538 2431607151631198419496663 := by
  unfold tailWord_4735538
  simp only [CollatzResearch.WordTrace]
  refine ⟨43179815079490516586599817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115146173545308044230932845 43179815079490516586599817)
  ·
    refine ⟨32384861309617887439949863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43179815079490516586599817 32384861309617887439949863)
    ·
      refine ⟨48577291964426831159924795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32384861309617887439949863 48577291964426831159924795)
      ·
        refine ⟨72865937946640246739887193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48577291964426831159924795 72865937946640246739887193)
        ·
          refine ⟨54649453459980185054915395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72865937946640246739887193 54649453459980185054915395)
          ·
            refine ⟨81974180189970277582373093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54649453459980185054915395 81974180189970277582373093)
            ·
              refine ⟨15370158785619427046694955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81974180189970277582373093 15370158785619427046694955)
              ·
                refine ⟨23055238178429140570042433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15370158785619427046694955 23055238178429140570042433)
                ·
                  refine ⟨17291428633821855427531825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23055238178429140570042433 17291428633821855427531825)
                  ·
                    refine ⟨12968571475366391570648869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17291428633821855427531825 12968571475366391570648869)
                    ·
                      refine ⟨2431607151631198419496663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12968571475366391570648869 2431607151631198419496663)
                      ·
                        rfl

theorem cell23_4735538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_4735538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735538 prefixEnd_4735538 := by exact prefixLift 4735538
  have htrace : WordTrace (prefixWord ++ tailWord_4735538) baseStart_4735538 baseEnd_4735538 := by
    simpa [prefixWord, tailWord_4735538, baseEnd_4735538] using wordTrace_append hprefix tailTrace_4735538
  have hstable : (prefixWord ++ tailWord_4735538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735538).length < 2 ^ (prefixWord ++ tailWord_4735538).sum := by decide
  have hdescent : baseEnd_4735538 < baseStart_4735538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735548 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 7]
def baseStart_4735548 : Nat := 118140960795 + 4735548 * 2 ^ 59
def prefixEnd_4735548 : Nat := 4983230072969 + 3 ^ 40 * 4735548 * 2
def baseEnd_4735548 : Nat := 270179142937527042263513

theorem tailTrace_4735548 : CollatzResearch.WordTrace tailWord_4735548 prefixEnd_4735548 270179142937527042263513 := by
  unfold tailWord_4735548
  simp only [CollatzResearch.WordTrace]
  refine ⟨86359812523962919027131649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115146416698617225369508865 86359812523962919027131649)
  ·
    refine ⟨64769859392972189270348737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86359812523962919027131649 64769859392972189270348737)
    ·
      refine ⟨48577394544729141952761553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64769859392972189270348737 48577394544729141952761553)
      ·
        refine ⟨36433045908546856464571165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48577394544729141952761553 36433045908546856464571165)
        ·
          refine ⟨13662392215705071174214187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36433045908546856464571165 13662392215705071174214187)
          ·
            refine ⟨20493588323557606761321281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13662392215705071174214187 20493588323557606761321281)
            ·
              refine ⟨15370191242668205070990961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20493588323557606761321281 15370191242668205070990961)
              ·
                refine ⟨11527643432001153803243221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15370191242668205070990961 11527643432001153803243221)
                ·
                  refine ⟨270179142937527042263513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11527643432001153803243221 270179142937527042263513)
                  ·
                    rfl

theorem cell23_4735548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_4735548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735548 prefixEnd_4735548 := by exact prefixLift 4735548
  have htrace : WordTrace (prefixWord ++ tailWord_4735548) baseStart_4735548 baseEnd_4735548 := by
    simpa [prefixWord, tailWord_4735548, baseEnd_4735548] using wordTrace_append hprefix tailTrace_4735548
  have hstable : (prefixWord ++ tailWord_4735548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735548).length < 2 ^ (prefixWord ++ tailWord_4735548).sum := by decide
  have hdescent : baseEnd_4735548 < baseStart_4735548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735588 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_4735588 : Nat := 118140960795 + 4735588 * 2 ^ 59
def prefixEnd_4735588 : Nat := 4983230072969 + 3 ^ 40 * 4735588 * 2
def baseEnd_4735588 : Nat := 2431632825663923223871433

theorem tailTrace_4735588 : CollatzResearch.WordTrace tailWord_4735588 prefixEnd_4735588 2431632825663923223871433 := by
  unfold tailWord_4735588
  simp only [CollatzResearch.WordTrace]
  refine ⟨86360541983890462442859709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115147389311853949923812945 86360541983890462442859709)
  ·
    refine ⟨32385203243958923416072391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86360541983890462442859709 32385203243958923416072391)
    ·
      refine ⟨48577804865938385124108587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32385203243958923416072391 48577804865938385124108587)
      ·
        refine ⟨72866707298907577686162881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48577804865938385124108587 72866707298907577686162881)
        ·
          refine ⟨54650030474180683264622161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72866707298907577686162881 54650030474180683264622161)
          ·
            refine ⟨40987522855635512448466621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54650030474180683264622161 40987522855635512448466621)
            ·
              refine ⟨15370321070863317168174983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40987522855635512448466621 15370321070863317168174983)
              ·
                refine ⟨23055481606294975752262475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15370321070863317168174983 23055481606294975752262475)
                ·
                  refine ⟨34583222409442463628393713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23055481606294975752262475 34583222409442463628393713)
                  ·
                    refine ⟨25937416807081847721295285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34583222409442463628393713 25937416807081847721295285)
                    ·
                      refine ⟨2431632825663923223871433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25937416807081847721295285 2431632825663923223871433)
                      ·
                        rfl

theorem cell23_4735588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_4735588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735588 prefixEnd_4735588 := by exact prefixLift 4735588
  have htrace : WordTrace (prefixWord ++ tailWord_4735588) baseStart_4735588 baseEnd_4735588 := by
    simpa [prefixWord, tailWord_4735588, baseEnd_4735588] using wordTrace_append hprefix tailTrace_4735588
  have hstable : (prefixWord ++ tailWord_4735588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735588).length < 2 ^ (prefixWord ++ tailWord_4735588).sum := by decide
  have hdescent : baseEnd_4735588 < baseStart_4735588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735669 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4735669 : Nat := 118140960795 + 4735669 * 2 ^ 59
def prefixEnd_4735669 : Nat := 4983230072969 + 3 ^ 40 * 4735669 * 2
def baseEnd_4735669 : Nat := 2431674417596937406958561

theorem tailTrace_4735669 : CollatzResearch.WordTrace tailWord_4735669 prefixEnd_4735669 2431674417596937406958561 := by
  unfold tailWord_4735669
  simp only [CollatzResearch.WordTrace]
  refine ⟨172724038280487475719418061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115149358853658317146278707 172724038280487475719418061)
  ·
    refine ⟨64771514355182803394781773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172724038280487475719418061 64771514355182803394781773)
    ·
      refine ⟨24289317883193551273043165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64771514355182803394781773 24289317883193551273043165)
      ·
        refine ⟨9108494206197581727391187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24289317883193551273043165 9108494206197581727391187)
        ·
          refine ⟨13662741309296372591086781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108494206197581727391187 13662741309296372591086781)
          ·
            refine ⟨5123527990986139721657543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13662741309296372591086781 5123527990986139721657543)
            ·
              refine ⟨7685291986479209582486315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123527990986139721657543 7685291986479209582486315)
              ·
                refine ⟨11527937979718814373729473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685291986479209582486315 11527937979718814373729473)
                ·
                  refine ⟨8645953484789110780297105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11527937979718814373729473 8645953484789110780297105)
                  ·
                    refine ⟨6484465113591833085222829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8645953484789110780297105 6484465113591833085222829)
                    ·
                      refine ⟨2431674417596937406958561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6484465113591833085222829 2431674417596937406958561)
                      ·
                        rfl

theorem cell23_4735669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4735669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735669 prefixEnd_4735669 := by exact prefixLift 4735669
  have htrace : WordTrace (prefixWord ++ tailWord_4735669) baseStart_4735669 baseEnd_4735669 := by
    simpa [prefixWord, tailWord_4735669, baseEnd_4735669] using wordTrace_append hprefix tailTrace_4735669
  have hstable : (prefixWord ++ tailWord_4735669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735669).length < 2 ^ (prefixWord ++ tailWord_4735669).sum := by decide
  have hdescent : baseEnd_4735669 < baseStart_4735669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735725 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4735725 : Nat := 118140960795 + 4735725 * 2 ^ 59
def prefixEnd_4735725 : Nat := 4983230072969 + 3 ^ 40 * 4735725 * 2
def baseEnd_4735725 : Nat := 2431703172513589187858303

theorem tailTrace_4735725 : CollatzResearch.WordTrace tailWord_4735725 prefixEnd_4735725 2431703172513589187858303 := by
  unfold tailWord_4735725
  simp only [CollatzResearch.WordTrace]
  refine ⟨172726080768284597283456629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115150720512189731522304419 172726080768284597283456629)
  ·
    refine ⟨16193070072026680995324059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172726080768284597283456629 16193070072026680995324059)
    ·
      refine ⟨24289605108040021492986089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16193070072026680995324059 24289605108040021492986089)
      ·
        refine ⟨18217203831030016119739567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24289605108040021492986089 18217203831030016119739567)
        ·
          refine ⟨27325805746545024179609351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18217203831030016119739567 27325805746545024179609351)
          ·
            refine ⟨40988708619817536269414027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27325805746545024179609351 40988708619817536269414027)
            ·
              refine ⟨61483062929726304404121041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40988708619817536269414027 61483062929726304404121041)
              ·
                refine ⟨46112297197294728303090781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61483062929726304404121041 46112297197294728303090781)
                ·
                  refine ⟨17292111448985523113659043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46112297197294728303090781 17292111448985523113659043)
                  ·
                    refine ⟨25938167173478284670488565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17292111448985523113659043 25938167173478284670488565)
                    ·
                      refine ⟨2431703172513589187858303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25938167173478284670488565 2431703172513589187858303)
                      ·
                        rfl

theorem cell23_4735725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4735725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735725 prefixEnd_4735725 := by exact prefixLift 4735725
  have htrace : WordTrace (prefixWord ++ tailWord_4735725) baseStart_4735725 baseEnd_4735725 := by
    simpa [prefixWord, tailWord_4735725, baseEnd_4735725] using wordTrace_append hprefix tailTrace_4735725
  have hstable : (prefixWord ++ tailWord_4735725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735725).length < 2 ^ (prefixWord ++ tailWord_4735725).sum := by decide
  have hdescent : baseEnd_4735725 < baseStart_4735725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735728 : List Nat := [2, 1, 1, 1, 3, 1, 5, 9]
def baseStart_4735728 : Nat := 118140960795 + 4735728 * 2 ^ 59
def prefixEnd_4735728 : Nat := 4983230072969 + 3 ^ 40 * 4735728 * 2
def baseEnd_4735728 : Nat := 90063137516872321337807

theorem tailTrace_4735728 : CollatzResearch.WordTrace tailWord_4735728 prefixEnd_4735728 90063137516872321337807 := by
  unfold tailWord_4735728
  simp only [CollatzResearch.WordTrace]
  refine ⟨86363095093636864397907919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115150793458182485863877225 86363095093636864397907919)
  ·
    refine ⟨129544642640455296596861879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86363095093636864397907919 129544642640455296596861879)
    ·
      refine ⟨194316963960682944895292819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129544642640455296596861879 194316963960682944895292819)
      ·
        refine ⟨291475445941024417342939229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194316963960682944895292819 291475445941024417342939229)
        ·
          refine ⟨109303292227884156503602211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291475445941024417342939229 109303292227884156503602211)
          ·
            refine ⟨163954938341826234755403317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109303292227884156503602211 163954938341826234755403317)
            ·
              refine ⟨15370775469546209508319061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163954938341826234755403317 15370775469546209508319061)
              ·
                refine ⟨90063137516872321337807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15370775469546209508319061 90063137516872321337807)
                ·
                  rfl

theorem cell23_4735728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_4735728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735728 prefixEnd_4735728 := by exact prefixLift 4735728
  have htrace : WordTrace (prefixWord ++ tailWord_4735728) baseStart_4735728 baseEnd_4735728 := by
    simpa [prefixWord, tailWord_4735728, baseEnd_4735728] using wordTrace_append hprefix tailTrace_4735728
  have hstable : (prefixWord ++ tailWord_4735728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735728).length < 2 ^ (prefixWord ++ tailWord_4735728).sum := by decide
  have hdescent : baseEnd_4735728 < baseStart_4735728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735742 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4735742 : Nat := 118140960795 + 4735742 * 2 ^ 59
def prefixEnd_4735742 : Nat := 4983230072969 + 3 ^ 40 * 4735742 * 2
def baseEnd_4735742 : Nat := 2431711901684715621345725

theorem tailTrace_4735742 : CollatzResearch.WordTrace tailWord_4735742 prefixEnd_4735742 2431711901684715621345725 := by
  unfold tailWord_4735742
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590837601152876148353185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115151133872815339457883653 21590837601152876148353185)
  ·
    refine ⟨16193128200864657111264889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21590837601152876148353185 16193128200864657111264889)
    ·
      refine ⟨12144846150648492833448667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16193128200864657111264889 12144846150648492833448667)
      ·
        refine ⟨18217269225972739250173001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12144846150648492833448667 18217269225972739250173001)
        ·
          refine ⟨13662951919479554437629751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18217269225972739250173001 13662951919479554437629751)
          ·
            refine ⟨20494427879219331656444627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13662951919479554437629751 20494427879219331656444627)
            ·
              refine ⟨30741641818828997484666941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20494427879219331656444627 30741641818828997484666941)
              ·
                refine ⟨11528115682060874056750103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30741641818828997484666941 11528115682060874056750103)
                ·
                  refine ⟨17292173523091311085125155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11528115682060874056750103 17292173523091311085125155)
                  ·
                    refine ⟨25938260284636966627687733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17292173523091311085125155 25938260284636966627687733)
                    ·
                      refine ⟨2431711901684715621345725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25938260284636966627687733 2431711901684715621345725)
                      ·
                        rfl

theorem cell23_4735742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4735742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735742 prefixEnd_4735742 := by exact prefixLift 4735742
  have htrace : WordTrace (prefixWord ++ tailWord_4735742) baseStart_4735742 baseEnd_4735742 := by
    simpa [prefixWord, tailWord_4735742, baseEnd_4735742] using wordTrace_append hprefix tailTrace_4735742
  have hstable : (prefixWord ++ tailWord_4735742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735742).length < 2 ^ (prefixWord ++ tailWord_4735742).sum := by decide
  have hdescent : baseEnd_4735742 < baseStart_4735742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735773 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4735773 : Nat := 118140960795 + 4735773 * 2 ^ 59
def prefixEnd_4735773 : Nat := 4983230072969 + 3 ^ 40 * 4735773 * 2
def baseEnd_4735773 : Nat := 2431727819585005000058083

theorem tailTrace_4735773 : CollatzResearch.WordTrace tailWord_4735773 prefixEnd_4735773 2431727819585005000058083 := by
  unfold tailWord_4735773
  simp only [CollatzResearch.WordTrace]
  refine ⟨172727831472110701481203973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115151887648073800987469315 172727831472110701481203973)
  ·
    refine ⟨32386468401020756527725745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172727831472110701481203973 32386468401020756527725745)
    ·
      refine ⟨24289851300765567395794309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32386468401020756527725745 24289851300765567395794309)
      ·
        refine ⟨4554347118893543886711433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24289851300765567395794309 4554347118893543886711433)
        ·
          refine ⟨3415760339170157915033575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4554347118893543886711433 3415760339170157915033575)
          ·
            refine ⟨5123640508755236872550363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415760339170157915033575 5123640508755236872550363)
            ·
              refine ⟨7685460763132855308825545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123640508755236872550363 7685460763132855308825545)
              ·
                refine ⟨5764095572349641481619159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7685460763132855308825545 5764095572349641481619159)
                ·
                  refine ⟨8646143358524462222428739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764095572349641481619159 8646143358524462222428739)
                  ·
                    refine ⟨12969215037786693333643109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8646143358524462222428739 12969215037786693333643109)
                    ·
                      refine ⟨2431727819585005000058083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12969215037786693333643109 2431727819585005000058083)
                      ·
                        rfl

theorem cell23_4735773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4735773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735773 prefixEnd_4735773 := by exact prefixLift 4735773
  have htrace : WordTrace (prefixWord ++ tailWord_4735773) baseStart_4735773 baseEnd_4735773 := by
    simpa [prefixWord, tailWord_4735773, baseEnd_4735773] using wordTrace_append hprefix tailTrace_4735773
  have hstable : (prefixWord ++ tailWord_4735773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735773).length < 2 ^ (prefixWord ++ tailWord_4735773).sum := by decide
  have hdescent : baseEnd_4735773 < baseStart_4735773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735829 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4735829 : Nat := 118140960795 + 4735829 * 2 ^ 59
def prefixEnd_4735829 : Nat := 4983230072969 + 3 ^ 40 * 4735829 * 2
def baseEnd_4735829 : Nat := 2431756574501656780957825

theorem tailTrace_4735829 : CollatzResearch.WordTrace tailWord_4735829 prefixEnd_4735829 2431756574501656780957825 := by
  unfold tailWord_4735829
  simp only [CollatzResearch.WordTrace]
  refine ⟨172729873959907823045242541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115153249306605215363495027 172729873959907823045242541)
  ·
    refine ⟨64773702734965433641965953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172729873959907823045242541 64773702734965433641965953)
    ·
      refine ⟨48580277051224075231474465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64773702734965433641965953 48580277051224075231474465)
      ·
        refine ⟨36435207788418056423605849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48580277051224075231474465 36435207788418056423605849)
        ·
          refine ⟨27326405841313542317704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36435207788418056423605849 27326405841313542317704387)
          ·
            refine ⟨40989608761970313476556581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27326405841313542317704387 40989608761970313476556581)
            ·
              refine ⟨7685551642869433776854359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40989608761970313476556581 7685551642869433776854359)
              ·
                refine ⟨11528327464304150665281539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685551642869433776854359 11528327464304150665281539)
                ·
                  refine ⟨17292491196456225997922309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11528327464304150665281539 17292491196456225997922309)
                  ·
                    refine ⟨3242342099335542374610433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17292491196456225997922309 3242342099335542374610433)
                    ·
                      refine ⟨2431756574501656780957825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242342099335542374610433 2431756574501656780957825)
                      ·
                        rfl

theorem cell23_4735829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4735829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735829 prefixEnd_4735829 := by exact prefixLift 4735829
  have htrace : WordTrace (prefixWord ++ tailWord_4735829) baseStart_4735829 baseEnd_4735829 := by
    simpa [prefixWord, tailWord_4735829, baseEnd_4735829] using wordTrace_append hprefix tailTrace_4735829
  have hstable : (prefixWord ++ tailWord_4735829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735829).length < 2 ^ (prefixWord ++ tailWord_4735829).sum := by decide
  have hdescent : baseEnd_4735829 < baseStart_4735829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735872 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2]
def baseStart_4735872 : Nat := 118140960795 + 4735872 * 2 ^ 59
def prefixEnd_4735872 : Nat := 4983230072969 + 3 ^ 40 * 4735872 * 2
def baseEnd_4735872 : Nat := 2431778654169800112720127

theorem tailTrace_4735872 : CollatzResearch.WordTrace tailWord_4735872 prefixEnd_4735872 2431778654169800112720127 := by
  unfold tailWord_4735872
  simp only [CollatzResearch.WordTrace]
  refine ⟨86365721149376020694528935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115154294865834694259371913 86365721149376020694528935)
  ·
    refine ⟨129548581724064031041793403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86365721149376020694528935 129548581724064031041793403)
    ·
      refine ⟨194322872586096046562690105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129548581724064031041793403 194322872586096046562690105)
      ·
        refine ⟨145742154439572034922017579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194322872586096046562690105 145742154439572034922017579)
        ·
          refine ⟨218613231659358052383026369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145742154439572034922017579 218613231659358052383026369)
          ·
            refine ⟨163959923744518539287269777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218613231659358052383026369 163959923744518539287269777)
            ·
              refine ⟨122969942808388904465452333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163959923744518539287269777 122969942808388904465452333)
              ·
                refine ⟨46113728553145839174544625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122969942808388904465452333 46113728553145839174544625)
                ·
                  refine ⟨34585296414859379380908469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46113728553145839174544625 34585296414859379380908469)
                  ·
                    refine ⟨3242371538893066816960169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34585296414859379380908469 3242371538893066816960169)
                    ·
                      refine ⟨2431778654169800112720127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242371538893066816960169 2431778654169800112720127)
                      ·
                        rfl

theorem cell23_4735872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_4735872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735872 prefixEnd_4735872 := by exact prefixLift 4735872
  have htrace : WordTrace (prefixWord ++ tailWord_4735872) baseStart_4735872 baseEnd_4735872 := by
    simpa [prefixWord, tailWord_4735872, baseEnd_4735872] using wordTrace_append hprefix tailTrace_4735872
  have hstable : (prefixWord ++ tailWord_4735872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735872).length < 2 ^ (prefixWord ++ tailWord_4735872).sum := by decide
  have hdescent : baseEnd_4735872 < baseStart_4735872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735875 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4735875 : Nat := 118140960795 + 4735875 * 2 ^ 59
def prefixEnd_4735875 : Nat := 4983230072969 + 3 ^ 40 * 4735875 * 2
def baseEnd_4735875 : Nat := 2431780194611763600982613

theorem tailTrace_4735875 : CollatzResearch.WordTrace tailWord_4735875 prefixEnd_4735875 2431780194611763600982613 := by
  unfold tailWord_4735875
  simp only [CollatzResearch.WordTrace]
  refine ⟨172731551717741172901417079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115154367811827448600944719 172731551717741172901417079)
  ·
    refine ⟨259097327576611759352125619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172731551717741172901417079 259097327576611759352125619)
    ·
      refine ⟨388645991364917639028188429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259097327576611759352125619 388645991364917639028188429)
      ·
        refine ⟨145742246761844114635570661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388645991364917639028188429 145742246761844114635570661)
        ·
          refine ⟨27326671267845771494169499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145742246761844114635570661 27326671267845771494169499)
          ·
            refine ⟨40990006901768657241254249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27326671267845771494169499 40990006901768657241254249)
            ·
              refine ⟨30742505176326492930940687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40990006901768657241254249 30742505176326492930940687)
              ·
                refine ⟨46113757764489739396411031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30742505176326492930940687 46113757764489739396411031)
                ·
                  refine ⟨69170636646734609094616547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46113757764489739396411031 69170636646734609094616547)
                  ·
                    refine ⟨103755954970101913641924821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69170636646734609094616547 103755954970101913641924821)
                    ·
                      refine ⟨2431780194611763600982613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103755954970101913641924821 2431780194611763600982613)
                      ·
                        rfl

theorem cell23_4735875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4735875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735875 prefixEnd_4735875 := by exact prefixLift 4735875
  have htrace : WordTrace (prefixWord ++ tailWord_4735875) baseStart_4735875 baseEnd_4735875 := by
    simpa [prefixWord, tailWord_4735875, baseEnd_4735875] using wordTrace_append hprefix tailTrace_4735875
  have hstable : (prefixWord ++ tailWord_4735875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735875).length < 2 ^ (prefixWord ++ tailWord_4735875).sum := by decide
  have hdescent : baseEnd_4735875 < baseStart_4735875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735882 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_4735882 : Nat := 118140960795 + 4735882 * 2 ^ 59
def prefixEnd_4735882 : Nat := 4983230072969 + 3 ^ 40 * 4735882 * 2
def baseEnd_4735882 : Nat := 810594596325448357865027

theorem tailTrace_4735882 : CollatzResearch.WordTrace tailWord_4735882 prefixEnd_4735882 810594596325448357865027 := by
  unfold tailWord_4735882
  simp only [CollatzResearch.WordTrace]
  refine ⟨43182951757178953274230475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115154538019143875397947933 43182951757178953274230475)
  ·
    refine ⟨64774427635768429911345713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43182951757178953274230475 64774427635768429911345713)
    ·
      refine ⟨48580820726826322433509285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64774427635768429911345713 48580820726826322433509285)
      ·
        refine ⟨9108903886279935456282991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48580820726826322433509285 9108903886279935456282991)
        ·
          refine ⟨13663355829419903184424487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108903886279935456282991 13663355829419903184424487)
          ·
            refine ⟨20495033744129854776636731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13663355829419903184424487 20495033744129854776636731)
            ·
              refine ⟨30742550616194782164955097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20495033744129854776636731 30742550616194782164955097)
              ·
                refine ⟨23056912962146086623716323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30742550616194782164955097 23056912962146086623716323)
                ·
                  refine ⟨34585369443219129935574485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23056912962146086623716323 34585369443219129935574485)
                  ·
                    refine ⟨810594596325448357865027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34585369443219129935574485 810594596325448357865027)
                    ·
                      rfl

theorem cell23_4735882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_4735882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735882 prefixEnd_4735882 := by exact prefixLift 4735882
  have htrace : WordTrace (prefixWord ++ tailWord_4735882) baseStart_4735882 baseEnd_4735882 := by
    simpa [prefixWord, tailWord_4735882, baseEnd_4735882] using wordTrace_append hprefix tailTrace_4735882
  have hstable : (prefixWord ++ tailWord_4735882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735882).length < 2 ^ (prefixWord ++ tailWord_4735882).sum := by decide
  have hdescent : baseEnd_4735882 < baseStart_4735882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735895 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 8]
def baseStart_4735895 : Nat := 118140960795 + 4735895 * 2 ^ 59
def prefixEnd_4735895 : Nat := 4983230072969 + 3 ^ 40 * 4735895 * 2
def baseEnd_4735895 : Nat := 810596821408284507577507

theorem tailTrace_4735895 : CollatzResearch.WordTrace tailWord_4735895 prefixEnd_4735895 810596821408284507577507 := by
  unfold tailWord_4735895
  simp only [CollatzResearch.WordTrace]
  refine ⟨172732281177668716317145139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115154854118445810878096759 172732281177668716317145139)
  ·
    refine ⟨259098421766503074475717709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172732281177668716317145139 259098421766503074475717709)
    ·
      refine ⟨97161908162438652928394141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259098421766503074475717709 97161908162438652928394141)
      ·
        refine ⟨36435715560914494848147803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97161908162438652928394141 36435715560914494848147803)
        ·
          refine ⟨54653573341371742272221705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36435715560914494848147803 54653573341371742272221705)
          ·
            refine ⟨40990180006028806704166279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54653573341371742272221705 40990180006028806704166279)
            ·
              refine ⟨61485270009043210056249419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40990180006028806704166279 61485270009043210056249419)
              ·
                refine ⟨92227905013564815084374129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61485270009043210056249419 92227905013564815084374129)
                ·
                  refine ⟨69170928760173611313280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92227905013564815084374129 69170928760173611313280597)
                  ·
                    refine ⟨810596821408284507577507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69170928760173611313280597 810596821408284507577507)
                    ·
                      rfl

theorem cell23_4735895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_4735895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735895 prefixEnd_4735895 := by exact prefixLift 4735895
  have htrace : WordTrace (prefixWord ++ tailWord_4735895) baseStart_4735895 baseEnd_4735895 := by
    simpa [prefixWord, tailWord_4735895, baseEnd_4735895] using wordTrace_append hprefix tailTrace_4735895
  have hstable : (prefixWord ++ tailWord_4735895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735895).length < 2 ^ (prefixWord ++ tailWord_4735895).sum := by decide
  have hdescent : baseEnd_4735895 < baseStart_4735895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735915 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_4735915 : Nat := 118140960795 + 4735915 * 2 ^ 59
def prefixEnd_4735915 : Nat := 4983230072969 + 3 ^ 40 * 4735915 * 2
def baseEnd_4735915 : Nat := 2431800733837943444482429

theorem tailTrace_4735915 : CollatzResearch.WordTrace tailWord_4735915 prefixEnd_4735915 2431800733837943444482429 := by
  unfold tailWord_4735915
  simp only [CollatzResearch.WordTrace]
  refine ⟨172733010637596259732873199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115155340425064173155248799 172733010637596259732873199)
  ·
    refine ⟨259099515956394389599309799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172733010637596259732873199 259099515956394389599309799)
    ·
      refine ⟨388649273934591584398964699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259099515956394389599309799 388649273934591584398964699)
      ·
        refine ⟨582973910901887376598447049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388649273934591584398964699 582973910901887376598447049)
        ·
          refine ⟨437230433176415532448835287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582973910901887376598447049 437230433176415532448835287)
          ·
            refine ⟨655845649764623298673252931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437230433176415532448835287 655845649764623298673252931)
            ·
              refine ⟨983768474646934948009879397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655845649764623298673252931 983768474646934948009879397)
              ·
                refine ⟨184456588996300302751852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 983768474646934948009879397 184456588996300302751852387)
                ·
                  refine ⟨276684883494450454127778581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184456588996300302751852387 276684883494450454127778581)
                  ·
                    refine ⟨12969603913802365037239621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 276684883494450454127778581 12969603913802365037239621)
                    ·
                      refine ⟨2431800733837943444482429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12969603913802365037239621 2431800733837943444482429)
                      ·
                        rfl

theorem cell23_4735915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_4735915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735915 prefixEnd_4735915 := by exact prefixLift 4735915
  have htrace : WordTrace (prefixWord ++ tailWord_4735915) baseStart_4735915 baseEnd_4735915 := by
    simpa [prefixWord, tailWord_4735915, baseEnd_4735915] using wordTrace_append hprefix tailTrace_4735915
  have hstable : (prefixWord ++ tailWord_4735915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735915).length < 2 ^ (prefixWord ++ tailWord_4735915).sum := by decide
  have hdescent : baseEnd_4735915 < baseStart_4735915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735929 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_4735929 : Nat := 118140960795 + 4735929 * 2 ^ 59
def prefixEnd_4735929 : Nat := 4983230072969 + 3 ^ 40 * 4735929 * 2
def baseEnd_4735929 : Nat := 810602640855702129902455

theorem tailTrace_4735929 : CollatzResearch.WordTrace tailWord_4735929 prefixEnd_4735929 810602640855702129902455 := by
  unfold tailWord_4735929
  simp only [CollatzResearch.WordTrace]
  refine ⟨172733521259545540123882841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115155680839697026749255227 172733521259545540123882841)
  ·
    refine ⟨129550140944659155092912131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172733521259545540123882841 129550140944659155092912131)
    ·
      refine ⟨194325211416988732639368197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129550140944659155092912131 194325211416988732639368197)
      ·
        refine ⟨36435977140685387369881537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194325211416988732639368197 36435977140685387369881537)
        ·
          refine ⟨27326982855514040527411153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36435977140685387369881537 27326982855514040527411153)
          ·
            refine ⟨20495237141635530395558365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27326982855514040527411153 20495237141635530395558365)
            ·
              refine ⟨7685713928113323898334387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20495237141635530395558365 7685713928113323898334387)
              ·
                refine ⟨11528570892169985847501581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685713928113323898334387 11528570892169985847501581)
                ·
                  refine ⟨4323214084563744692813093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11528570892169985847501581 4323214084563744692813093)
                  ·
                    refine ⟨810602640855702129902455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4323214084563744692813093 810602640855702129902455)
                    ·
                      rfl

theorem cell23_4735929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_4735929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735929 prefixEnd_4735929 := by exact prefixLift 4735929
  have htrace : WordTrace (prefixWord ++ tailWord_4735929) baseStart_4735929 baseEnd_4735929 := by
    simpa [prefixWord, tailWord_4735929, baseEnd_4735929] using wordTrace_append hprefix tailTrace_4735929
  have hstable : (prefixWord ++ tailWord_4735929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735929).length < 2 ^ (prefixWord ++ tailWord_4735929).sum := by decide
  have hdescent : baseEnd_4735929 < baseStart_4735929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4735956 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4735956 : Nat := 118140960795 + 4735956 * 2 ^ 59
def prefixEnd_4735956 : Nat := 4983230072969 + 3 ^ 40 * 4735956 * 2
def baseEnd_4735956 : Nat := 2431821786544777784069741

theorem tailTrace_4735956 : CollatzResearch.WordTrace tailWord_4735956 prefixEnd_4735956 2431821786544777784069741 := by
  unfold tailWord_4735956
  simp only [CollatzResearch.WordTrace]
  refine ⟨86367253015223861867557861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115156337353631815823410481 86367253015223861867557861)
  ·
    refine ⟨16193859940354474100167099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86367253015223861867557861 16193859940354474100167099)
    ·
      refine ⟨24290789910531711150250649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16193859940354474100167099 24290789910531711150250649)
      ·
        refine ⟨18218092432898783362687987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24290789910531711150250649 18218092432898783362687987)
        ·
          refine ⟨27327138649348175044031981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18218092432898783362687987 27327138649348175044031981)
          ·
            refine ⟨10247676993505565641511993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27327138649348175044031981 10247676993505565641511993)
            ·
              refine ⟨7685757745129174231133995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10247676993505565641511993 7685757745129174231133995)
              ·
                refine ⟨11528636617693761346700993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685757745129174231133995 11528636617693761346700993)
                ·
                  refine ⟨8646477463270321010025745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11528636617693761346700993 8646477463270321010025745)
                  ·
                    refine ⟨6484858097452740757519309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8646477463270321010025745 6484858097452740757519309)
                    ·
                      refine ⟨2431821786544777784069741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6484858097452740757519309 2431821786544777784069741)
                      ·
                        rfl

theorem cell23_4735956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4735956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4735956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4735956 prefixEnd_4735956 := by exact prefixLift 4735956
  have htrace : WordTrace (prefixWord ++ tailWord_4735956) baseStart_4735956 baseEnd_4735956 := by
    simpa [prefixWord, tailWord_4735956, baseEnd_4735956] using wordTrace_append hprefix tailTrace_4735956
  have hstable : (prefixWord ++ tailWord_4735956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4735956).length < 2 ^ (prefixWord ++ tailWord_4735956).sum := by decide
  have hdescent : baseEnd_4735956 < baseStart_4735956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4735956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736023 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 1, 5]
def baseStart_4736023 : Nat := 118140960795 + 4736023 * 2 ^ 59
def prefixEnd_4736023 : Nat := 4983230072969 + 3 ^ 40 * 4736023 * 2
def baseEnd_4736023 : Nat := 810618729916209673977311

theorem tailTrace_4736023 : CollatzResearch.WordTrace tailWord_4736023 prefixEnd_4736023 810618729916209673977311 := by
  unfold tailWord_4736023
  simp only [CollatzResearch.WordTrace]
  refine ⟨172736949721204994177804723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115157966480803329451869815 172736949721204994177804723)
  ·
    refine ⟨259105424581807491266707085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172736949721204994177804723 259105424581807491266707085)
    ·
      refine ⟨97164534218177809225015157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259105424581807491266707085 97164534218177809225015157)
      ·
        refine ⟨9109175082954169614845171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97164534218177809225015157 9109175082954169614845171)
        ·
          refine ⟨13663762624431254422267757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109175082954169614845171 13663762624431254422267757)
          ·
            refine ⟨5123910984161720408350409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13663762624431254422267757 5123910984161720408350409)
            ·
              refine ⟨3842933238121290306262807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123910984161720408350409 3842933238121290306262807)
              ·
                refine ⟨5764399857181935459394211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842933238121290306262807 5764399857181935459394211)
                ·
                  refine ⟨8646599785772903189091317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764399857181935459394211 8646599785772903189091317)
                  ·
                    refine ⟨810618729916209673977311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8646599785772903189091317 810618729916209673977311)
                    ·
                      rfl

theorem cell23_4736023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_4736023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736023 prefixEnd_4736023 := by exact prefixLift 4736023
  have htrace : WordTrace (prefixWord ++ tailWord_4736023) baseStart_4736023 baseEnd_4736023 := by
    simpa [prefixWord, tailWord_4736023, baseEnd_4736023] using wordTrace_append hprefix tailTrace_4736023
  have hstable : (prefixWord ++ tailWord_4736023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736023).length < 2 ^ (prefixWord ++ tailWord_4736023).sum := by decide
  have hdescent : baseEnd_4736023 < baseStart_4736023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736026 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_4736026 : Nat := 118140960795 + 4736026 * 2 ^ 59
def prefixEnd_4736026 : Nat := 4983230072969 + 3 ^ 40 * 4736026 * 2
def baseEnd_4736026 : Nat := 2431857730190592510194419

theorem tailTrace_4736026 : CollatzResearch.WordTrace tailWord_4736026 prefixEnd_4736026 2431857730190592510194419 := by
  unfold tailWord_4736026
  simp only [CollatzResearch.WordTrace]
  refine ⟨43184264785048531422540983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115158039426796083793442621 43184264785048531422540983)
  ·
    refine ⟨64776397177572797133811475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43184264785048531422540983 64776397177572797133811475)
    ·
      refine ⟨97164595766359195700717213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64776397177572797133811475 97164595766359195700717213)
      ·
        refine ⟨36436723412384698387768955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97164595766359195700717213 36436723412384698387768955)
        ·
          refine ⟨54655085118577047581653433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36436723412384698387768955 54655085118577047581653433)
          ·
            refine ⟨40991313838932785686240075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54655085118577047581653433 40991313838932785686240075)
            ·
              refine ⟨61486970758399178529360113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40991313838932785686240075 61486970758399178529360113)
              ·
                refine ⟨46115228068799383897020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61486970758399178529360113 46115228068799383897020085)
                ·
                  refine ⟨4323302631449942240345633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46115228068799383897020085 4323302631449942240345633)
                  ·
                    refine ⟨3242476973587456680259225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323302631449942240345633 3242476973587456680259225)
                    ·
                      refine ⟨2431857730190592510194419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242476973587456680259225 2431857730190592510194419)
                      ·
                        rfl

theorem cell23_4736026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_4736026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736026 prefixEnd_4736026 := by exact prefixLift 4736026
  have htrace : WordTrace (prefixWord ++ tailWord_4736026) baseStart_4736026 baseEnd_4736026 := by
    simpa [prefixWord, tailWord_4736026, baseEnd_4736026] using wordTrace_append hprefix tailTrace_4736026
  have hstable : (prefixWord ++ tailWord_4736026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736026).length < 2 ^ (prefixWord ++ tailWord_4736026).sum := by decide
  have hdescent : baseEnd_4736026 < baseStart_4736026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736036 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_4736036 : Nat := 118140960795 + 4736036 * 2 ^ 59
def prefixEnd_4736036 : Nat := 4983230072969 + 3 ^ 40 * 4736036 * 2
def baseEnd_4736036 : Nat := 810620954999045823689791

theorem tailTrace_4736036 : CollatzResearch.WordTrace tailWord_4736036 prefixEnd_4736036 810620954999045823689791 := by
  unfold tailWord_4736036
  simp only [CollatzResearch.WordTrace]
  refine ⟨86368711935078948699013981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115158282580105264932018641 86368711935078948699013981)
  ·
    refine ⟨32388266975654605762130243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86368711935078948699013981 32388266975654605762130243)
    ·
      refine ⟨48582400463481908643195365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32388266975654605762130243 48582400463481908643195365)
      ·
        refine ⟨9109200086902857870599131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48582400463481908643195365 9109200086902857870599131)
        ·
          refine ⟨13663800130354286805898697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109200086902857870599131 13663800130354286805898697)
          ·
            refine ⟨10247850097765715104424023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13663800130354286805898697 10247850097765715104424023)
            ·
              refine ⟨15371775146648572656636035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10247850097765715104424023 15371775146648572656636035)
              ·
                refine ⟨23057662719972858984954053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15371775146648572656636035 23057662719972858984954053)
                ·
                  refine ⟨4323311759994911059678885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23057662719972858984954053 4323311759994911059678885)
                  ·
                    refine ⟨810620954999045823689791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4323311759994911059678885 810620954999045823689791)
                    ·
                      rfl

theorem cell23_4736036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_4736036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736036 prefixEnd_4736036 := by exact prefixLift 4736036
  have htrace : WordTrace (prefixWord ++ tailWord_4736036) baseStart_4736036 baseEnd_4736036 := by
    simpa [prefixWord, tailWord_4736036, baseEnd_4736036] using wordTrace_append hprefix tailTrace_4736036
  have hstable : (prefixWord ++ tailWord_4736036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736036).length < 2 ^ (prefixWord ++ tailWord_4736036).sum := by decide
  have hdescent : baseEnd_4736036 < baseStart_4736036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736043 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 1, 2, 2]
def baseStart_4736043 : Nat := 118140960795 + 4736043 * 2 ^ 59
def prefixEnd_4736043 : Nat := 4983230072969 + 3 ^ 40 * 4736043 * 2
def baseEnd_4736043 : Nat := 2431866459361718943681841

theorem tailTrace_4736043 : CollatzResearch.WordTrace tailWord_4736043 prefixEnd_4736043 2431866459361718943681841 := by
  unfold tailWord_4736043
  simp only [CollatzResearch.WordTrace]
  refine ⟨172737679181132537593532783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115158452787421691729021855 172737679181132537593532783)
  ·
    refine ⟨259106518771698806390299175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172737679181132537593532783 259106518771698806390299175)
    ·
      refine ⟨388659778157548209585448763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259106518771698806390299175 388659778157548209585448763)
      ·
        refine ⟨582989667236322314378173145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388659778157548209585448763 582989667236322314378173145)
        ·
          refine ⟨437242250427241735783629859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582989667236322314378173145 437242250427241735783629859)
          ·
            refine ⟨655863375640862603675444789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437242250427241735783629859 655863375640862603675444789)
            ·
              refine ⟨61487191466330869094572949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 655863375640862603675444789 61487191466330869094572949)
              ·
                refine ⟨2882212099984259488808107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61487191466330869094572949 2882212099984259488808107)
                ·
                  refine ⟨4323318149976389233212161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882212099984259488808107 4323318149976389233212161)
                  ·
                    refine ⟨3242488612482291924909121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323318149976389233212161 3242488612482291924909121)
                    ·
                      refine ⟨2431866459361718943681841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242488612482291924909121 2431866459361718943681841)
                      ·
                        rfl

theorem cell23_4736043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 2, 2].length) (baseStart_4736043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736043 prefixEnd_4736043 := by exact prefixLift 4736043
  have htrace : WordTrace (prefixWord ++ tailWord_4736043) baseStart_4736043 baseEnd_4736043 := by
    simpa [prefixWord, tailWord_4736043, baseEnd_4736043] using wordTrace_append hprefix tailTrace_4736043
  have hstable : (prefixWord ++ tailWord_4736043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736043).length < 2 ^ (prefixWord ++ tailWord_4736043).sum := by decide
  have hdescent : baseEnd_4736043 < baseStart_4736043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736056 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_4736056 : Nat := 118140960795 + 4736056 * 2 ^ 59
def prefixEnd_4736056 : Nat := 4983230072969 + 3 ^ 40 * 4736056 * 2
def baseEnd_4736056 : Nat := 2431873134610227392819281

theorem tailTrace_4736056 : CollatzResearch.WordTrace tailWord_4736056 prefixEnd_4736056 2431873134610227392819281 := by
  unfold tailWord_4736056
  simp only [CollatzResearch.WordTrace]
  refine ⟨86369076665042720406878011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115158768886723627209170681 86369076665042720406878011)
  ·
    refine ⟨129553614997564080610317017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86369076665042720406878011 129553614997564080610317017)
    ·
      refine ⟨97165211248173060457737763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129553614997564080610317017 97165211248173060457737763)
      ·
        refine ⟨145747816872259590686606645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97165211248173060457737763 145747816872259590686606645)
        ·
          refine ⟨13663857831774336626869373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145747816872259590686606645 13663857831774336626869373)
          ·
            refine ⟨5123946686915376235076015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13663857831774336626869373 5123946686915376235076015)
            ·
              refine ⟨7685920030373064352614023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123946686915376235076015 7685920030373064352614023)
              ·
                refine ⟨11528880045559596528921035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685920030373064352614023 11528880045559596528921035)
                ·
                  refine ⟨17293320068339394793381553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11528880045559596528921035 17293320068339394793381553)
                  ·
                    refine ⟨12969990051254546095036165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17293320068339394793381553 12969990051254546095036165)
                    ·
                      refine ⟨2431873134610227392819281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12969990051254546095036165 2431873134610227392819281)
                      ·
                        rfl

theorem cell23_4736056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_4736056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736056 prefixEnd_4736056 := by exact prefixLift 4736056
  have htrace : WordTrace (prefixWord ++ tailWord_4736056) baseStart_4736056 baseEnd_4736056 := by
    simpa [prefixWord, tailWord_4736056, baseEnd_4736056] using wordTrace_append hprefix tailTrace_4736056
  have hstable : (prefixWord ++ tailWord_4736056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736056).length < 2 ^ (prefixWord ++ tailWord_4736056).sum := by decide
  have hdescent : baseEnd_4736056 < baseStart_4736056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736059 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 3]
def baseStart_4736059 : Nat := 118140960795 + 4736059 * 2 ^ 59
def prefixEnd_4736059 : Nat := 4983230072969 + 3 ^ 40 * 4736059 * 2
def baseEnd_4736059 : Nat := 2431874675052190881081767

theorem tailTrace_4736059 : CollatzResearch.WordTrace tailWord_4736059 prefixEnd_4736059 2431874675052190881081767 := by
  unfold tailWord_4736059
  simp only [CollatzResearch.WordTrace]
  refine ⟨172738262749074572326115231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115158841832716381550743487 172738262749074572326115231)
  ·
    refine ⟨259107394123611858489172847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172738262749074572326115231 259107394123611858489172847)
    ·
      refine ⟨388661091185417787733759271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259107394123611858489172847 388661091185417787733759271)
      ·
        refine ⟨582991636778126681600638907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388661091185417787733759271 582991636778126681600638907)
        ·
          refine ⟨874487455167190022400958361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582991636778126681600638907 874487455167190022400958361)
          ·
            refine ⟨655865591375392516800718771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874487455167190022400958361 655865591375392516800718771)
            ·
              refine ⟨983798387063088775201078157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655865591375392516800718771 983798387063088775201078157)
              ·
                refine ⟨368924395148658290700404309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 983798387063088775201078157 368924395148658290700404309)
                ·
                  refine ⟨4323332755648339344145363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 368924395148658290700404309 4323332755648339344145363)
                  ·
                    refine ⟨6484999133472509016218045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323332755648339344145363 6484999133472509016218045)
                    ·
                      refine ⟨2431874675052190881081767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6484999133472509016218045 2431874675052190881081767)
                      ·
                        rfl

theorem cell23_4736059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 3].length) (baseStart_4736059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736059 prefixEnd_4736059 := by exact prefixLift 4736059
  have htrace : WordTrace (prefixWord ++ tailWord_4736059) baseStart_4736059 baseEnd_4736059 := by
    simpa [prefixWord, tailWord_4736059, baseEnd_4736059] using wordTrace_append hprefix tailTrace_4736059
  have hstable : (prefixWord ++ tailWord_4736059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736059).length < 2 ^ (prefixWord ++ tailWord_4736059).sum := by decide
  have hdescent : baseEnd_4736059 < baseStart_4736059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736072 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_4736072 : Nat := 118140960795 + 4736072 * 2 ^ 59
def prefixEnd_4736072 : Nat := 4983230072969 + 3 ^ 40 * 4736072 * 2
def baseEnd_4736072 : Nat := 2431881350300699330219207

theorem tailTrace_4736072 : CollatzResearch.WordTrace tailWord_4736072 prefixEnd_4736072 2431881350300699330219207 := by
  unfold tailWord_4736072
  simp only [CollatzResearch.WordTrace]
  refine ⟨86369368449013737773169235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115159157932018317030892313 86369368449013737773169235)
  ·
    refine ⟨129554052673520606659753853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86369368449013737773169235 129554052673520606659753853)
    ·
      refine ⟨48582769752570227497407695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129554052673520606659753853 48582769752570227497407695)
      ·
        refine ⟨72874154628855341246111543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48582769752570227497407695 72874154628855341246111543)
        ·
          refine ⟨109311231943283011869167315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72874154628855341246111543 109311231943283011869167315)
          ·
            refine ⟨163966847914924517803750973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109311231943283011869167315 163966847914924517803750973)
            ·
              refine ⟨61487567968096694176406615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163966847914924517803750973 61487567968096694176406615)
              ·
                refine ⟨92231351952145041264609923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61487567968096694176406615 92231351952145041264609923)
                ·
                  refine ⟨138347027928217561896914885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92231351952145041264609923 138347027928217561896914885)
                  ·
                    refine ⟨25940067736540792855671541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138347027928217561896914885 25940067736540792855671541)
                    ·
                      refine ⟨2431881350300699330219207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25940067736540792855671541 2431881350300699330219207)
                      ·
                        rfl

theorem cell23_4736072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_4736072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736072 prefixEnd_4736072 := by exact prefixLift 4736072
  have htrace : WordTrace (prefixWord ++ tailWord_4736072) baseStart_4736072 baseEnd_4736072 := by
    simpa [prefixWord, tailWord_4736072, baseEnd_4736072] using wordTrace_append hprefix tailTrace_4736072
  have hstable : (prefixWord ++ tailWord_4736072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736072).length < 2 ^ (prefixWord ++ tailWord_4736072).sum := by decide
  have hdescent : baseEnd_4736072 < baseStart_4736072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736077 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_4736077 : Nat := 118140960795 + 4736077 * 2 ^ 59
def prefixEnd_4736077 : Nat := 4983230072969 + 3 ^ 40 * 4736077 * 2
def baseEnd_4736077 : Nat := 2431883917703971810656685

theorem tailTrace_4736077 : CollatzResearch.WordTrace tailWord_4736077 prefixEnd_4736077 2431883917703971810656685 := by
  unfold tailWord_4736077
  simp only [CollatzResearch.WordTrace]
  refine ⟨172738919263009361400270485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115159279508672907600180323 172738919263009361400270485)
  ·
    refine ⟨8097136840453563815637679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172738919263009361400270485 8097136840453563815637679)
    ·
      refine ⟨12145705260680345723456519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097136840453563815637679 12145705260680345723456519)
      ·
        refine ⟨18218557891020518585184779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12145705260680345723456519 18218557891020518585184779)
        ·
          refine ⟨27327836836530777877777169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18218557891020518585184779 27327836836530777877777169)
          ·
            refine ⟨20495877627398083408332877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27327836836530777877777169 20495877627398083408332877)
            ·
              refine ⟨7685954110274281278124829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20495877627398083408332877 7685954110274281278124829)
              ·
                refine ⟨2882232791352855479296811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7685954110274281278124829 2882232791352855479296811)
                ·
                  refine ⟨4323349187029283218945217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882232791352855479296811 4323349187029283218945217)
                  ·
                    refine ⟨3242511890271962414208913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323349187029283218945217 3242511890271962414208913)
                    ·
                      refine ⟨2431883917703971810656685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242511890271962414208913 2431883917703971810656685)
                      ·
                        rfl

theorem cell23_4736077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_4736077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736077 prefixEnd_4736077 := by exact prefixLift 4736077
  have htrace : WordTrace (prefixWord ++ tailWord_4736077) baseStart_4736077 baseEnd_4736077 := by
    simpa [prefixWord, tailWord_4736077, baseEnd_4736077] using wordTrace_append hprefix tailTrace_4736077
  have hstable : (prefixWord ++ tailWord_4736077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736077).length < 2 ^ (prefixWord ++ tailWord_4736077).sum := by decide
  have hdescent : baseEnd_4736077 < baseStart_4736077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736094 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4736094 : Nat := 118140960795 + 4736094 * 2 ^ 59
def prefixEnd_4736094 : Nat := 4983230072969 + 3 ^ 40 * 4736094 * 2
def baseEnd_4736094 : Nat := 2431892646875098244144107

theorem tailTrace_4736094 : CollatzResearch.WordTrace tailWord_4736094 prefixEnd_4736094 2431892646875098244144107 := by
  unfold tailWord_4736094
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592442412993471662954917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115159692869298515535759557 21592442412993471662954917)
  ·
    refine ⟨4048582952436275936804047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21592442412993471662954917 4048582952436275936804047)
    ·
      refine ⟨6072874428654413905206071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048582952436275936804047 6072874428654413905206071)
      ·
        refine ⟨9109311642981620857809107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072874428654413905206071 9109311642981620857809107)
        ·
          refine ⟨13663967464472431286713661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109311642981620857809107 13663967464472431286713661)
          ·
            refine ⟨5123987799177161732517623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13663967464472431286713661 5123987799177161732517623)
            ·
              refine ⟨7685981698765742598776435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123987799177161732517623 7685981698765742598776435)
              ·
                refine ⟨11528972548148613898164653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685981698765742598776435 11528972548148613898164653)
                ·
                  refine ⟨4323364705555730211811745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11528972548148613898164653 4323364705555730211811745)
                  ·
                    refine ⟨3242523529166797658858809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323364705555730211811745 3242523529166797658858809)
                    ·
                      refine ⟨2431892646875098244144107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242523529166797658858809 2431892646875098244144107)
                      ·
                        rfl

theorem cell23_4736094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4736094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736094 prefixEnd_4736094 := by exact prefixLift 4736094
  have htrace : WordTrace (prefixWord ++ tailWord_4736094) baseStart_4736094 baseEnd_4736094 := by
    simpa [prefixWord, tailWord_4736094, baseEnd_4736094] using wordTrace_append hprefix tailTrace_4736094
  have hstable : (prefixWord ++ tailWord_4736094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736094).length < 2 ^ (prefixWord ++ tailWord_4736094).sum := by decide
  have hdescent : baseEnd_4736094 < baseStart_4736094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736110 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4736110 : Nat := 118140960795 + 4736110 * 2 ^ 59
def prefixEnd_4736110 : Nat := 4983230072969 + 3 ^ 40 * 4736110 * 2
def baseEnd_4736110 : Nat := 2431900862565570181544033

theorem tailTrace_4736110 : CollatzResearch.WordTrace tailWord_4736110 prefixEnd_4736110 2431900862565570181544033 := by
  unfold tailWord_4736110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592515358986226004527723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115160081914593205357481189 21592515358986226004527723)
  ·
    refine ⟨32388773038479339006791585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21592515358986226004527723 32388773038479339006791585)
    ·
      refine ⟨24291579778859504255093689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32388773038479339006791585 24291579778859504255093689)
      ·
        refine ⟨18218684834144628191320267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24291579778859504255093689 18218684834144628191320267)
        ·
          refine ⟨27328027251216942286980401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18218684834144628191320267 27328027251216942286980401)
          ·
            refine ⟨20496020438412706715235301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27328027251216942286980401 20496020438412706715235301)
            ·
              refine ⟨3843003832202382509106619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20496020438412706715235301 3843003832202382509106619)
              ·
                refine ⟨5764505748303573763659929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843003832202382509106619 5764505748303573763659929)
                ·
                  refine ⟨4323379311227680322744947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5764505748303573763659929 4323379311227680322744947)
                  ·
                    refine ⟨6485068966841520484117421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323379311227680322744947 6485068966841520484117421)
                    ·
                      refine ⟨2431900862565570181544033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485068966841520484117421 2431900862565570181544033)
                      ·
                        rfl

theorem cell23_4736110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4736110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736110 prefixEnd_4736110 := by exact prefixLift 4736110
  have htrace : WordTrace (prefixWord ++ tailWord_4736110) baseStart_4736110 baseEnd_4736110 := by
    simpa [prefixWord, tailWord_4736110, baseEnd_4736110] using wordTrace_append hprefix tailTrace_4736110
  have hstable : (prefixWord ++ tailWord_4736110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736110).length < 2 ^ (prefixWord ++ tailWord_4736110).sum := by decide
  have hdescent : baseEnd_4736110 < baseStart_4736110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736133 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_4736133 : Nat := 118140960795 + 4736133 * 2 ^ 59
def prefixEnd_4736133 : Nat := 4983230072969 + 3 ^ 40 * 4736133 * 2
def baseEnd_4736133 : Nat := 2431912672620623591556427

theorem tailTrace_4736133 : CollatzResearch.WordTrace tailWord_4736133 prefixEnd_4736133 2431912672620623591556427 := by
  unfold tailWord_4736133
  simp only [CollatzResearch.WordTrace]
  refine ⟨172740961750806482964309053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115160641167204321976206035 172740961750806482964309053)
  ·
    refine ⟨64777860656552431111615895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172740961750806482964309053 64777860656552431111615895)
    ·
      refine ⟨97166790984828646667423843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64777860656552431111615895 97166790984828646667423843)
      ·
        refine ⟨145750186477242970001135765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97166790984828646667423843 145750186477242970001135765)
        ·
          refine ⟨6832039991120764218803239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145750186477242970001135765 6832039991120764218803239)
          ·
            refine ⟨10248059986681146328204859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832039991120764218803239 10248059986681146328204859)
            ·
              refine ⟨15372089980021719492307289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10248059986681146328204859 15372089980021719492307289)
              ·
                refine ⟨11529067485016289619230467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15372089980021719492307289 11529067485016289619230467)
                ·
                  refine ⟨17293601227524434428845701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11529067485016289619230467 17293601227524434428845701)
                  ·
                    refine ⟨3242550230160831455408569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17293601227524434428845701 3242550230160831455408569)
                    ·
                      refine ⟨2431912672620623591556427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242550230160831455408569 2431912672620623591556427)
                      ·
                        rfl

theorem cell23_4736133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_4736133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736133 prefixEnd_4736133 := by exact prefixLift 4736133
  have htrace : WordTrace (prefixWord ++ tailWord_4736133) baseStart_4736133 baseEnd_4736133 := by
    simpa [prefixWord, tailWord_4736133, baseEnd_4736133] using wordTrace_append hprefix tailTrace_4736133
  have hstable : (prefixWord ++ tailWord_4736133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736133).length < 2 ^ (prefixWord ++ tailWord_4736133).sum := by decide
  have hdescent : baseEnd_4736133 < baseStart_4736133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736293 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_4736293 : Nat := 118140960795 + 4736293 * 2 ^ 59
def prefixEnd_4736293 : Nat := 4983230072969 + 3 ^ 40 * 4736293 * 2
def baseEnd_4736293 : Nat := 810664943175114321851897

theorem tailTrace_4736293 : CollatzResearch.WordTrace tailWord_4736293 prefixEnd_4736293 810664943175114321851897 := by
  unfold tailWord_4736293
  simp only [CollatzResearch.WordTrace]
  refine ⟨172746797430226830290133533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115164531620151220193422355 172746797430226830290133533)
  ·
    refine ⟨64780049036335061358800075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172746797430226830290133533 64780049036335061358800075)
    ·
      refine ⟨97170073554502592038200113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64780049036335061358800075 97170073554502592038200113)
      ·
        refine ⟨72877555165876944028650085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97170073554502592038200113 72877555165876944028650085)
        ·
          refine ⟨13664541593601927005371891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72877555165876944028650085 13664541593601927005371891)
          ·
            refine ⟨20496812390402890508057837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664541593601927005371891 20496812390402890508057837)
            ·
              refine ⟨7686304646401083940521689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20496812390402890508057837 7686304646401083940521689)
              ·
                refine ⟨5764728484800812955391267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7686304646401083940521689 5764728484800812955391267)
                ·
                  refine ⟨8647092727201219433086901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764728484800812955391267 8647092727201219433086901)
                  ·
                    refine ⟨810664943175114321851897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8647092727201219433086901 810664943175114321851897)
                    ·
                      rfl

theorem cell23_4736293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_4736293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736293 prefixEnd_4736293 := by exact prefixLift 4736293
  have htrace : WordTrace (prefixWord ++ tailWord_4736293) baseStart_4736293 baseEnd_4736293 := by
    simpa [prefixWord, tailWord_4736293, baseEnd_4736293] using wordTrace_append hprefix tailTrace_4736293
  have hstable : (prefixWord ++ tailWord_4736293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736293).length < 2 ^ (prefixWord ++ tailWord_4736293).sum := by decide
  have hdescent : baseEnd_4736293 < baseStart_4736293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736306 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_4736306 : Nat := 118140960795 + 4736306 * 2 ^ 59
def prefixEnd_4736306 : Nat := 4983230072969 + 3 ^ 40 * 4736306 * 2
def baseEnd_4736306 : Nat := 810667168257950471564377

theorem tailTrace_4736306 : CollatzResearch.WordTrace tailWord_4736306 prefixEnd_4736306 810667168257950471564377 := by
  unfold tailWord_4736306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43186817894794933377589193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115164847719453155673571181 43186817894794933377589193)
  ·
    refine ⟨32390113421096200033191895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43186817894794933377589193 32390113421096200033191895)
    ·
      refine ⟨48585170131644300049787843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32390113421096200033191895 48585170131644300049787843)
      ·
        refine ⟨72877755197466450074681765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48585170131644300049787843 72877755197466450074681765)
        ·
          refine ⟨13664579099524959389002831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72877755197466450074681765 13664579099524959389002831)
          ·
            refine ⟨20496868649287439083504247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664579099524959389002831 20496868649287439083504247)
            ·
              refine ⟨30745302973931158625256371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20496868649287439083504247 30745302973931158625256371)
              ·
                refine ⟨46117954460896737937884557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30745302973931158625256371 46117954460896737937884557)
                ·
                  refine ⟨17294232922836276726706709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46117954460896737937884557 17294232922836276726706709)
                  ·
                    refine ⟨810667168257950471564377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17294232922836276726706709 810667168257950471564377)
                    ·
                      rfl

theorem cell23_4736306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_4736306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736306 prefixEnd_4736306 := by exact prefixLift 4736306
  have htrace : WordTrace (prefixWord ++ tailWord_4736306) baseStart_4736306 baseEnd_4736306 := by
    simpa [prefixWord, tailWord_4736306, baseEnd_4736306] using wordTrace_append hprefix tailTrace_4736306
  have hstable : (prefixWord ++ tailWord_4736306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736306).length < 2 ^ (prefixWord ++ tailWord_4736306).sum := by decide
  have hdescent : baseEnd_4736306 < baseStart_4736306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736319 : List Nat := [1, 1, 2, 2, 4, 13]
def baseStart_4736319 : Nat := 118140960795 + 4736319 * 2 ^ 59
def prefixEnd_4736319 : Nat := 4983230072969 + 3 ^ 40 * 4736319 * 2
def baseEnd_4736319 : Nat := 10008264115318353349097

theorem tailTrace_4736319 : CollatzResearch.WordTrace tailWord_4736319 prefixEnd_4736319 10008264115318353349097 := by
  unfold tailWord_4736319
  simp only [CollatzResearch.WordTrace]
  refine ⟨172747745728132636730580011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115165163818755091153720007 172747745728132636730580011)
  ·
    refine ⟨259121618592198955095870017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172747745728132636730580011 259121618592198955095870017)
    ·
      refine ⟨194341213944149216321902513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259121618592198955095870017 194341213944149216321902513)
      ·
        refine ⟨145755910458111912241426885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194341213944149216321902513 145755910458111912241426885)
        ·
          refine ⟨27329233210895983545267541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145755910458111912241426885 27329233210895983545267541)
          ·
            refine ⟨10008264115318353349097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 27329233210895983545267541 10008264115318353349097)
            ·
              rfl

theorem cell23_4736319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 13].length) (baseStart_4736319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736319 prefixEnd_4736319 := by exact prefixLift 4736319
  have htrace : WordTrace (prefixWord ++ tailWord_4736319) baseStart_4736319 baseEnd_4736319 := by
    simpa [prefixWord, tailWord_4736319, baseEnd_4736319] using wordTrace_append hprefix tailTrace_4736319
  have hstable : (prefixWord ++ tailWord_4736319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736319).length < 2 ^ (prefixWord ++ tailWord_4736319).sum := by decide
  have hdescent : baseEnd_4736319 < baseStart_4736319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736324 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4736324 : Nat := 118140960795 + 4736324 * 2 ^ 59
def prefixEnd_4736324 : Nat := 4983230072969 + 3 ^ 40 * 4736324 * 2
def baseEnd_4736324 : Nat := 2432010747425632344268049

theorem tailTrace_4736324 : CollatzResearch.WordTrace tailWord_4736324 prefixEnd_4736324 2432010747425632344268049 := by
  unfold tailWord_4736324
  simp only [CollatzResearch.WordTrace]
  refine ⟨86373964046557261292256013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115165285395409681723008017 86373964046557261292256013)
  ·
    refine ⟨32390236517458972984596005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86373964046557261292256013 32390236517458972984596005)
    ·
      refine ⟨6073169347023557434611751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32390236517458972984596005 6073169347023557434611751)
      ·
        refine ⟨9109754020535336151917627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073169347023557434611751 9109754020535336151917627)
        ·
          refine ⟨13664631030803004227876441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109754020535336151917627 13664631030803004227876441)
          ·
            refine ⟨10248473273102253170907331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13664631030803004227876441 10248473273102253170907331)
            ·
              refine ⟨15372709909653379756360997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10248473273102253170907331 15372709909653379756360997)
              ·
                refine ⟨2882383108060008704317687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15372709909653379756360997 2882383108060008704317687)
                ·
                  refine ⟨4323574662090013056476531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882383108060008704317687 4323574662090013056476531)
                  ·
                    refine ⟨6485361993135019584714797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323574662090013056476531 6485361993135019584714797)
                    ·
                      refine ⟨2432010747425632344268049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485361993135019584714797 2432010747425632344268049)
                      ·
                        rfl

theorem cell23_4736324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4736324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736324 prefixEnd_4736324 := by exact prefixLift 4736324
  have htrace : WordTrace (prefixWord ++ tailWord_4736324) baseStart_4736324 baseEnd_4736324 := by
    simpa [prefixWord, tailWord_4736324, baseEnd_4736324] using wordTrace_append hprefix tailTrace_4736324
  have hstable : (prefixWord ++ tailWord_4736324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736324).length < 2 ^ (prefixWord ++ tailWord_4736324).sum := by decide
  have hdescent : baseEnd_4736324 < baseStart_4736324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736343 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_4736343 : Nat := 118140960795 + 4736343 * 2 ^ 59
def prefixEnd_4736343 : Nat := 4983230072969 + 3 ^ 40 * 4736343 * 2
def baseEnd_4736343 : Nat := 2432020503558067769930461

theorem tailTrace_4736343 : CollatzResearch.WordTrace tailWord_4736343 prefixEnd_4736343 2432020503558067769930461 := by
  unfold tailWord_4736343
  simp only [CollatzResearch.WordTrace]
  refine ⟨172748621080045688829453683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115165747386697125886302455 172748621080045688829453683)
  ·
    refine ⟨259122931620068533244180525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172748621080045688829453683 259122931620068533244180525)
    ·
      refine ⟨97171099357525699966567697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259122931620068533244180525 97171099357525699966567697)
      ·
        refine ⟨72878324518144274974925773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97171099357525699966567697 72878324518144274974925773)
        ·
          refine ⟨27329371694304103115597165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72878324518144274974925773 27329371694304103115597165)
          ·
            refine ⟨10248514385364038668348937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27329371694304103115597165 10248514385364038668348937)
            ·
              refine ⟨7686385789023029001261703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10248514385364038668348937 7686385789023029001261703)
              ·
                refine ⟨11529578683534543501892555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7686385789023029001261703 11529578683534543501892555)
                ·
                  refine ⟨17294368025301815252838833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11529578683534543501892555 17294368025301815252838833)
                  ·
                    refine ⟨12970776018976361439629125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17294368025301815252838833 12970776018976361439629125)
                    ·
                      refine ⟨2432020503558067769930461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12970776018976361439629125 2432020503558067769930461)
                      ·
                        rfl

theorem cell23_4736343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_4736343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736343 prefixEnd_4736343 := by exact prefixLift 4736343
  have htrace : WordTrace (prefixWord ++ tailWord_4736343) baseStart_4736343 baseEnd_4736343 := by
    simpa [prefixWord, tailWord_4736343, baseEnd_4736343] using wordTrace_append hprefix tailTrace_4736343
  have hstable : (prefixWord ++ tailWord_4736343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736343).length < 2 ^ (prefixWord ++ tailWord_4736343).sum := by decide
  have hdescent : baseEnd_4736343 < baseStart_4736343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736364 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_4736364 : Nat := 118140960795 + 4736364 * 2 ^ 59
def prefixEnd_4736364 : Nat := 4983230072969 + 3 ^ 40 * 4736364 * 2
def baseEnd_4736364 : Nat := 2432031286651812187767865

theorem tailTrace_4736364 : CollatzResearch.WordTrace tailWord_4736364 prefixEnd_4736364 2432031286651812187767865 := by
  unfold tailWord_4736364
  simp only [CollatzResearch.WordTrace]
  refine ⟨86374693506484804707984073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115166258008646406277312097 86374693506484804707984073)
  ·
    refine ⟨64781020129863603530988055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86374693506484804707984073 64781020129863603530988055)
    ·
      refine ⟨97171530194795405296482083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64781020129863603530988055 97171530194795405296482083)
      ·
        refine ⟨145757295292193107944723125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97171530194795405296482083 145757295292193107944723125)
        ·
          refine ⟨13664746433643103869817793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145757295292193107944723125 13664746433643103869817793)
          ·
            refine ⟨10248559825232327902363345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13664746433643103869817793 10248559825232327902363345)
            ·
              refine ⟨7686419868924245926772509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10248559825232327902363345 7686419868924245926772509)
              ·
                refine ⟨2882407450846592222539691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7686419868924245926772509 2882407450846592222539691)
                ·
                  refine ⟨4323611176269888333809537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882407450846592222539691 4323611176269888333809537)
                  ·
                    refine ⟨3242708382202416250357153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323611176269888333809537 3242708382202416250357153)
                    ·
                      refine ⟨2432031286651812187767865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242708382202416250357153 2432031286651812187767865)
                      ·
                        rfl

theorem cell23_4736364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_4736364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736364 prefixEnd_4736364 := by exact prefixLift 4736364
  have htrace : WordTrace (prefixWord ++ tailWord_4736364) baseStart_4736364 baseEnd_4736364 := by
    simpa [prefixWord, tailWord_4736364, baseEnd_4736364] using wordTrace_append hprefix tailTrace_4736364
  have hstable : (prefixWord ++ tailWord_4736364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736364).length < 2 ^ (prefixWord ++ tailWord_4736364).sum := by decide
  have hdescent : baseEnd_4736364 < baseStart_4736364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736396 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_4736396 : Nat := 118140960795 + 4736396 * 2 ^ 59
def prefixEnd_4736396 : Nat := 4983230072969 + 3 ^ 40 * 4736396 * 2
def baseEnd_4736396 : Nat := 810682572677585354189239

theorem tailTrace_4736396 : CollatzResearch.WordTrace tailWord_4736396 prefixEnd_4736396 810682572677585354189239 := by
  unfold tailWord_4736396
  simp only [CollatzResearch.WordTrace]
  refine ⟨86375277074426839440566521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115167036099235785920755361 86375277074426839440566521)
  ·
    refine ⟨64781457805820129580424891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86375277074426839440566521 64781457805820129580424891)
    ·
      refine ⟨97172186708730194370637337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64781457805820129580424891 97172186708730194370637337)
      ·
        refine ⟨72879140031547645777978003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97172186708730194370637337 72879140031547645777978003)
        ·
          refine ⟨109318710047321468666967005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72879140031547645777978003 109318710047321468666967005)
          ·
            refine ⟨40994516267745550750112627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109318710047321468666967005 40994516267745550750112627)
            ·
              refine ⟨61491774401618326125168941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40994516267745550750112627 61491774401618326125168941)
              ·
                refine ⟨23059415400606872296938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61491774401618326125168941 23059415400606872296938353)
                ·
                  refine ⟨17294561550455154222703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23059415400606872296938353 17294561550455154222703765)
                  ·
                    refine ⟨810682572677585354189239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17294561550455154222703765 810682572677585354189239)
                    ·
                      rfl

theorem cell23_4736396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_4736396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736396 prefixEnd_4736396 := by exact prefixLift 4736396
  have htrace : WordTrace (prefixWord ++ tailWord_4736396) baseStart_4736396 baseEnd_4736396 := by
    simpa [prefixWord, tailWord_4736396, baseEnd_4736396] using wordTrace_append hprefix tailTrace_4736396
  have hstable : (prefixWord ++ tailWord_4736396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736396).length < 2 ^ (prefixWord ++ tailWord_4736396).sum := by decide
  have hdescent : baseEnd_4736396 < baseStart_4736396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736423 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4736423 : Nat := 118140960795 + 4736423 * 2 ^ 59
def prefixEnd_4736423 : Nat := 4983230072969 + 3 ^ 40 * 4736423 * 2
def baseEnd_4736423 : Nat := 2432061582010427456930093

theorem tailTrace_4736423 : CollatzResearch.WordTrace tailWord_4736423 prefixEnd_4736423 2432061582010427456930093 := by
  unfold tailWord_4736423
  simp only [CollatzResearch.WordTrace]
  refine ⟨172751538919755862492365923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115167692613170574994910615 172751538919755862492365923)
  ·
    refine ⟨259127308379633793738548885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172751538919755862492365923 259127308379633793738548885)
    ·
      refine ⟨12146592580295334081494479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259127308379633793738548885 12146592580295334081494479)
      ·
        refine ⟨18219888870443001122241719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12146592580295334081494479 18219888870443001122241719)
        ·
          refine ⟨27329833305664501683362579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18219888870443001122241719 27329833305664501683362579)
          ·
            refine ⟨40994749958496752525043869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27329833305664501683362579 40994749958496752525043869)
            ·
              refine ⟨15373031234436282196891451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40994749958496752525043869 15373031234436282196891451)
              ·
                refine ⟨23059546851654423295337177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15373031234436282196891451 23059546851654423295337177)
                ·
                  refine ⟨17294660138740817471502883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23059546851654423295337177 17294660138740817471502883)
                  ·
                    refine ⟨25941990208111226207254325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17294660138740817471502883 25941990208111226207254325)
                    ·
                      refine ⟨2432061582010427456930093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25941990208111226207254325 2432061582010427456930093)
                      ·
                        rfl

theorem cell23_4736423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4736423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736423 prefixEnd_4736423 := by exact prefixLift 4736423
  have htrace : WordTrace (prefixWord ++ tailWord_4736423) baseStart_4736423 baseEnd_4736423 := by
    simpa [prefixWord, tailWord_4736423, baseEnd_4736423] using wordTrace_append hprefix tailTrace_4736423
  have hstable : (prefixWord ++ tailWord_4736423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736423).length < 2 ^ (prefixWord ++ tailWord_4736423).sum := by decide
  have hdescent : baseEnd_4736423 < baseStart_4736423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736437 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_4736437 : Nat := 118140960795 + 4736437 * 2 ^ 59
def prefixEnd_4736437 : Nat := 4983230072969 + 3 ^ 40 * 4736437 * 2
def baseEnd_4736437 : Nat := 2432068770739590402155029

theorem tailTrace_4736437 : CollatzResearch.WordTrace tailWord_4736437 prefixEnd_4736437 2432068770739590402155029 := by
  unfold tailWord_4736437
  simp only [CollatzResearch.WordTrace]
  refine ⟨172752049541705142883375565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115168033027803428588917043 172752049541705142883375565)
  ·
    refine ⟨64782018578139428581265837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172752049541705142883375565 64782018578139428581265837)
    ·
      refine ⟨24293256966802285717974689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64782018578139428581265837 24293256966802285717974689)
      ·
        refine ⟨18219942725101714288481017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24293256966802285717974689 18219942725101714288481017)
        ·
          refine ⟨13664957043826285716360763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18219942725101714288481017 13664957043826285716360763)
          ·
            refine ⟨20497435565739428574541145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664957043826285716360763 20497435565739428574541145)
            ·
              refine ⟨15373076674304571430905859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20497435565739428574541145 15373076674304571430905859)
              ·
                refine ⟨23059615011456857146358789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15373076674304571430905859 23059615011456857146358789)
                ·
                  refine ⟨4323677814648160714942273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23059615011456857146358789 4323677814648160714942273)
                  ·
                    refine ⟨3242758360986120536206705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323677814648160714942273 3242758360986120536206705)
                    ·
                      refine ⟨2432068770739590402155029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242758360986120536206705 2432068770739590402155029)
                      ·
                        rfl

theorem cell23_4736437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_4736437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736437 prefixEnd_4736437 := by exact prefixLift 4736437
  have htrace : WordTrace (prefixWord ++ tailWord_4736437) baseStart_4736437 baseEnd_4736437 := by
    simpa [prefixWord, tailWord_4736437, baseEnd_4736437] using wordTrace_append hprefix tailTrace_4736437
  have hstable : (prefixWord ++ tailWord_4736437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736437).length < 2 ^ (prefixWord ++ tailWord_4736437).sum := by decide
  have hdescent : baseEnd_4736437 < baseStart_4736437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736473 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_4736473 : Nat := 118140960795 + 4736473 * 2 ^ 59
def prefixEnd_4736473 : Nat := 4983230072969 + 3 ^ 40 * 4736473 * 2
def baseEnd_4736473 : Nat := 810695752014384087101621

theorem tailTrace_4736473 : CollatzResearch.WordTrace tailWord_4736473 prefixEnd_4736473 810695752014384087101621 := by
  unfold tailWord_4736473
  simp only [CollatzResearch.WordTrace]
  refine ⟨172753362569574721031686073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115168908379716480687790715 172753362569574721031686073)
  ·
    refine ⟨129565021927181040773764555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172753362569574721031686073 129565021927181040773764555)
    ·
      refine ⟨194347532890771561160646833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129565021927181040773764555 194347532890771561160646833)
      ·
        refine ⟨145760649668078670870485125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194347532890771561160646833 145760649668078670870485125)
        ·
          refine ⟨27330121812764750788215961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145760649668078670870485125 27330121812764750788215961)
          ·
            refine ⟨20497591359573563091161971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27330121812764750788215961 20497591359573563091161971)
            ·
              refine ⟨30746387039360344636742957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20497591359573563091161971 30746387039360344636742957)
              ·
                refine ⟨11529895139760129238778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30746387039360344636742957 11529895139760129238778609)
                ·
                  refine ⟨8647421354820096929083957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11529895139760129238778609 8647421354820096929083957)
                  ·
                    refine ⟨810695752014384087101621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8647421354820096929083957 810695752014384087101621)
                    ·
                      rfl

theorem cell23_4736473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_4736473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736473 prefixEnd_4736473 := by exact prefixLift 4736473
  have htrace : WordTrace (prefixWord ++ tailWord_4736473) baseStart_4736473 baseEnd_4736473 := by
    simpa [prefixWord, tailWord_4736473, baseEnd_4736473] using wordTrace_append hprefix tailTrace_4736473
  have hstable : (prefixWord ++ tailWord_4736473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736473).length < 2 ^ (prefixWord ++ tailWord_4736473).sum := by decide
  have hdescent : baseEnd_4736473 < baseStart_4736473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736483 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4736483 : Nat := 118140960795 + 4736483 * 2 ^ 59
def prefixEnd_4736483 : Nat := 4983230072969 + 3 ^ 40 * 4736483 * 2
def baseEnd_4736483 : Nat := 2432092390849697222179817

theorem tailTrace_4736483 : CollatzResearch.WordTrace tailWord_4736483 prefixEnd_4736483 2432092390849697222179817 := by
  unfold tailWord_4736483
  simp only [CollatzResearch.WordTrace]
  refine ⟨172753727299538492739550103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115169151533025661826366735 172753727299538492739550103)
  ·
    refine ⟨259130590949307739109325155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172753727299538492739550103 259130590949307739109325155)
    ·
      refine ⟨388695886423961608663987733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259130590949307739109325155 388695886423961608663987733)
      ·
        refine ⟨18220119676123200406124425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 388695886423961608663987733 18220119676123200406124425)
        ·
          refine ⟨13665089757092400304593319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18220119676123200406124425 13665089757092400304593319)
          ·
            refine ⟨20497634635638600456889979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13665089757092400304593319 20497634635638600456889979)
            ·
              refine ⟨30746451953457900685334969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20497634635638600456889979 30746451953457900685334969)
              ·
                refine ⟨23059838965093425514001227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30746451953457900685334969 23059838965093425514001227)
                ·
                  refine ⟨34589758447640138271001841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23059838965093425514001227 34589758447640138271001841)
                  ·
                    refine ⟨25942318835730103703251381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34589758447640138271001841 25942318835730103703251381)
                    ·
                      refine ⟨2432092390849697222179817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25942318835730103703251381 2432092390849697222179817)
                      ·
                        rfl

theorem cell23_4736483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4736483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736483 prefixEnd_4736483 := by exact prefixLift 4736483
  have htrace : WordTrace (prefixWord ++ tailWord_4736483) baseStart_4736483 baseEnd_4736483 := by
    simpa [prefixWord, tailWord_4736483, baseEnd_4736483] using wordTrace_append hprefix tailTrace_4736483
  have hstable : (prefixWord ++ tailWord_4736483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736483).length < 2 ^ (prefixWord ++ tailWord_4736483).sum := by decide
  have hdescent : baseEnd_4736483 < baseStart_4736483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736570 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_4736570 : Nat := 118140960795 + 4736570 * 2 ^ 59
def prefixEnd_4736570 : Nat := 4983230072969 + 3 ^ 40 * 4736570 * 2
def baseEnd_4736570 : Nat := 2432137063666638381791917

theorem tailTrace_4736570 : CollatzResearch.WordTrace tailWord_4736570 prefixEnd_4736570 2432137063666638381791917 := by
  unfold tailWord_4736570
  simp only [CollatzResearch.WordTrace]
  refine ⟨43189225112555826649491791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115171266966815537731978109 43189225112555826649491791)
  ·
    refine ⟨64783837668833739974237687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43189225112555826649491791 64783837668833739974237687)
    ·
      refine ⟨97175756503250609961356531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64783837668833739974237687 97175756503250609961356531)
      ·
        refine ⟨145763634754875914942034797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97175756503250609961356531 145763634754875914942034797)
        ·
          refine ⟨54661363033078468103263049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145763634754875914942034797 54661363033078468103263049)
          ·
            refine ⟨40996022274808851077447287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54661363033078468103263049 40996022274808851077447287)
            ·
              refine ⟨61494033412213276616170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40996022274808851077447287 61494033412213276616170931)
              ·
                refine ⟨92241050118319914924256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61494033412213276616170931 92241050118319914924256397)
                ·
                  refine ⟨34590393794369968096596149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92241050118319914924256397 34590393794369968096596149)
                  ·
                    refine ⟨3242849418222184509055889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34590393794369968096596149 3242849418222184509055889)
                    ·
                      refine ⟨2432137063666638381791917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242849418222184509055889 2432137063666638381791917)
                      ·
                        rfl

theorem cell23_4736570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_4736570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736570 prefixEnd_4736570 := by exact prefixLift 4736570
  have htrace : WordTrace (prefixWord ++ tailWord_4736570) baseStart_4736570 baseEnd_4736570 := by
    simpa [prefixWord, tailWord_4736570, baseEnd_4736570] using wordTrace_append hprefix tailTrace_4736570
  have hstable : (prefixWord ++ tailWord_4736570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736570).length < 2 ^ (prefixWord ++ tailWord_4736570).sum := by decide
  have hdescent : baseEnd_4736570 < baseStart_4736570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736577 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4736577 : Nat := 118140960795 + 4736577 * 2 ^ 59
def prefixEnd_4736577 : Nat := 4983230072969 + 3 ^ 40 * 4736577 * 2
def baseEnd_4736577 : Nat := 2432140658031219854404385

theorem tailTrace_4736577 : CollatzResearch.WordTrace tailWord_4736577 prefixEnd_4736577 2432140658031219854404385 := by
  unfold tailWord_4736577
  simp only [CollatzResearch.WordTrace]
  refine ⟨172757155761197946793471985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115171437174131964528981323 172757155761197946793471985)
  ·
    refine ⟨129567866820898460095103989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172757155761197946793471985 129567866820898460095103989)
    ·
      refine ⟨12146987514459230633915999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129567866820898460095103989 12146987514459230633915999)
      ·
        refine ⟨18220481271688845950873999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12146987514459230633915999 18220481271688845950873999)
        ·
          refine ⟨27330721907533268926310999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18220481271688845950873999 27330721907533268926310999)
          ·
            refine ⟨40996082861299903389466499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27330721907533268926310999 40996082861299903389466499)
            ·
              refine ⟨61494124291949855084199749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40996082861299903389466499 61494124291949855084199749)
              ·
                refine ⟨11530148304740597828287453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61494124291949855084199749 11530148304740597828287453)
                ·
                  refine ⟨4323805614277724185607795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11530148304740597828287453 4323805614277724185607795)
                  ·
                    refine ⟨6485708421416586278411693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323805614277724185607795 6485708421416586278411693)
                    ·
                      refine ⟨2432140658031219854404385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485708421416586278411693 2432140658031219854404385)
                      ·
                        rfl

theorem cell23_4736577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4736577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736577 prefixEnd_4736577 := by exact prefixLift 4736577
  have htrace : WordTrace (prefixWord ++ tailWord_4736577) baseStart_4736577 baseEnd_4736577 := by
    simpa [prefixWord, tailWord_4736577, baseEnd_4736577] using wordTrace_append hprefix tailTrace_4736577
  have hstable : (prefixWord ++ tailWord_4736577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736577).length < 2 ^ (prefixWord ++ tailWord_4736577).sum := by decide
  have hdescent : baseEnd_4736577 < baseStart_4736577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736593 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_4736593 : Nat := 118140960795 + 4736593 * 2 ^ 59
def prefixEnd_4736593 : Nat := 4983230072969 + 3 ^ 40 * 4736593 * 2
def baseEnd_4736593 : Nat := 810716291240563930601437

theorem tailTrace_4736593 : CollatzResearch.WordTrace tailWord_4736593 prefixEnd_4736593 810716291240563930601437 := by
  unfold tailWord_4736593
  simp only [CollatzResearch.WordTrace]
  refine ⟨172757739329139981526054433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115171826219426654350702955 172757739329139981526054433)
  ·
    refine ⟨129568304496854986144540825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172757739329139981526054433 129568304496854986144540825)
    ·
      refine ⟨97176228372641239608405619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129568304496854986144540825 97176228372641239608405619)
      ·
        refine ⟨145764342558961859412608429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97176228372641239608405619 145764342558961859412608429)
        ·
          refine ⟨54661628459610697279728161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145764342558961859412608429 54661628459610697279728161)
          ·
            refine ⟨40996221344708022959796121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54661628459610697279728161 40996221344708022959796121)
            ·
              refine ⟨30747166008531017219847091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40996221344708022959796121 30747166008531017219847091)
              ·
                refine ⟨46120749012796525829770637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30747166008531017219847091 46120749012796525829770637)
                ·
                  refine ⟨17295280879798697186163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46120749012796525829770637 17295280879798697186163989)
                  ·
                    refine ⟨810716291240563930601437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17295280879798697186163989 810716291240563930601437)
                    ·
                      rfl

theorem cell23_4736593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_4736593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736593 prefixEnd_4736593 := by exact prefixLift 4736593
  have htrace : WordTrace (prefixWord ++ tailWord_4736593) baseStart_4736593 baseEnd_4736593 := by
    simpa [prefixWord, tailWord_4736593, baseEnd_4736593] using wordTrace_append hprefix tailTrace_4736593
  have hstable : (prefixWord ++ tailWord_4736593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736593).length < 2 ^ (prefixWord ++ tailWord_4736593).sum := by decide
  have hdescent : baseEnd_4736593 < baseStart_4736593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736604 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4736604 : Nat := 118140960795 + 4736604 * 2 ^ 59
def prefixEnd_4736604 : Nat := 4983230072969 + 3 ^ 40 * 4736604 * 2
def baseEnd_4736604 : Nat := 2432154522008891248766761

theorem tailTrace_4736604 : CollatzResearch.WordTrace tailWord_4736604 prefixEnd_4736604 2432154522008891248766761 := by
  unfold tailWord_4736604
  simp only [CollatzResearch.WordTrace]
  refine ⟨86379070266050065202352433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115172093688066753603136577 86379070266050065202352433)
  ·
    refine ⟨64784302699537548901764325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86379070266050065202352433 64784302699537548901764325)
    ·
      refine ⟨12147056756163290419080811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64784302699537548901764325 12147056756163290419080811)
      ·
        refine ⟨18220585134244935628621217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12147056756163290419080811 18220585134244935628621217)
        ·
          refine ⟨13665438850683701721465913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18220585134244935628621217 13665438850683701721465913)
          ·
            refine ⟨10249079138012776291099435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13665438850683701721465913 10249079138012776291099435)
            ·
              refine ⟨15373618707019164436649153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249079138012776291099435 15373618707019164436649153)
              ·
                refine ⟨11530214030264373327486865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15373618707019164436649153 11530214030264373327486865)
                ·
                  refine ⟨8647660522698279995615149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11530214030264373327486865 8647660522698279995615149)
                  ·
                    refine ⟨3242872696011854998355681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8647660522698279995615149 3242872696011854998355681)
                    ·
                      refine ⟨2432154522008891248766761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242872696011854998355681 2432154522008891248766761)
                      ·
                        rfl

theorem cell23_4736604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4736604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736604 prefixEnd_4736604 := by exact prefixLift 4736604
  have htrace : WordTrace (prefixWord ++ tailWord_4736604) baseStart_4736604 baseEnd_4736604 := by
    simpa [prefixWord, tailWord_4736604, baseEnd_4736604] using wordTrace_append hprefix tailTrace_4736604
  have hstable : (prefixWord ++ tailWord_4736604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736604).length < 2 ^ (prefixWord ++ tailWord_4736604).sum := by decide
  have hdescent : baseEnd_4736604 < baseStart_4736604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736611 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4736611 : Nat := 118140960795 + 4736611 * 2 ^ 59
def prefixEnd_4736611 : Nat := 4983230072969 + 3 ^ 40 * 4736611 * 2
def baseEnd_4736611 : Nat := 2432158116373472721379229

theorem tailTrace_4736611 : CollatzResearch.WordTrace tailWord_4736611 prefixEnd_4736611 2432158116373472721379229 := by
  unfold tailWord_4736611
  simp only [CollatzResearch.WordTrace]
  refine ⟨172758395843074770600209687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115172263895383180400139791 172758395843074770600209687)
  ·
    refine ⟨259137593764612155900314531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172758395843074770600209687 259137593764612155900314531)
    ·
      refine ⟨388706390646918233850471797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259137593764612155900314531 388706390646918233850471797)
      ·
        refine ⟨36441224123148584423481731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 388706390646918233850471797 36441224123148584423481731)
        ·
          refine ⟨54661836184722876635222597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36441224123148584423481731 54661836184722876635222597)
          ·
            refine ⟨10249094284635539369104237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54661836184722876635222597 10249094284635539369104237)
            ·
              refine ⟨3843410356738327263414089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10249094284635539369104237 3843410356738327263414089)
              ·
                refine ⟨2882557767553745447560567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3843410356738327263414089 2882557767553745447560567)
                ·
                  refine ⟨4323836651330618171340851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882557767553745447560567 4323836651330618171340851)
                  ·
                    refine ⟨6485754976995927257011277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323836651330618171340851 6485754976995927257011277)
                    ·
                      refine ⟨2432158116373472721379229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485754976995927257011277 2432158116373472721379229)
                      ·
                        rfl

theorem cell23_4736611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4736611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736611 prefixEnd_4736611 := by exact prefixLift 4736611
  have htrace : WordTrace (prefixWord ++ tailWord_4736611) baseStart_4736611 baseEnd_4736611 := by
    simpa [prefixWord, tailWord_4736611, baseEnd_4736611] using wordTrace_append hprefix tailTrace_4736611
  have hstable : (prefixWord ++ tailWord_4736611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736611).length < 2 ^ (prefixWord ++ tailWord_4736611).sum := by decide
  have hdescent : baseEnd_4736611 < baseStart_4736611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736620 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_4736620 : Nat := 118140960795 + 4736620 * 2 ^ 59
def prefixEnd_4736620 : Nat := 4983230072969 + 3 ^ 40 * 4736620 * 2
def baseEnd_4736620 : Nat := 2432162737699363186166687

theorem tailTrace_4736620 : CollatzResearch.WordTrace tailWord_4736620 prefixEnd_4736620 2432162737699363186166687 := by
  unfold tailWord_4736620
  simp only [CollatzResearch.WordTrace]
  refine ⟨86379362050021082568643657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115172482733361443424858209 86379362050021082568643657)
  ·
    refine ⟨64784521537515811926482743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86379362050021082568643657 64784521537515811926482743)
    ·
      refine ⟨97176782306273717889724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64784521537515811926482743 97176782306273717889724115)
      ·
        refine ⟨145765173459410576834586173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97176782306273717889724115 145765173459410576834586173)
        ·
          refine ⟨54661940047278966312969815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145765173459410576834586173 54661940047278966312969815)
          ·
            refine ⟨81992910070918449469454723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54661940047278966312969815 81992910070918449469454723)
            ·
              refine ⟨122989365106377674204182085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81992910070918449469454723 122989365106377674204182085)
              ·
                refine ⟨23060505957445813913284141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122989365106377674204182085 23060505957445813913284141)
                ·
                  refine ⟨8647689734042180217481553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23060505957445813913284141 8647689734042180217481553)
                  ·
                    refine ⟨6485767300531635163111165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8647689734042180217481553 6485767300531635163111165)
                    ·
                      refine ⟨2432162737699363186166687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485767300531635163111165 2432162737699363186166687)
                      ·
                        rfl

theorem cell23_4736620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_4736620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736620 prefixEnd_4736620 := by exact prefixLift 4736620
  have htrace : WordTrace (prefixWord ++ tailWord_4736620) baseStart_4736620 baseEnd_4736620 := by
    simpa [prefixWord, tailWord_4736620, baseEnd_4736620] using wordTrace_append hprefix tailTrace_4736620
  have hstable : (prefixWord ++ tailWord_4736620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736620).length < 2 ^ (prefixWord ++ tailWord_4736620).sum := by decide
  have hdescent : baseEnd_4736620 < baseStart_4736620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736637 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_4736637 : Nat := 118140960795 + 4736637 * 2 ^ 59
def prefixEnd_4736637 : Nat := 4983230072969 + 3 ^ 40 * 4736637 * 2
def baseEnd_4736637 : Nat := 2432171466870489619654109

theorem tailTrace_4736637 : CollatzResearch.WordTrace tailWord_4736637 prefixEnd_4736637 2432171466870489619654109 := by
  unfold tailWord_4736637
  simp only [CollatzResearch.WordTrace]
  refine ⟨172759344140980577040656165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115172896093987051360437443 172759344140980577040656165)
  ·
    refine ⟨32392377026433858195123031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172759344140980577040656165 32392377026433858195123031)
    ·
      refine ⟨48588565539650787292684547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32392377026433858195123031 48588565539650787292684547)
      ·
        refine ⟨72882848309476180939026821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48588565539650787292684547 72882848309476180939026821)
        ·
          refine ⟨13665534058026783926067529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72882848309476180939026821 13665534058026783926067529)
          ·
            refine ⟨10249150543520087944550647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13665534058026783926067529 10249150543520087944550647)
            ·
              refine ⟨15373725815280131916825971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249150543520087944550647 15373725815280131916825971)
              ·
                refine ⟨23060588722920197875238957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15373725815280131916825971 23060588722920197875238957)
                ·
                  refine ⟨8647720771095074203214609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23060588722920197875238957 8647720771095074203214609)
                  ·
                    refine ⟨6485790578321305652410957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8647720771095074203214609 6485790578321305652410957)
                    ·
                      refine ⟨2432171466870489619654109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6485790578321305652410957 2432171466870489619654109)
                      ·
                        rfl

theorem cell23_4736637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_4736637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736637 prefixEnd_4736637 := by exact prefixLift 4736637
  have htrace : WordTrace (prefixWord ++ tailWord_4736637) baseStart_4736637 baseEnd_4736637 := by
    simpa [prefixWord, tailWord_4736637, baseEnd_4736637] using wordTrace_append hprefix tailTrace_4736637
  have hstable : (prefixWord ++ tailWord_4736637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736637).length < 2 ^ (prefixWord ++ tailWord_4736637).sum := by decide
  have hdescent : baseEnd_4736637 < baseStart_4736637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736668 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4736668 : Nat := 118140960795 + 4736668 * 2 ^ 59
def prefixEnd_4736668 : Nat := 4983230072969 + 3 ^ 40 * 4736668 * 2
def baseEnd_4736668 : Nat := 2432187384770778998366467

theorem tailTrace_4736668 : CollatzResearch.WordTrace tailWord_4736668 prefixEnd_4736668 2432187384770778998366467 := by
  unfold tailWord_4736668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86380237401934134667517329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115173649869245512890023105 86380237401934134667517329)
  ·
    refine ⟨64785178051450601000637997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86380237401934134667517329 64785178051450601000637997)
    ·
      refine ⟨24294441769293975375239249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64785178051450601000637997 24294441769293975375239249)
      ·
        refine ⟨18220831326970481531429437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24294441769293975375239249 18220831326970481531429437)
        ·
          refine ⟨6832811747613930574286039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18220831326970481531429437 6832811747613930574286039)
          ·
            refine ⟨10249217621420895861429059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832811747613930574286039 10249217621420895861429059)
            ·
              refine ⟨15373826432131343792143589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249217621420895861429059 15373826432131343792143589)
              ·
                refine ⟨2882592456024626961026923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15373826432131343792143589 2882592456024626961026923)
                ·
                  refine ⟨4323888684036940441540385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882592456024626961026923 4323888684036940441540385)
                  ·
                    refine ⟨3242916513027705331155289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323888684036940441540385 3242916513027705331155289)
                    ·
                      refine ⟨2432187384770778998366467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242916513027705331155289 2432187384770778998366467)
                      ·
                        rfl

theorem cell23_4736668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4736668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736668 prefixEnd_4736668 := by exact prefixLift 4736668
  have htrace : WordTrace (prefixWord ++ tailWord_4736668) baseStart_4736668 baseEnd_4736668 := by
    simpa [prefixWord, tailWord_4736668, baseEnd_4736668] using wordTrace_append hprefix tailTrace_4736668
  have hstable : (prefixWord ++ tailWord_4736668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736668).length < 2 ^ (prefixWord ++ tailWord_4736668).sum := by decide
  have hdescent : baseEnd_4736668 < baseStart_4736668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736674 : List Nat := [3, 3, 1, 4, 1, 2, 1, 8]
def baseStart_4736674 : Nat := 118140960795 + 4736674 * 2 ^ 59
def prefixEnd_4736674 : Nat := 4983230072969 + 3 ^ 40 * 4736674 * 2
def baseEnd_4736674 : Nat := 90081128357581702773757

theorem tailTrace_4736674 : CollatzResearch.WordTrace tailWord_4736674 prefixEnd_4736674 90081128357581702773757 := by
  unfold tailWord_4736674
  simp only [CollatzResearch.WordTrace]
  refine ⟨43190173410461633089938269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115173795761231021573168717 43190173410461633089938269)
  ·
    refine ⟨16196315028923112408726851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43190173410461633089938269 16196315028923112408726851)
    ·
      refine ⟨24294472543384668613090277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16196315028923112408726851 24294472543384668613090277)
      ·
        refine ⟨4555213601884625364954427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24294472543384668613090277 4555213601884625364954427)
        ·
          refine ⟨6832820402826938047431641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555213601884625364954427 6832820402826938047431641)
          ·
            refine ⟨5124615302120203535573731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832820402826938047431641 5124615302120203535573731)
            ·
              refine ⟨7686922953180305303360597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124615302120203535573731 7686922953180305303360597)
              ·
                refine ⟨90081128357581702773757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7686922953180305303360597 90081128357581702773757)
                ·
                  rfl

theorem cell23_4736674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_4736674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736674 prefixEnd_4736674 := by exact prefixLift 4736674
  have htrace : WordTrace (prefixWord ++ tailWord_4736674) baseStart_4736674 baseEnd_4736674 := by
    simpa [prefixWord, tailWord_4736674, baseEnd_4736674] using wordTrace_append hprefix tailTrace_4736674
  have hstable : (prefixWord ++ tailWord_4736674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736674).length < 2 ^ (prefixWord ++ tailWord_4736674).sum := by decide
  have hdescent : baseEnd_4736674 < baseStart_4736674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736677 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_4736677 : Nat := 118140960795 + 4736677 * 2 ^ 59
def prefixEnd_4736677 : Nat := 4983230072969 + 3 ^ 40 * 4736677 * 2
def baseEnd_4736677 : Nat := 2432192006096669463153925

theorem tailTrace_4736677 : CollatzResearch.WordTrace tailWord_4736677 prefixEnd_4736677 2432192006096669463153925 := by
  unfold tailWord_4736677
  simp only [CollatzResearch.WordTrace]
  refine ⟨172760803060835663872112285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115173868707223775914741523 172760803060835663872112285)
  ·
    refine ⟨64785301147813373952042107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172760803060835663872112285 64785301147813373952042107)
    ·
      refine ⟨97177951721720060928063161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64785301147813373952042107 97177951721720060928063161)
      ·
        refine ⟨72883463791290045696047371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97177951721720060928063161 72883463791290045696047371)
        ·
          refine ⟨109325195686935068544071057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72883463791290045696047371 109325195686935068544071057)
          ·
            refine ⟨81993896765201301408053293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109325195686935068544071057 81993896765201301408053293)
            ·
              refine ⟨30747711286950488028019985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81993896765201301408053293 30747711286950488028019985)
              ·
                refine ⟨23060783465212866021014989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30747711286950488028019985 23060783465212866021014989)
                ·
                  refine ⟨8647793799454824757880621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23060783465212866021014989 8647793799454824757880621)
                  ·
                    refine ⟨3242922674795559284205233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8647793799454824757880621 3242922674795559284205233)
                    ·
                      refine ⟨2432192006096669463153925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3242922674795559284205233 2432192006096669463153925)
                      ·
                        rfl

theorem cell23_4736677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_4736677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736677 prefixEnd_4736677 := by exact prefixLift 4736677
  have htrace : WordTrace (prefixWord ++ tailWord_4736677) baseStart_4736677 baseEnd_4736677 := by
    simpa [prefixWord, tailWord_4736677, baseEnd_4736677] using wordTrace_append hprefix tailTrace_4736677
  have hstable : (prefixWord ++ tailWord_4736677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736677).length < 2 ^ (prefixWord ++ tailWord_4736677).sum := by decide
  have hdescent : baseEnd_4736677 < baseStart_4736677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736730 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_4736730 : Nat := 118140960795 + 4736730 * 2 ^ 59
def prefixEnd_4736730 : Nat := 4983230072969 + 3 ^ 40 * 4736730 * 2
def baseEnd_4736730 : Nat := 270246580063484195087909

theorem tailTrace_4736730 : CollatzResearch.WordTrace tailWord_4736730 prefixEnd_4736730 270246580063484195087909 := by
  unfold tailWord_4736730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43190684032410913480947911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115175157419762435949194429 43190684032410913480947911)
  ·
    refine ⟨64786026048616370221421867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43190684032410913480947911 64786026048616370221421867)
    ·
      refine ⟨97179039072924555332132801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64786026048616370221421867 97179039072924555332132801)
      ·
        refine ⟨72884279304693416499099601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97179039072924555332132801 72884279304693416499099601)
        ·
          refine ⟨54663209478520062374324701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72884279304693416499099601 54663209478520062374324701)
          ·
            refine ⟨20498703554445023390371763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54663209478520062374324701 20498703554445023390371763)
            ·
              refine ⟨30748055331667535085557645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20498703554445023390371763 30748055331667535085557645)
              ·
                refine ⟨11530520749375325657084117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30748055331667535085557645 11530520749375325657084117)
                ·
                  refine ⟨270246580063484195087909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11530520749375325657084117 270246580063484195087909)
                  ·
                    rfl

theorem cell23_4736730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_4736730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736730 prefixEnd_4736730 := by exact prefixLift 4736730
  have htrace : WordTrace (prefixWord ++ tailWord_4736730) baseStart_4736730 baseEnd_4736730 := by
    simpa [prefixWord, tailWord_4736730, baseEnd_4736730] using wordTrace_append hprefix tailTrace_4736730
  have hstable : (prefixWord ++ tailWord_4736730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736730).length < 2 ^ (prefixWord ++ tailWord_4736730).sum := by decide
  have hdescent : baseEnd_4736730 < baseStart_4736730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736837 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 6]
def baseStart_4736837 : Nat := 118140960795 + 4736837 * 2 ^ 59
def prefixEnd_4736837 : Nat := 4983230072969 + 3 ^ 40 * 4736837 * 2
def baseEnd_4736837 : Nat := 270252684777932093017021

theorem tailTrace_4736837 : CollatzResearch.WordTrace tailWord_4736837 prefixEnd_4736837 270252684777932093017021 := by
  unfold tailWord_4736837
  simp only [CollatzResearch.WordTrace]
  refine ⟨172766638740256011197936765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115177759160170674131957843 172766638740256011197936765)
  ·
    refine ⟨64787489527596004199226287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172766638740256011197936765 64787489527596004199226287)
    ·
      refine ⟨97181234291394006298839431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64787489527596004199226287 97181234291394006298839431)
      ·
        refine ⟨145771851437091009448259147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97181234291394006298839431 145771851437091009448259147)
        ·
          refine ⟨218657777155636514172388721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145771851437091009448259147 218657777155636514172388721)
          ·
            refine ⟨163993332866727385629291541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218657777155636514172388721 163993332866727385629291541)
            ·
              refine ⟨7687187478127846201373041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163993332866727385629291541 7687187478127846201373041)
              ·
                refine ⟨5765390608595884651029781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7687187478127846201373041 5765390608595884651029781)
                ·
                  refine ⟨270252684777932093017021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5765390608595884651029781 270252684777932093017021)
                  ·
                    rfl

theorem cell23_4736837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_4736837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736837 prefixEnd_4736837 := by exact prefixLift 4736837
  have htrace : WordTrace (prefixWord ++ tailWord_4736837) baseStart_4736837 baseEnd_4736837 := by
    simpa [prefixWord, tailWord_4736837, baseEnd_4736837] using wordTrace_append hprefix tailTrace_4736837
  have hstable : (prefixWord ++ tailWord_4736837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736837).length < 2 ^ (prefixWord ++ tailWord_4736837).sum := by decide
  have hdescent : baseEnd_4736837 < baseStart_4736837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736864 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_4736864 : Nat := 118140960795 + 4736864 * 2 ^ 59
def prefixEnd_4736864 : Nat := 4983230072969 + 3 ^ 40 * 4736864 * 2
def baseEnd_4736864 : Nat := 2432288026979060231515565

theorem tailTrace_4736864 : CollatzResearch.WordTrace tailWord_4736864 prefixEnd_4736864 2432288026979060231515565 := by
  unfold tailWord_4736864
  simp only [CollatzResearch.WordTrace]
  refine ⟨86383811755579097404584823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115178415674105463206113097 86383811755579097404584823)
  ·
    refine ⟨129575717633368646106877235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86383811755579097404584823 129575717633368646106877235)
    ·
      refine ⟨194363576450052969160315853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129575717633368646106877235 194363576450052969160315853)
      ·
        refine ⟨72886341168769863435118445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194363576450052969160315853 72886341168769863435118445)
        ·
          refine ⟨27332377938288698788169417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72886341168769863435118445 27332377938288698788169417)
          ·
            refine ⟨20499283453716524091127063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27332377938288698788169417 20499283453716524091127063)
            ·
              refine ⟨30748925180574786136690595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20499283453716524091127063 30748925180574786136690595)
              ·
                refine ⟨46123387770862179205035893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30748925180574786136690595 46123387770862179205035893)
                ·
                  refine ⟨4324067603518329300472115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46123387770862179205035893 4324067603518329300472115)
                  ·
                    refine ⟨6486101405277493950708173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324067603518329300472115 6486101405277493950708173)
                    ·
                      refine ⟨2432288026979060231515565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486101405277493950708173 2432288026979060231515565)
                      ·
                        rfl

theorem cell23_4736864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_4736864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736864 prefixEnd_4736864 := by exact prefixLift 4736864
  have htrace : WordTrace (prefixWord ++ tailWord_4736864) baseStart_4736864 baseEnd_4736864 := by
    simpa [prefixWord, tailWord_4736864, baseEnd_4736864] using wordTrace_append hprefix tailTrace_4736864
  have hstable : (prefixWord ++ tailWord_4736864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736864).length < 2 ^ (prefixWord ++ tailWord_4736864).sum := by decide
  have hdescent : baseEnd_4736864 < baseStart_4736864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736868 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_4736868 : Nat := 118140960795 + 4736868 * 2 ^ 59
def prefixEnd_4736868 : Nat := 4983230072969 + 3 ^ 40 * 4736868 * 2
def baseEnd_4736868 : Nat := 2432290080901678215865547

theorem tailTrace_4736868 : CollatzResearch.WordTrace tailWord_4736868 prefixEnd_4736868 2432290080901678215865547 := by
  unfold tailWord_4736868
  simp only [CollatzResearch.WordTrace]
  refine ⟨86383884701571851746157629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115178512935429135661543505 86383884701571851746157629)
  ·
    refine ⟨32393956763089444404809111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86383884701571851746157629 32393956763089444404809111)
    ·
      refine ⟨48590935144634166607213667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32393956763089444404809111 48590935144634166607213667)
      ·
        refine ⟨72886402716951249910820501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48590935144634166607213667 72886402716951249910820501)
        ·
          refine ⟨3416550127357089839569711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72886402716951249910820501 3416550127357089839569711)
          ·
            refine ⟨5124825191035634759354567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416550127357089839569711 5124825191035634759354567)
            ·
              refine ⟨7687237786553452139031851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124825191035634759354567 7687237786553452139031851)
              ·
                refine ⟨11530856679830178208547777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687237786553452139031851 11530856679830178208547777)
                ·
                  refine ⟨8648142509872633656410833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11530856679830178208547777 8648142509872633656410833)
                  ·
                    refine ⟨6486106882404475242308125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8648142509872633656410833 6486106882404475242308125)
                    ·
                      refine ⟨2432290080901678215865547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486106882404475242308125 2432290080901678215865547)
                      ·
                        rfl

theorem cell23_4736868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_4736868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736868 prefixEnd_4736868 := by exact prefixLift 4736868
  have htrace : WordTrace (prefixWord ++ tailWord_4736868) baseStart_4736868 baseEnd_4736868 := by
    simpa [prefixWord, tailWord_4736868, baseEnd_4736868] using wordTrace_append hprefix tailTrace_4736868
  have hstable : (prefixWord ++ tailWord_4736868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736868).length < 2 ^ (prefixWord ++ tailWord_4736868).sum := by decide
  have hdescent : baseEnd_4736868 < baseStart_4736868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736917 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4736917 : Nat := 118140960795 + 4736917 * 2 ^ 59
def prefixEnd_4736917 : Nat := 4983230072969 + 3 ^ 40 * 4736917 * 2
def baseEnd_4736917 : Nat := 2432315241453748524152821

theorem tailTrace_4736917 : CollatzResearch.WordTrace tailWord_4736917 prefixEnd_4736917 2432315241453748524152821 := by
  unfold tailWord_4736917
  simp only [CollatzResearch.WordTrace]
  refine ⟨172769556579966184860849005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115179704386644123240566003 172769556579966184860849005)
  ·
    refine ⟨64788583717487319322818377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172769556579966184860849005 64788583717487319322818377)
    ·
      refine ⟨48591437788115489492113783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64788583717487319322818377 48591437788115489492113783)
      ·
        refine ⟨72887156682173234238170675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48591437788115489492113783 72887156682173234238170675)
        ·
          refine ⟨109330735023259851357256013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72887156682173234238170675 109330735023259851357256013)
          ·
            refine ⟨40999025633722444258971005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109330735023259851357256013 40999025633722444258971005)
            ·
              refine ⟨15374634612645916597114127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40999025633722444258971005 15374634612645916597114127)
              ·
                refine ⟨23061951918968874895671191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15374634612645916597114127 23061951918968874895671191)
                ·
                  refine ⟨34592927878453312343506787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23061951918968874895671191 34592927878453312343506787)
                  ·
                    refine ⟨51889391817679968515260181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34592927878453312343506787 51889391817679968515260181)
                    ·
                      refine ⟨2432315241453748524152821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51889391817679968515260181 2432315241453748524152821)
                      ·
                        rfl

theorem cell23_4736917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4736917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736917 prefixEnd_4736917 := by exact prefixLift 4736917
  have htrace : WordTrace (prefixWord ++ tailWord_4736917) baseStart_4736917 baseEnd_4736917 := by
    simpa [prefixWord, tailWord_4736917, baseEnd_4736917] using wordTrace_append hprefix tailTrace_4736917
  have hstable : (prefixWord ++ tailWord_4736917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736917).length < 2 ^ (prefixWord ++ tailWord_4736917).sum := by decide
  have hdescent : baseEnd_4736917 < baseStart_4736917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736921 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 3, 2, 2]
def baseStart_4736921 : Nat := 118140960795 + 4736921 * 2 ^ 59
def prefixEnd_4736921 : Nat := 4983230072969 + 3 ^ 40 * 4736921 * 2
def baseEnd_4736921 : Nat := 2432317295376366508502803

theorem tailTrace_4736921 : CollatzResearch.WordTrace tailWord_4736921 prefixEnd_4736921 2432317295376366508502803 := by
  unfold tailWord_4736921
  simp only [CollatzResearch.WordTrace]
  refine ⟨172769702471951693543994617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115179801647967795695996411 172769702471951693543994617)
  ·
    refine ⟨129577276853963770157995963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172769702471951693543994617 129577276853963770157995963)
    ·
      refine ⟨194365915280945655236993945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129577276853963770157995963 194365915280945655236993945)
      ·
        refine ⟨145774436460709241427745459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194365915280945655236993945 145774436460709241427745459)
        ·
          refine ⟨218661654691063862141618189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145774436460709241427745459 218661654691063862141618189)
          ·
            refine ⟨81998120509148948303106821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218661654691063862141618189 81998120509148948303106821)
            ·
              refine ⟨15374647595465427806832529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81998120509148948303106821 15374647595465427806832529)
              ·
                refine ⟨11530985696599070855124397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15374647595465427806832529 11530985696599070855124397)
                ·
                  refine ⟨4324119636224651570671649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11530985696599070855124397 4324119636224651570671649)
                  ·
                    refine ⟨3243089727168488678003737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324119636224651570671649 3243089727168488678003737)
                    ·
                      refine ⟨2432317295376366508502803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243089727168488678003737 2432317295376366508502803)
                      ·
                        rfl

theorem cell23_4736921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_4736921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736921 prefixEnd_4736921 := by exact prefixLift 4736921
  have htrace : WordTrace (prefixWord ++ tailWord_4736921) baseStart_4736921 baseEnd_4736921 := by
    simpa [prefixWord, tailWord_4736921, baseEnd_4736921] using wordTrace_append hprefix tailTrace_4736921
  have hstable : (prefixWord ++ tailWord_4736921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736921).length < 2 ^ (prefixWord ++ tailWord_4736921).sum := by decide
  have hdescent : baseEnd_4736921 < baseStart_4736921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736942 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4736942 : Nat := 118140960795 + 4736942 * 2 ^ 59
def prefixEnd_4736942 : Nat := 4983230072969 + 3 ^ 40 * 4736942 * 2
def baseEnd_4736942 : Nat := 2432328078470110926340207

theorem tailTrace_4736942 : CollatzResearch.WordTrace tailWord_4736942 prefixEnd_4736942 2432328078470110926340207 := by
  unfold tailWord_4736942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21596308550609451766313635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115180312269917076087006053 21596308550609451766313635)
  ·
    refine ⟨32394462825914177649470453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21596308550609451766313635 32394462825914177649470453)
    ·
      refine ⟨3036980889929454154637855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32394462825914177649470453 3036980889929454154637855)
      ·
        refine ⟨4555471334894181231956783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036980889929454154637855 4555471334894181231956783)
        ·
          refine ⟨6833207002341271847935175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555471334894181231956783 6833207002341271847935175)
          ·
            refine ⟨10249810503511907771902763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833207002341271847935175 10249810503511907771902763)
            ·
              refine ⟨15374715755267861657854145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249810503511907771902763 15374715755267861657854145)
              ·
                refine ⟨11531036816450896243390609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15374715755267861657854145 11531036816450896243390609)
                ·
                  refine ⟨8648277612338172182542957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11531036816450896243390609 8648277612338172182542957)
                  ·
                    refine ⟨3243104104626814568453609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8648277612338172182542957 3243104104626814568453609)
                    ·
                      refine ⟨2432328078470110926340207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243104104626814568453609 2432328078470110926340207)
                      ·
                        rfl

theorem cell23_4736942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4736942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736942 prefixEnd_4736942 := by exact prefixLift 4736942
  have htrace : WordTrace (prefixWord ++ tailWord_4736942) baseStart_4736942 baseEnd_4736942 := by
    simpa [prefixWord, tailWord_4736942, baseEnd_4736942] using wordTrace_append hprefix tailTrace_4736942
  have hstable : (prefixWord ++ tailWord_4736942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736942).length < 2 ^ (prefixWord ++ tailWord_4736942).sum := by decide
  have hdescent : baseEnd_4736942 < baseStart_4736942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736971 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 3]
def baseStart_4736971 : Nat := 118140960795 + 4736971 * 2 ^ 59
def prefixEnd_4736971 : Nat := 4983230072969 + 3 ^ 40 * 4736971 * 2
def baseEnd_4736971 : Nat := 2432342969409091312877573

theorem tailTrace_4736971 : CollatzResearch.WordTrace tailWord_4736971 prefixEnd_4736971 2432342969409091312877573 := by
  unfold tailWord_4736971
  simp only [CollatzResearch.WordTrace]
  refine ⟨172771526121770552083314767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115181017414513701388876511 172771526121770552083314767)
  ·
    refine ⟨259157289182655828124972151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172771526121770552083314767 259157289182655828124972151)
    ·
      refine ⟨388735933773983742187458227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259157289182655828124972151 388735933773983742187458227)
      ·
        refine ⟨583103900660975613281187341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388735933773983742187458227 583103900660975613281187341)
        ·
          refine ⟨218663962747865854980445253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 583103900660975613281187341 218663962747865854980445253)
          ·
            refine ⟨40999493015224847808833485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218663962747865854980445253 40999493015224847808833485)
            ·
              refine ⟨15374809880709317928312557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40999493015224847808833485 15374809880709317928312557)
              ·
                refine ⟨5765553705265994223117209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15374809880709317928312557 5765553705265994223117209)
                ·
                  refine ⟨4324165278949495667337907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5765553705265994223117209 4324165278949495667337907)
                  ·
                    refine ⟨6486247918424243501006861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324165278949495667337907 6486247918424243501006861)
                    ·
                      refine ⟨2432342969409091312877573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486247918424243501006861 2432342969409091312877573)
                      ·
                        rfl

theorem cell23_4736971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 3].length) (baseStart_4736971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736971 prefixEnd_4736971 := by exact prefixLift 4736971
  have htrace : WordTrace (prefixWord ++ tailWord_4736971) baseStart_4736971 baseEnd_4736971 := by
    simpa [prefixWord, tailWord_4736971, baseEnd_4736971] using wordTrace_append hprefix tailTrace_4736971
  have hstable : (prefixWord ++ tailWord_4736971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736971).length < 2 ^ (prefixWord ++ tailWord_4736971).sum := by decide
  have hdescent : baseEnd_4736971 < baseStart_4736971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4736977 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_4736977 : Nat := 118140960795 + 4736977 * 2 ^ 59
def prefixEnd_4736977 : Nat := 4983230072969 + 3 ^ 40 * 4736977 * 2
def baseEnd_4736977 : Nat := 2432346050293018289402545

theorem tailTrace_4736977 : CollatzResearch.WordTrace tailWord_4736977 prefixEnd_4736977 2432346050293018289402545 := by
  unfold tailWord_4736977
  simp only [CollatzResearch.WordTrace]
  refine ⟨172771744959748815108033185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115181163306499210072022123 172771744959748815108033185)
  ·
    refine ⟨129578808719811611331024889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172771744959748815108033185 129578808719811611331024889)
    ·
      refine ⟨97184106539858708498268667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129578808719811611331024889 97184106539858708498268667)
      ·
        refine ⟨145776159809788062747403001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97184106539858708498268667 145776159809788062747403001)
        ·
          refine ⟨109332119857341047060552251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145776159809788062747403001 109332119857341047060552251)
          ·
            refine ⟨163998179786011570590828377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109332119857341047060552251 163998179786011570590828377)
            ·
              refine ⟨122998634839508677943121283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163998179786011570590828377 122998634839508677943121283)
              ·
                refine ⟨184497952259263016914681925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122998634839508677943121283 184497952259263016914681925)
                ·
                  refine ⟨34593366048611815671502861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184497952259263016914681925 34593366048611815671502861)
                  ·
                    refine ⟨12972512268229430876813573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34593366048611815671502861 12972512268229430876813573)
                    ·
                      refine ⟨2432346050293018289402545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12972512268229430876813573 2432346050293018289402545)
                      ·
                        rfl

theorem cell23_4736977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_4736977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4736977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4736977 prefixEnd_4736977 := by exact prefixLift 4736977
  have htrace : WordTrace (prefixWord ++ tailWord_4736977) baseStart_4736977 baseEnd_4736977 := by
    simpa [prefixWord, tailWord_4736977, baseEnd_4736977] using wordTrace_append hprefix tailTrace_4736977
  have hstable : (prefixWord ++ tailWord_4736977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4736977).length < 2 ^ (prefixWord ++ tailWord_4736977).sum := by decide
  have hdescent : baseEnd_4736977 < baseStart_4736977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4736977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737011 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 4, 2, 2]
def baseStart_4737011 : Nat := 118140960795 + 4737011 * 2 ^ 59
def prefixEnd_4737011 : Nat := 4983230072969 + 3 ^ 40 * 4737011 * 2
def baseEnd_4737011 : Nat := 2432363508635271156377389

theorem tailTrace_4737011 : CollatzResearch.WordTrace tailWord_4737011 prefixEnd_4737011 2432363508635271156377389 := by
  unfold tailWord_4737011
  simp only [CollatzResearch.WordTrace]
  refine ⟨172772985041625638914770887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115181990027750425943180591 172772985041625638914770887)
  ·
    refine ⟨259159477562438458372156331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172772985041625638914770887 259159477562438458372156331)
    ·
      refine ⟨388739216343657687558234497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259159477562438458372156331 388739216343657687558234497)
      ·
        refine ⟨291554412257743265668675873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388739216343657687558234497 291554412257743265668675873)
        ·
          refine ⟨218665809193307449251506905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291554412257743265668675873 218665809193307449251506905)
          ·
            refine ⟨163999356894980586938630179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218665809193307449251506905 163999356894980586938630179)
            ·
              refine ⟨245999035342470880407945269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163999356894980586938630179 245999035342470880407945269)
              ·
                refine ⟨23062409563356645038244869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 245999035342470880407945269 23062409563356645038244869)
                ·
                  refine ⟨4324201793129370944670913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23062409563356645038244869 4324201793129370944670913)
                  ·
                    refine ⟨3243151344847028208503185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324201793129370944670913 3243151344847028208503185)
                    ·
                      refine ⟨2432363508635271156377389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243151344847028208503185 2432363508635271156377389)
                      ·
                        rfl

theorem cell23_4737011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2, 2].length) (baseStart_4737011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737011 prefixEnd_4737011 := by exact prefixLift 4737011
  have htrace : WordTrace (prefixWord ++ tailWord_4737011) baseStart_4737011 baseEnd_4737011 := by
    simpa [prefixWord, tailWord_4737011, baseEnd_4737011] using wordTrace_append hprefix tailTrace_4737011
  have hstable : (prefixWord ++ tailWord_4737011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737011).length < 2 ^ (prefixWord ++ tailWord_4737011).sum := by decide
  have hdescent : baseEnd_4737011 < baseStart_4737011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737084 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4737084 : Nat := 118140960795 + 4737084 * 2 ^ 59
def prefixEnd_4737084 : Nat := 4983230072969 + 3 ^ 40 * 4737084 * 2
def baseEnd_4737084 : Nat := 2432400992723049370764553

theorem tailTrace_4737084 : CollatzResearch.WordTrace tailWord_4737084 prefixEnd_4737084 2432400992723049370764553 := by
  unfold tailWord_4737084
  simp only [CollatzResearch.WordTrace]
  refine ⟨86387823785180586191089153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115183765046907448254785537 86387823785180586191089153)
  ·
    refine ⟨64790867838885439643316865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86387823785180586191089153 64790867838885439643316865)
    ·
      refine ⟨48593150879164079732487649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64790867838885439643316865 48593150879164079732487649)
      ·
        refine ⟨36444863159373059799365737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48593150879164079732487649 36444863159373059799365737)
        ·
          refine ⟨27333647369529794849524303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36444863159373059799365737 27333647369529794849524303)
          ·
            refine ⟨41000471054294692274286455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27333647369529794849524303 41000471054294692274286455)
            ·
              refine ⟨61500706581442038411429683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41000471054294692274286455 61500706581442038411429683)
              ·
                refine ⟨92251059872163057617144525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61500706581442038411429683 92251059872163057617144525)
                ·
                  refine ⟨34594147452061146606429197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92251059872163057617144525 34594147452061146606429197)
                  ·
                    refine ⟨12972805294522929977410949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34594147452061146606429197 12972805294522929977410949)
                    ·
                      refine ⟨2432400992723049370764553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12972805294522929977410949 2432400992723049370764553)
                      ·
                        rfl

theorem cell23_4737084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4737084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737084 prefixEnd_4737084 := by exact prefixLift 4737084
  have htrace : WordTrace (prefixWord ++ tailWord_4737084) baseStart_4737084 baseEnd_4737084 := by
    simpa [prefixWord, tailWord_4737084, baseEnd_4737084] using wordTrace_append hprefix tailTrace_4737084
  have hstable : (prefixWord ++ tailWord_4737084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737084).length < 2 ^ (prefixWord ++ tailWord_4737084).sum := by decide
  have hdescent : baseEnd_4737084 < baseStart_4737084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737101 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_4737101 : Nat := 118140960795 + 4737101 * 2 ^ 59
def prefixEnd_4737101 : Nat := 4983230072969 + 3 ^ 40 * 4737101 * 2
def baseEnd_4737101 : Nat := 2432409721894175804251975

theorem tailTrace_4737101 : CollatzResearch.WordTrace tailWord_4737101 prefixEnd_4737101 2432409721894175804251975 := by
  unfold tailWord_4737101
  simp only [CollatzResearch.WordTrace]
  refine ⟨172776267611299584285547157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115184178407533056190364771 172776267611299584285547157)
  ·
    refine ⟨8098887544279668013385023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172776267611299584285547157 8098887544279668013385023)
    ·
      refine ⟨12148331316419502020077535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8098887544279668013385023 12148331316419502020077535)
      ·
        refine ⟨18222496974629253030116303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12148331316419502020077535 18222496974629253030116303)
        ·
          refine ⟨27333745461943879545174455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18222496974629253030116303 27333745461943879545174455)
          ·
            refine ⟨41000618192915819317761683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27333745461943879545174455 41000618192915819317761683)
            ·
              refine ⟨61500927289373728976642525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41000618192915819317761683 61500927289373728976642525)
              ·
                refine ⟨23062847733515148366240947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61500927289373728976642525 23062847733515148366240947)
                ·
                  refine ⟨34594271600272722549361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23062847733515148366240947 34594271600272722549361421)
                  ·
                    refine ⟨12972851850102270956010533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34594271600272722549361421 12972851850102270956010533)
                    ·
                      refine ⟨2432409721894175804251975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12972851850102270956010533 2432409721894175804251975)
                      ·
                        rfl

theorem cell23_4737101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_4737101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737101 prefixEnd_4737101 := by exact prefixLift 4737101
  have htrace : WordTrace (prefixWord ++ tailWord_4737101) baseStart_4737101 baseEnd_4737101 := by
    simpa [prefixWord, tailWord_4737101, baseEnd_4737101] using wordTrace_append hprefix tailTrace_4737101
  have hstable : (prefixWord ++ tailWord_4737101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737101).length < 2 ^ (prefixWord ++ tailWord_4737101).sum := by decide
  have hdescent : baseEnd_4737101 < baseStart_4737101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737124 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 8]
def baseStart_4737124 : Nat := 118140960795 + 4737124 * 2 ^ 59
def prefixEnd_4737124 : Nat := 4983230072969 + 3 ^ 40 * 4737124 * 2
def baseEnd_4737124 : Nat := 270269059105469912696041

theorem tailTrace_4737124 : CollatzResearch.WordTrace tailWord_4737124 prefixEnd_4737124 270269059105469912696041 := by
  unfold tailWord_4737124
  simp only [CollatzResearch.WordTrace]
  refine ⟨86388553245108129606817213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115184737660144172809089617 86388553245108129606817213)
  ·
    refine ⟨32395707466915548602556455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86388553245108129606817213 32395707466915548602556455)
    ·
      refine ⟨48593561200373322903834683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32395707466915548602556455 48593561200373322903834683)
      ·
        refine ⟨72890341800559984355752025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48593561200373322903834683 72890341800559984355752025)
        ·
          refine ⟨54667756350419988266814019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72890341800559984355752025 54667756350419988266814019)
          ·
            refine ⟨82001634525629982400221029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54667756350419988266814019 82001634525629982400221029)
            ·
              refine ⟨15375306473555621700041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82001634525629982400221029 15375306473555621700041443)
              ·
                refine ⟨23062959710333432550062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15375306473555621700041443 23062959710333432550062165)
                ·
                  refine ⟨270269059105469912696041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23062959710333432550062165 270269059105469912696041)
                  ·
                    rfl

theorem cell23_4737124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_4737124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737124 prefixEnd_4737124 := by exact prefixLift 4737124
  have htrace : WordTrace (prefixWord ++ tailWord_4737124) baseStart_4737124 baseEnd_4737124 := by
    simpa [prefixWord, tailWord_4737124, baseEnd_4737124] using wordTrace_append hprefix tailTrace_4737124
  have hstable : (prefixWord ++ tailWord_4737124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737124).length < 2 ^ (prefixWord ++ tailWord_4737124).sum := by decide
  have hdescent : baseEnd_4737124 < baseStart_4737124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737211 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3]
def baseStart_4737211 : Nat := 118140960795 + 4737211 * 2 ^ 59
def prefixEnd_4737211 : Nat := 4983230072969 + 3 ^ 40 * 4737211 * 2
def baseEnd_4737211 : Nat := 2432466204766170373876469

theorem tailTrace_4737211 : CollatzResearch.WordTrace tailWord_4737211 prefixEnd_4737211 2432466204766170373876469 := by
  unfold tailWord_4737211
  simp only [CollatzResearch.WordTrace]
  refine ⟨172780279640901073072051487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115186853093934048714700991 172780279640901073072051487)
  ·
    refine ⟨259170419461351609608077231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172780279640901073072051487 259170419461351609608077231)
    ·
      refine ⟨388755629192027414412115847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259170419461351609608077231 388755629192027414412115847)
      ·
        refine ⟨583133443788041121618173771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388755629192027414412115847 583133443788041121618173771)
        ·
          refine ⟨874700165682061682427260657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583133443788041121618173771 874700165682061682427260657)
          ·
            refine ⟨656025124261546261820445493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874700165682061682427260657 656025124261546261820445493)
            ·
              refine ⟨61502355399519962045666765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 656025124261546261820445493 61502355399519962045666765)
              ·
                refine ⟨23063383274819985767125037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61502355399519962045666765 23063383274819985767125037)
                ·
                  refine ⟨8648768728057494662671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23063383274819985767125037 8648768728057494662671889)
                  ·
                    refine ⟨6486576546043120997003917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8648768728057494662671889 6486576546043120997003917)
                    ·
                      refine ⟨2432466204766170373876469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486576546043120997003917 2432466204766170373876469)
                      ·
                        rfl

theorem cell23_4737211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].length) (baseStart_4737211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737211 prefixEnd_4737211 := by exact prefixLift 4737211
  have htrace : WordTrace (prefixWord ++ tailWord_4737211) baseStart_4737211 baseEnd_4737211 := by
    simpa [prefixWord, tailWord_4737211, baseEnd_4737211] using wordTrace_append hprefix tailTrace_4737211
  have hstable : (prefixWord ++ tailWord_4737211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737211).length < 2 ^ (prefixWord ++ tailWord_4737211).sum := by decide
  have hdescent : baseEnd_4737211 < baseStart_4737211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737212 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4737212 : Nat := 118140960795 + 4737212 * 2 ^ 59
def prefixEnd_4737212 : Nat := 4983230072969 + 3 ^ 40 * 4737212 * 2
def baseEnd_4737212 : Nat := 2432466718246824869963965

theorem tailTrace_4737212 : CollatzResearch.WordTrace tailWord_4737212 prefixEnd_4737212 2432466718246824869963965 := by
  unfold tailWord_4737212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86390158056948725121418945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115186877409264966828558593 86390158056948725121418945)
  ·
    refine ⟨64792618542711543841064209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86390158056948725121418945 64792618542711543841064209)
    ·
      refine ⟨48594463907033657880798157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64792618542711543841064209 48594463907033657880798157)
      ·
        refine ⟨18222923965137621705299309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48594463907033657880798157 18222923965137621705299309)
        ·
          refine ⟨6833596486926608139487241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18222923965137621705299309 6833596486926608139487241)
          ·
            refine ⟨5125197365194956104615431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6833596486926608139487241 5125197365194956104615431)
            ·
              refine ⟨7687796047792434156923147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125197365194956104615431 7687796047792434156923147)
              ·
                refine ⟨11531694071688651235384721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687796047792434156923147 11531694071688651235384721)
                ·
                  refine ⟨8648770553766488426538541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11531694071688651235384721 8648770553766488426538541)
                  ·
                    refine ⟨3243288957662433159951953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8648770553766488426538541 3243288957662433159951953)
                    ·
                      refine ⟨2432466718246824869963965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243288957662433159951953 2432466718246824869963965)
                      ·
                        rfl

theorem cell23_4737212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4737212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737212 prefixEnd_4737212 := by exact prefixLift 4737212
  have htrace : WordTrace (prefixWord ++ tailWord_4737212) baseStart_4737212 baseEnd_4737212 := by
    simpa [prefixWord, tailWord_4737212, baseEnd_4737212] using wordTrace_append hprefix tailTrace_4737212
  have hstable : (prefixWord ++ tailWord_4737212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737212).length < 2 ^ (prefixWord ++ tailWord_4737212).sum := by decide
  have hdescent : baseEnd_4737212 < baseStart_4737212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737221 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_4737221 : Nat := 118140960795 + 4737221 * 2 ^ 59
def prefixEnd_4737221 : Nat := 4983230072969 + 3 ^ 40 * 4737221 * 2
def baseEnd_4737221 : Nat := 2432471339572715334751423

theorem tailTrace_4737221 : CollatzResearch.WordTrace tailWord_4737221 prefixEnd_4737221 2432471339572715334751423 := by
  unfold tailWord_4737221
  simp only [CollatzResearch.WordTrace]
  refine ⟨172780644370864844779915517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115187096247243229853277011 172780644370864844779915517)
  ·
    refine ⟨64792741639074316792468319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172780644370864844779915517 64792741639074316792468319)
    ·
      refine ⟨97189112458611475188702479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64792741639074316792468319 97189112458611475188702479)
      ·
        refine ⟨145783668687917212783053719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97189112458611475188702479 145783668687917212783053719)
        ·
          refine ⟨218675503031875819174580579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145783668687917212783053719 218675503031875819174580579)
          ·
            refine ⟨328013254547813728761870869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218675503031875819174580579 328013254547813728761870869)
            ·
              refine ⟨15375621306928768535712697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 328013254547813728761870869 15375621306928768535712697)
              ·
                refine ⟨11531715980196576401784523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15375621306928768535712697 11531715980196576401784523)
                ·
                  refine ⟨17297573970294864602676785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11531715980196576401784523 17297573970294864602676785)
                  ·
                    refine ⟨12973180477721148452007589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17297573970294864602676785 12973180477721148452007589)
                    ·
                      refine ⟨2432471339572715334751423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12973180477721148452007589 2432471339572715334751423)
                      ·
                        rfl

theorem cell23_4737221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_4737221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737221 prefixEnd_4737221 := by exact prefixLift 4737221
  have htrace : WordTrace (prefixWord ++ tailWord_4737221) baseStart_4737221 baseEnd_4737221 := by
    simpa [prefixWord, tailWord_4737221, baseEnd_4737221] using wordTrace_append hprefix tailTrace_4737221
  have hstable : (prefixWord ++ tailWord_4737221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737221).length < 2 ^ (prefixWord ++ tailWord_4737221).sum := by decide
  have hdescent : baseEnd_4737221 < baseStart_4737221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737241 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_4737241 : Nat := 118140960795 + 4737241 * 2 ^ 59
def prefixEnd_4737241 : Nat := 4983230072969 + 3 ^ 40 * 4737241 * 2
def baseEnd_4737241 : Nat := 2432481609185805256501331

theorem tailTrace_4737241 : CollatzResearch.WordTrace tailWord_4737241 prefixEnd_4737241 2432481609185805256501331 := by
  unfold tailWord_4737241
  simp only [CollatzResearch.WordTrace]
  refine ⟨172781373830792388195643577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115187582553861592130429051 172781373830792388195643577)
  ·
    refine ⟨129586030373094291146732683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172781373830792388195643577 129586030373094291146732683)
    ·
      refine ⟨194379045559641436720099025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129586030373094291146732683 194379045559641436720099025)
      ·
        refine ⟨145784284169731077540074269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194379045559641436720099025 145784284169731077540074269)
        ·
          refine ⟨54669106563649154077527851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145784284169731077540074269 54669106563649154077527851)
          ·
            refine ⟨82003659845473731116291777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54669106563649154077527851 82003659845473731116291777)
            ·
              refine ⟨61502744884105298337218833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82003659845473731116291777 61502744884105298337218833)
              ·
                refine ⟨46127058663078973752914125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61502744884105298337218833 46127058663078973752914125)
                ·
                  refine ⟨17297646998654615157342797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46127058663078973752914125 17297646998654615157342797)
                  ·
                    refine ⟨6486617624495480684003549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17297646998654615157342797 6486617624495480684003549)
                    ·
                      refine ⟨2432481609185805256501331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486617624495480684003549 2432481609185805256501331)
                      ·
                        rfl

theorem cell23_4737241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_4737241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737241 prefixEnd_4737241 := by exact prefixLift 4737241
  have htrace : WordTrace (prefixWord ++ tailWord_4737241) baseStart_4737241 baseEnd_4737241 := by
    simpa [prefixWord, tailWord_4737241, baseEnd_4737241] using wordTrace_append hprefix tailTrace_4737241
  have hstable : (prefixWord ++ tailWord_4737241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737241).length < 2 ^ (prefixWord ++ tailWord_4737241).sum := by decide
  have hdescent : baseEnd_4737241 < baseStart_4737241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737242 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_4737242 : Nat := 118140960795 + 4737242 * 2 ^ 59
def prefixEnd_4737242 : Nat := 4983230072969 + 3 ^ 40 * 4737242 * 2
def baseEnd_4737242 : Nat := 2432482122666459752588827

theorem tailTrace_4737242 : CollatzResearch.WordTrace tailWord_4737242 prefixEnd_4737242 2432482122666459752588827 := by
  unfold tailWord_4737242
  simp only [CollatzResearch.WordTrace]
  refine ⟨43195352575947191341607495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115187606869192510244286653 43195352575947191341607495)
  ·
    refine ⟨64793028863920787012411243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43195352575947191341607495 64793028863920787012411243)
    ·
      refine ⟨97189543295881180518616865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64793028863920787012411243 97189543295881180518616865)
      ·
        refine ⟨72892157471910885388962649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97189543295881180518616865 72892157471910885388962649)
        ·
          refine ⟨54669118103933164041721987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72892157471910885388962649 54669118103933164041721987)
          ·
            refine ⟨82003677155899746062582981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54669118103933164041721987 82003677155899746062582981)
            ·
              refine ⟨15375689466731202386734309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82003677155899746062582981 15375689466731202386734309)
              ·
                refine ⟨2882941775012100447512683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15375689466731202386734309 2882941775012100447512683)
                ·
                  refine ⟨4324412662518150671269025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882941775012100447512683 4324412662518150671269025)
                  ·
                    refine ⟨3243309496888613003451769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324412662518150671269025 3243309496888613003451769)
                    ·
                      refine ⟨2432482122666459752588827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243309496888613003451769 2432482122666459752588827)
                      ·
                        rfl

theorem cell23_4737242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_4737242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737242 prefixEnd_4737242 := by exact prefixLift 4737242
  have htrace : WordTrace (prefixWord ++ tailWord_4737242) baseStart_4737242 baseEnd_4737242 := by
    simpa [prefixWord, tailWord_4737242, baseEnd_4737242] using wordTrace_append hprefix tailTrace_4737242
  have hstable : (prefixWord ++ tailWord_4737242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737242).length < 2 ^ (prefixWord ++ tailWord_4737242).sum := by decide
  have hdescent : baseEnd_4737242 < baseStart_4737242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737255 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4737255 : Nat := 118140960795 + 4737255 * 2 ^ 59
def prefixEnd_4737255 : Nat := 4983230072969 + 3 ^ 40 * 4737255 * 2
def baseEnd_4737255 : Nat := 2432488797914968201726267

theorem tailTrace_4737255 : CollatzResearch.WordTrace tailWord_4737255 prefixEnd_4737255 2432488797914968201726267 := by
  unfold tailWord_4737255
  simp only [CollatzResearch.WordTrace]
  refine ⟨172781884452741668586653219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115187922968494445724435479 172781884452741668586653219)
  ·
    refine ⟨259172826679112502879979829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172781884452741668586653219 259172826679112502879979829)
    ·
      refine ⟨24297452501166797144998109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259172826679112502879979829 24297452501166797144998109)
      ·
        refine ⟨9111544687937548929374291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24297452501166797144998109 9111544687937548929374291)
        ·
          refine ⟨13667317031906323394061437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9111544687937548929374291 13667317031906323394061437)
          ·
            refine ⟨5125243886964871272773039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13667317031906323394061437 5125243886964871272773039)
            ·
              refine ⟨7687865830447306909159559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125243886964871272773039 7687865830447306909159559)
              ·
                refine ⟨11531798745670960363739339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687865830447306909159559 11531798745670960363739339)
                ·
                  refine ⟨17297698118506440545609009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11531798745670960363739339 17297698118506440545609009)
                  ·
                    refine ⟨12973273588879830409206757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17297698118506440545609009 12973273588879830409206757)
                    ·
                      refine ⟨2432488797914968201726267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12973273588879830409206757 2432488797914968201726267)
                      ·
                        rfl

theorem cell23_4737255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4737255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737255 prefixEnd_4737255 := by exact prefixLift 4737255
  have htrace : WordTrace (prefixWord ++ tailWord_4737255) baseStart_4737255 baseEnd_4737255 := by
    simpa [prefixWord, tailWord_4737255, baseEnd_4737255] using wordTrace_append hprefix tailTrace_4737255
  have hstable : (prefixWord ++ tailWord_4737255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737255).length < 2 ^ (prefixWord ++ tailWord_4737255).sum := by decide
  have hdescent : baseEnd_4737255 < baseStart_4737255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737332 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_4737332 : Nat := 118140960795 + 4737332 * 2 ^ 59
def prefixEnd_4737332 : Nat := 4983230072969 + 3 ^ 40 * 4737332 * 2
def baseEnd_4737332 : Nat := 2432528335925364400463413

theorem tailTrace_4737332 : CollatzResearch.WordTrace tailWord_4737332 prefixEnd_4737332 2432528335925364400463413 := by
  unfold tailWord_4737332
  simp only [CollatzResearch.WordTrace]
  refine ⟨86392346436731355368603125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115189795248975140491470833 86392346436731355368603125)
  ·
    refine ⟨8099282478443564565806543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86392346436731355368603125 8099282478443564565806543)
    ·
      refine ⟨12148923717665346848709815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099282478443564565806543 12148923717665346848709815)
      ·
        refine ⟨18223385576498020273064723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12148923717665346848709815 18223385576498020273064723)
        ·
          refine ⟨27335078364747030409597085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18223385576498020273064723 27335078364747030409597085)
          ·
            refine ⟨10250654386780136403598907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27335078364747030409597085 10250654386780136403598907)
            ·
              refine ⟨15375981580170204605398361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10250654386780136403598907 15375981580170204605398361)
              ·
                refine ⟨11531986185127653454048771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15375981580170204605398361 11531986185127653454048771)
                ·
                  refine ⟨17297979277691480181073157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11531986185127653454048771 17297979277691480181073157)
                  ·
                    refine ⟨3243371114567152533951217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17297979277691480181073157 3243371114567152533951217)
                    ·
                      refine ⟨2432528335925364400463413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243371114567152533951217 2432528335925364400463413)
                      ·
                        rfl

theorem cell23_4737332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_4737332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737332 prefixEnd_4737332 := by exact prefixLift 4737332
  have htrace : WordTrace (prefixWord ++ tailWord_4737332) baseStart_4737332 baseEnd_4737332 := by
    simpa [prefixWord, tailWord_4737332, baseEnd_4737332] using wordTrace_append hprefix tailTrace_4737332
  have hstable : (prefixWord ++ tailWord_4737332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737332).length < 2 ^ (prefixWord ++ tailWord_4737332).sum := by decide
  have hdescent : baseEnd_4737332 < baseStart_4737332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737365 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4737365 : Nat := 118140960795 + 4737365 * 2 ^ 59
def prefixEnd_4737365 : Nat := 4983230072969 + 3 ^ 40 * 4737365 * 2
def baseEnd_4737365 : Nat := 2432545280786962771350761

theorem tailTrace_4737365 : CollatzResearch.WordTrace tailWord_4737365 prefixEnd_4737365 2432545280786962771350761 := by
  unfold tailWord_4737365
  simp only [CollatzResearch.WordTrace]
  refine ⟨172785896482343157373157549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115190597654895438248771699 172785896482343157373157549)
  ·
    refine ⟨64794711180878684014934081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172785896482343157373157549 64794711180878684014934081)
    ·
      refine ⟨48596033385659013011200561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64794711180878684014934081 48596033385659013011200561)
      ·
        refine ⟨36447025039244259758400421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48596033385659013011200561 36447025039244259758400421)
        ·
          refine ⟨6833817194858298704700079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36447025039244259758400421 6833817194858298704700079)
          ·
            refine ⟨10250725792287448057050119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833817194858298704700079 10250725792287448057050119)
            ·
              refine ⟨15376088688431172085575179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10250725792287448057050119 15376088688431172085575179)
              ·
                refine ⟨23064133032646758128362769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15376088688431172085575179 23064133032646758128362769)
                ·
                  refine ⟨17298099774485068596272077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23064133032646758128362769 17298099774485068596272077)
                  ·
                    refine ⟨6486787415431900723602029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17298099774485068596272077 6486787415431900723602029)
                    ·
                      refine ⟨2432545280786962771350761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6486787415431900723602029 2432545280786962771350761)
                      ·
                        rfl

theorem cell23_4737365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4737365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737365 prefixEnd_4737365 := by exact prefixLift 4737365
  have htrace : WordTrace (prefixWord ++ tailWord_4737365) baseStart_4737365 baseEnd_4737365 := by
    simpa [prefixWord, tailWord_4737365, baseEnd_4737365] using wordTrace_append hprefix tailTrace_4737365
  have hstable : (prefixWord ++ tailWord_4737365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737365).length < 2 ^ (prefixWord ++ tailWord_4737365).sum := by decide
  have hdescent : baseEnd_4737365 < baseStart_4737365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737391 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_4737391 : Nat := 118140960795 + 4737391 * 2 ^ 59
def prefixEnd_4737391 : Nat := 4983230072969 + 3 ^ 40 * 4737391 * 2
def baseEnd_4737391 : Nat := 2432558631283979669625641

theorem tailTrace_4737391 : CollatzResearch.WordTrace tailWord_4737391 prefixEnd_4737391 2432558631283979669625641 := by
  unfold tailWord_4737391
  simp only [CollatzResearch.WordTrace]
  refine ⟨172786844780248963813604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115191229853499309209069351 172786844780248963813604027)
  ·
    refine ⟨259180267170373445720406041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172786844780248963813604027 259180267170373445720406041)
    ·
      refine ⟨194385200377780084290304531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259180267170373445720406041 194385200377780084290304531)
      ·
        refine ⟨291577800566670126435456797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194385200377780084290304531 291577800566670126435456797)
        ·
          refine ⟨109341675212501297413296299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291577800566670126435456797 109341675212501297413296299)
          ·
            refine ⟨164012512818751946119944449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109341675212501297413296299 164012512818751946119944449)
            ·
              refine ⟨123009384614063959589958337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164012512818751946119944449 123009384614063959589958337)
              ·
                refine ⟨92257038460547969692468753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123009384614063959589958337 92257038460547969692468753)
                ·
                  refine ⟨69192778845410977269351565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92257038460547969692468753 69192778845410977269351565)
                  ·
                    refine ⟨25947292067029116476006837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69192778845410977269351565 25947292067029116476006837)
                    ·
                      refine ⟨2432558631283979669625641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25947292067029116476006837 2432558631283979669625641)
                      ·
                        rfl

theorem cell23_4737391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_4737391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737391 prefixEnd_4737391 := by exact prefixLift 4737391
  have htrace : WordTrace (prefixWord ++ tailWord_4737391) baseStart_4737391 baseEnd_4737391 := by
    simpa [prefixWord, tailWord_4737391, baseEnd_4737391] using wordTrace_append hprefix tailTrace_4737391
  have hstable : (prefixWord ++ tailWord_4737391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737391).length < 2 ^ (prefixWord ++ tailWord_4737391).sum := by decide
  have hdescent : baseEnd_4737391 < baseStart_4737391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737405 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_4737405 : Nat := 118140960795 + 4737405 * 2 ^ 59
def prefixEnd_4737405 : Nat := 4983230072969 + 3 ^ 40 * 4737405 * 2
def baseEnd_4737405 : Nat := 2432565820013142614850577

theorem tailTrace_4737405 : CollatzResearch.WordTrace tailWord_4737405 prefixEnd_4737405 2432565820013142614850577 := by
  unfold tailWord_4737405
  simp only [CollatzResearch.WordTrace]
  refine ⟨172787355402198244204613669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115191570268132162803075779 172787355402198244204613669)
  ·
    refine ⟨32397629137912170788365063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172787355402198244204613669 32397629137912170788365063)
    ·
      refine ⟨48596443706868256182547595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32397629137912170788365063 48596443706868256182547595)
      ·
        refine ⟨72894665560302384273821393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48596443706868256182547595 72894665560302384273821393)
        ·
          refine ⟨54670999170226788205366045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72894665560302384273821393 54670999170226788205366045)
          ·
            refine ⟨20501624688835045577012267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54670999170226788205366045 20501624688835045577012267)
            ·
              refine ⟨30752437033252568365518401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20501624688835045577012267 30752437033252568365518401)
              ·
                refine ⟨23064327774939426274138801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30752437033252568365518401 23064327774939426274138801)
                ·
                  refine ⟨17298245831204569705604101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23064327774939426274138801 17298245831204569705604101)
                  ·
                    refine ⟨3243421093350856819800769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17298245831204569705604101 3243421093350856819800769)
                    ·
                      refine ⟨2432565820013142614850577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243421093350856819800769 2432565820013142614850577)
                      ·
                        rfl

theorem cell23_4737405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_4737405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737405 prefixEnd_4737405 := by exact prefixLift 4737405
  have htrace : WordTrace (prefixWord ++ tailWord_4737405) baseStart_4737405 baseEnd_4737405 := by
    simpa [prefixWord, tailWord_4737405, baseEnd_4737405] using wordTrace_append hprefix tailTrace_4737405
  have hstable : (prefixWord ++ tailWord_4737405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737405).length < 2 ^ (prefixWord ++ tailWord_4737405).sum := by decide
  have hdescent : baseEnd_4737405 < baseStart_4737405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737415 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 3, 4]
def baseStart_4737415 : Nat := 118140960795 + 4737415 * 2 ^ 59
def prefixEnd_4737415 : Nat := 4983230072969 + 3 ^ 40 * 4737415 * 2
def baseEnd_4737415 : Nat := 810856984939895858575177

theorem tailTrace_4737415 : CollatzResearch.WordTrace tailWord_4737415 prefixEnd_4737415 810856984939895858575177 := by
  unfold tailWord_4737415
  simp only [CollatzResearch.WordTrace]
  refine ⟨172787720132162015912477699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115191813421441343941651799 172787720132162015912477699)
  ·
    refine ⟨259181580198243023868716549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172787720132162015912477699 259181580198243023868716549)
    ·
      refine ⟨48596546287170566975384353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259181580198243023868716549 48596546287170566975384353)
      ·
        refine ⟨36447409715377925231538265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48596546287170566975384353 36447409715377925231538265)
        ·
          refine ⟨27335557286533443923653699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36447409715377925231538265 27335557286533443923653699)
          ·
            refine ⟨41003335929800165885480549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27335557286533443923653699 41003335929800165885480549)
            ·
              refine ⟨7688125486837531103527603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41003335929800165885480549 7688125486837531103527603)
              ·
                refine ⟨11532188230256296655291405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7688125486837531103527603 11532188230256296655291405)
                ·
                  refine ⟨4324570586346111245734277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11532188230256296655291405 4324570586346111245734277)
                  ·
                    refine ⟨810856984939895858575177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324570586346111245734277 810856984939895858575177)
                    ·
                      rfl

theorem cell23_4737415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_4737415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737415 prefixEnd_4737415 := by exact prefixLift 4737415
  have htrace : WordTrace (prefixWord ++ tailWord_4737415) baseStart_4737415 baseEnd_4737415 := by
    simpa [prefixWord, tailWord_4737415, baseEnd_4737415] using wordTrace_append hprefix tailTrace_4737415
  have hstable : (prefixWord ++ tailWord_4737415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737415).length < 2 ^ (prefixWord ++ tailWord_4737415).sum := by decide
  have hdescent : baseEnd_4737415 < baseStart_4737415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737422 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4737422 : Nat := 118140960795 + 4737422 * 2 ^ 59
def prefixEnd_4737422 : Nat := 4983230072969 + 3 ^ 40 * 4737422 * 2
def baseEnd_4737422 : Nat := 2432574549184269048337999

theorem tailTrace_4737422 : CollatzResearch.WordTrace tailWord_4737422 prefixEnd_4737422 2432574549184269048337999 := by
  unfold tailWord_4737422
  simp only [CollatzResearch.WordTrace]
  refine ⟨21598496930392082013497815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115191983628757770738655013 21598496930392082013497815)
  ·
    refine ⟨32397745395588123020246723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21598496930392082013497815 32397745395588123020246723)
    ·
      refine ⟨48596618093382184530370085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32397745395588123020246723 48596618093382184530370085)
      ·
        refine ⟨9111865892509159599444391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48596618093382184530370085 9111865892509159599444391)
        ·
          refine ⟨13667798838763739399166587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9111865892509159599444391 13667798838763739399166587)
          ·
            refine ⟨20501698258145609098749881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13667798838763739399166587 20501698258145609098749881)
            ·
              refine ⟨15376273693609206824062411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20501698258145609098749881 15376273693609206824062411)
              ·
                refine ⟨23064410540413810236093617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15376273693609206824062411 23064410540413810236093617)
                ·
                  refine ⟨17298307905310357677070213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23064410540413810236093617 17298307905310357677070213)
                  ·
                    refine ⟨3243432732245692064450665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17298307905310357677070213 3243432732245692064450665)
                    ·
                      refine ⟨2432574549184269048337999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243432732245692064450665 2432574549184269048337999)
                      ·
                        rfl

theorem cell23_4737422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4737422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737422 prefixEnd_4737422 := by exact prefixLift 4737422
  have htrace : WordTrace (prefixWord ++ tailWord_4737422) baseStart_4737422 baseEnd_4737422 := by
    simpa [prefixWord, tailWord_4737422, baseEnd_4737422] using wordTrace_append hprefix tailTrace_4737422
  have hstable : (prefixWord ++ tailWord_4737422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737422).length < 2 ^ (prefixWord ++ tailWord_4737422).sum := by decide
  have hdescent : baseEnd_4737422 < baseStart_4737422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737492 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4737492 : Nat := 118140960795 + 4737492 * 2 ^ 59
def prefixEnd_4737492 : Nat := 4983230072969 + 3 ^ 40 * 4737492 * 2
def baseEnd_4737492 : Nat := 810870164276694591487559

theorem tailTrace_4737492 : CollatzResearch.WordTrace tailWord_4737492 prefixEnd_4737492 810870164276694591487559 := by
  unfold tailWord_4737492
  simp only [CollatzResearch.WordTrace]
  refine ⟨86395264276441529031515365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115193685701922038708687153 86395264276441529031515365)
  ·
    refine ⟨16199112051832786693409131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86395264276441529031515365 16199112051832786693409131)
    ·
      refine ⟨24298668077749180040113697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16199112051832786693409131 24298668077749180040113697)
      ·
        refine ⟨18224001058311885030085273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24298668077749180040113697 18224001058311885030085273)
        ·
          refine ⟨13668000793733913772563955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18224001058311885030085273 13668000793733913772563955)
          ·
            refine ⟨20502001190600870658845933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668000793733913772563955 20502001190600870658845933)
            ·
              refine ⟨7688250446475326497067225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20502001190600870658845933 7688250446475326497067225)
              ·
                refine ⟨5766187834856494872800419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688250446475326497067225 5766187834856494872800419)
                ·
                  refine ⟨8649281752284742309200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766187834856494872800419 8649281752284742309200629)
                  ·
                    refine ⟨810870164276694591487559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8649281752284742309200629 810870164276694591487559)
                    ·
                      rfl

theorem cell23_4737492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4737492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737492 prefixEnd_4737492 := by exact prefixLift 4737492
  have htrace : WordTrace (prefixWord ++ tailWord_4737492) baseStart_4737492 baseEnd_4737492 := by
    simpa [prefixWord, tailWord_4737492, baseEnd_4737492] using wordTrace_append hprefix tailTrace_4737492
  have hstable : (prefixWord ++ tailWord_4737492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737492).length < 2 ^ (prefixWord ++ tailWord_4737492).sum := by decide
  have hdescent : baseEnd_4737492 < baseStart_4737492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737509 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_4737509 : Nat := 118140960795 + 4737509 * 2 ^ 59
def prefixEnd_4737509 : Nat := 4983230072969 + 3 ^ 40 * 4737509 * 2
def baseEnd_4737509 : Nat := 810873074000403402650033

theorem tailTrace_4737509 : CollatzResearch.WordTrace tailWord_4737509 prefixEnd_4737509 810873074000403402650033 := by
  unfold tailWord_4737509
  simp only [CollatzResearch.WordTrace]
  refine ⟨172791148593821469966399581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115194099062547646644266387 172791148593821469966399581)
  ·
    refine ⟨64796680722683051237399843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172791148593821469966399581 64796680722683051237399843)
    ·
      refine ⟨97195021084024576856099765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64796680722683051237399843 97195021084024576856099765)
      ·
        refine ⟨9112033226627304080259353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97195021084024576856099765 9112033226627304080259353)
        ·
          refine ⟨6834024919970478060194515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9112033226627304080259353 6834024919970478060194515)
          ·
            refine ⟨10251037379955717090291773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834024919970478060194515 10251037379955717090291773)
            ·
              refine ⟨3844139017483393908859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251037379955717090291773 3844139017483393908859415)
              ·
                refine ⟨5766208526225090863289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844139017483393908859415 5766208526225090863289123)
                ·
                  refine ⟨8649312789337636294933685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766208526225090863289123 8649312789337636294933685)
                  ·
                    refine ⟨810873074000403402650033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8649312789337636294933685 810873074000403402650033)
                    ·
                      rfl

theorem cell23_4737509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_4737509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737509 prefixEnd_4737509 := by exact prefixLift 4737509
  have htrace : WordTrace (prefixWord ++ tailWord_4737509) baseStart_4737509 baseEnd_4737509 := by
    simpa [prefixWord, tailWord_4737509, baseEnd_4737509] using wordTrace_append hprefix tailTrace_4737509
  have hstable : (prefixWord ++ tailWord_4737509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737509).length < 2 ^ (prefixWord ++ tailWord_4737509).sum := by decide
  have hdescent : baseEnd_4737509 < baseStart_4737509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737518 : List Nat := [4, 1, 2, 1, 2, 13]
def baseStart_4737518 : Nat := 118140960795 + 4737518 * 2 ^ 59
def prefixEnd_4737518 : Nat := 4983230072969 + 3 ^ 40 * 4737518 * 2
def baseEnd_4737518 : Nat := 10010797709165023344599

theorem tailTrace_4737518 : CollatzResearch.WordTrace tailWord_4737518 prefixEnd_4737518 10010797709165023344599 := by
  unfold tailWord_4737518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21598934606348608062934651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115194317900525909668984805 21598934606348608062934651)
  ·
    refine ⟨32398401909522912094401977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21598934606348608062934651 32398401909522912094401977)
    ·
      refine ⟨24298801432142184070801483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32398401909522912094401977 24298801432142184070801483)
      ·
        refine ⟨36448202148213276106202225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24298801432142184070801483 36448202148213276106202225)
        ·
          refine ⟨27336151611159957079651669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36448202148213276106202225 27336151611159957079651669)
          ·
            refine ⟨10010797709165023344599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 27336151611159957079651669 10010797709165023344599)
            ·
              rfl

theorem cell23_4737518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 13].length) (baseStart_4737518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737518 prefixEnd_4737518 := by exact prefixLift 4737518
  have htrace : WordTrace (prefixWord ++ tailWord_4737518) baseStart_4737518 baseEnd_4737518 := by
    simpa [prefixWord, tailWord_4737518, baseEnd_4737518] using wordTrace_append hprefix tailTrace_4737518
  have hstable : (prefixWord ++ tailWord_4737518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737518).length < 2 ^ (prefixWord ++ tailWord_4737518).sum := by decide
  have hdescent : baseEnd_4737518 < baseStart_4737518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737596 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_4737596 : Nat := 118140960795 + 4737596 * 2 ^ 59
def prefixEnd_4737596 : Nat := 4983230072969 + 3 ^ 40 * 4737596 * 2
def baseEnd_4737596 : Nat := 2432663894818151367562199

theorem tailTrace_4737596 : CollatzResearch.WordTrace tailWord_4737596 prefixEnd_4737596 2432663894818151367562199 := by
  unfold tailWord_4737596
  simp only [CollatzResearch.WordTrace]
  refine ⟨86397160872253141912408321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115196214496337522549877761 86397160872253141912408321)
  ·
    refine ⟨64797870654189856434306241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86397160872253141912408321 64797870654189856434306241)
    ·
      refine ⟨48598402990642392325729681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64797870654189856434306241 48598402990642392325729681)
      ·
        refine ⟨36448802242981794244297261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48598402990642392325729681 36448802242981794244297261)
        ·
          refine ⟨13668300841118172841611473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36448802242981794244297261 13668300841118172841611473)
          ·
            refine ⟨10251225630838629631208605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13668300841118172841611473 10251225630838629631208605)
            ·
              refine ⟨3844209611564486111703227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251225630838629631208605 3844209611564486111703227)
              ·
                refine ⟨5766314417346729167554841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844209611564486111703227 5766314417346729167554841)
                ·
                  refine ⟨4324735813010046875666131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766314417346729167554841 4324735813010046875666131)
                  ·
                    refine ⟨6487103719515070313499197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324735813010046875666131 6487103719515070313499197)
                    ·
                      refine ⟨2432663894818151367562199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487103719515070313499197 2432663894818151367562199)
                      ·
                        rfl

theorem cell23_4737596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_4737596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737596 prefixEnd_4737596 := by exact prefixLift 4737596
  have htrace : WordTrace (prefixWord ++ tailWord_4737596) baseStart_4737596 baseEnd_4737596 := by
    simpa [prefixWord, tailWord_4737596, baseEnd_4737596] using wordTrace_append hprefix tailTrace_4737596
  have hstable : (prefixWord ++ tailWord_4737596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737596).length < 2 ^ (prefixWord ++ tailWord_4737596).sum := by decide
  have hdescent : baseEnd_4737596 < baseStart_4737596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737653 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4737653 : Nat := 118140960795 + 4737653 * 2 ^ 59
def prefixEnd_4737653 : Nat := 4983230072969 + 3 ^ 40 * 4737653 * 2
def baseEnd_4737653 : Nat := 2432693163215457644549437

theorem tailTrace_4737653 : CollatzResearch.WordTrace tailWord_4737653 prefixEnd_4737653 2432693163215457644549437 := by
  unfold tailWord_4737653
  simp only [CollatzResearch.WordTrace]
  refine ⟨172796400705299782559641613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115197600470199855039761075 172796400705299782559641613)
  ·
    refine ⟨64798650264487418459865605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172796400705299782559641613 64798650264487418459865605)
    ·
      refine ⟨12149746924591390961224801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64798650264487418459865605 12149746924591390961224801)
      ·
        refine ⟨9112310193443543220918601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12149746924591390961224801 9112310193443543220918601)
        ·
          refine ⟨6834232645082657415688951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9112310193443543220918601 6834232645082657415688951)
          ·
            refine ⟨10251348967623986123533427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834232645082657415688951 10251348967623986123533427)
            ·
              refine ⟨15377023451435979185300141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251348967623986123533427 15377023451435979185300141)
              ·
                refine ⟨5766383794288492194487553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15377023451435979185300141 5766383794288492194487553)
                ·
                  refine ⟨4324787845716369145865665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766383794288492194487553 4324787845716369145865665)
                  ·
                    refine ⟨3243590884287276859399249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324787845716369145865665 3243590884287276859399249)
                    ·
                      refine ⟨2432693163215457644549437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243590884287276859399249 2432693163215457644549437)
                      ·
                        rfl

theorem cell23_4737653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4737653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737653 prefixEnd_4737653 := by exact prefixLift 4737653
  have htrace : WordTrace (prefixWord ++ tailWord_4737653) baseStart_4737653 baseEnd_4737653 := by
    simpa [prefixWord, tailWord_4737653, baseEnd_4737653] using wordTrace_append hprefix tailTrace_4737653
  have hstable : (prefixWord ++ tailWord_4737653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737653).length < 2 ^ (prefixWord ++ tailWord_4737653).sum := by decide
  have hdescent : baseEnd_4737653 < baseStart_4737653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737665 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4737665 : Nat := 118140960795 + 4737665 * 2 ^ 59
def prefixEnd_4737665 : Nat := 4983230072969 + 3 ^ 40 * 4737665 * 2
def baseEnd_4737665 : Nat := 2432699324983311597599381

theorem tailTrace_4737665 : CollatzResearch.WordTrace tailWord_4737665 prefixEnd_4737665 2432699324983311597599381 := by
  unfold tailWord_4737665
  simp only [CollatzResearch.WordTrace]
  refine ⟨172796838381256308609078449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115197892254170872406052299 172796838381256308609078449)
  ·
    refine ⟨129597628785942231456808837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172796838381256308609078449 129597628785942231456808837)
    ·
      refine ⟨24299555397364168398151657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129597628785942231456808837 24299555397364168398151657)
      ·
        refine ⟨18224666548023126298613743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24299555397364168398151657 18224666548023126298613743)
        ·
          refine ⟨27336999822034689447920615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18224666548023126298613743 27336999822034689447920615)
          ·
            refine ⟨41005499733052034171880923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27336999822034689447920615 41005499733052034171880923)
            ·
              refine ⟨61508249599578051257821385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41005499733052034171880923 61508249599578051257821385)
              ·
                refine ⟨46131187199683538443366039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61508249599578051257821385 46131187199683538443366039)
                ·
                  refine ⟨69196780799525307665049059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46131187199683538443366039 69196780799525307665049059)
                  ·
                    refine ⟨103795171199287961497573589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69196780799525307665049059 103795171199287961497573589)
                    ·
                      refine ⟨2432699324983311597599381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103795171199287961497573589 2432699324983311597599381)
                      ·
                        rfl

theorem cell23_4737665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4737665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737665 prefixEnd_4737665 := by exact prefixLift 4737665
  have htrace : WordTrace (prefixWord ++ tailWord_4737665) baseStart_4737665 baseEnd_4737665 := by
    simpa [prefixWord, tailWord_4737665, baseEnd_4737665] using wordTrace_append hprefix tailTrace_4737665
  have hstable : (prefixWord ++ tailWord_4737665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737665).length < 2 ^ (prefixWord ++ tailWord_4737665).sum := by decide
  have hdescent : baseEnd_4737665 < baseStart_4737665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737682 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4737682 : Nat := 118140960795 + 4737682 * 2 ^ 59
def prefixEnd_4737682 : Nat := 4983230072969 + 3 ^ 40 * 4737682 * 2
def baseEnd_4737682 : Nat := 2432708054154438031086803

theorem tailTrace_4737682 : CollatzResearch.WordTrace tailWord_4737682 prefixEnd_4737682 2432708054154438031086803 := by
  unfold tailWord_4737682
  simp only [CollatzResearch.WordTrace]
  refine ⟨43199364605548680128111825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115198305614796480341631533 43199364605548680128111825)
  ·
    refine ⟨32399523454161510096083869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43199364605548680128111825 32399523454161510096083869)
    ·
      refine ⟨12149821295310566286031451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32399523454161510096083869 12149821295310566286031451)
      ·
        refine ⟨18224731942965849429047177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12149821295310566286031451 18224731942965849429047177)
        ·
          refine ⟨13668548957224387071785383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18224731942965849429047177 13668548957224387071785383)
          ·
            refine ⟨20502823435836580607678075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668548957224387071785383 20502823435836580607678075)
            ·
              refine ⟨30754235153754870911517113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20502823435836580607678075 30754235153754870911517113)
              ·
                refine ⟨23065676365316153183637835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30754235153754870911517113 23065676365316153183637835)
                ·
                  refine ⟨34598514547974229775456753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23065676365316153183637835 34598514547974229775456753)
                  ·
                    refine ⟨25948885910980672331592565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34598514547974229775456753 25948885910980672331592565)
                    ·
                      refine ⟨2432708054154438031086803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25948885910980672331592565 2432708054154438031086803)
                      ·
                        rfl

theorem cell23_4737682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4737682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737682 prefixEnd_4737682 := by exact prefixLift 4737682
  have htrace : WordTrace (prefixWord ++ tailWord_4737682) baseStart_4737682 baseEnd_4737682 := by
    simpa [prefixWord, tailWord_4737682, baseEnd_4737682] using wordTrace_append hprefix tailTrace_4737682
  have hstable : (prefixWord ++ tailWord_4737682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737682).length < 2 ^ (prefixWord ++ tailWord_4737682).sum := by decide
  have hdescent : baseEnd_4737682 < baseStart_4737682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737709 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_4737709 : Nat := 118140960795 + 4737709 * 2 ^ 59
def prefixEnd_4737709 : Nat := 4983230072969 + 3 ^ 40 * 4737709 * 2
def baseEnd_4737709 : Nat := 2432721918132109425449179

theorem tailTrace_4737709 : CollatzResearch.WordTrace tailWord_4737709 prefixEnd_4737709 2432721918132109425449179 := by
  unfold tailWord_4737709
  simp only [CollatzResearch.WordTrace]
  refine ⟨172798443193096904123680181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115198962128731269415786787 172798443193096904123680181)
  ·
    refine ⟨16199854049352834761595017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172798443193096904123680181 16199854049352834761595017)
    ·
      refine ⟨12149890537014626071196263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16199854049352834761595017 12149890537014626071196263)
      ·
        refine ⟨18224835805521939106794395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12149890537014626071196263 18224835805521939106794395)
        ·
          refine ⟨27337253708282908660191593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18224835805521939106794395 27337253708282908660191593)
          ·
            refine ⟨20502940281212181495143695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27337253708282908660191593 20502940281212181495143695)
            ·
              refine ⟨30754410421818272242715543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20502940281212181495143695 30754410421818272242715543)
              ·
                refine ⟨46131615632727408364073315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30754410421818272242715543 46131615632727408364073315)
                ·
                  refine ⟨69197423449091112546109973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46131615632727408364073315 69197423449091112546109973)
                  ·
                    refine ⟨3243629224176145900598905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69197423449091112546109973 3243629224176145900598905)
                    ·
                      refine ⟨2432721918132109425449179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243629224176145900598905 2432721918132109425449179)
                      ·
                        rfl

theorem cell23_4737709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_4737709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737709 prefixEnd_4737709 := by exact prefixLift 4737709
  have htrace : WordTrace (prefixWord ++ tailWord_4737709) baseStart_4737709 baseEnd_4737709 := by
    simpa [prefixWord, tailWord_4737709, baseEnd_4737709] using wordTrace_append hprefix tailTrace_4737709
  have hstable : (prefixWord ++ tailWord_4737709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737709).length < 2 ^ (prefixWord ++ tailWord_4737709).sum := by decide
  have hdescent : baseEnd_4737709 < baseStart_4737709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737719 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 3, 4]
def baseStart_4737719 : Nat := 118140960795 + 4737719 * 2 ^ 59
def prefixEnd_4737719 : Nat := 4983230072969 + 3 ^ 40 * 4737719 * 2
def baseEnd_4737719 : Nat := 810909017646218128774711

theorem tailTrace_4737719 : CollatzResearch.WordTrace tailWord_4737719 prefixEnd_4737719 810909017646218128774711 := by
  unfold tailWord_4737719
  simp only [CollatzResearch.WordTrace]
  refine ⟨172798807923060675831544211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115199205282040450554362807 172798807923060675831544211)
  ·
    refine ⟨259198211884591013747316317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172798807923060675831544211 259198211884591013747316317)
    ·
      refine ⟨97199329456721630155243619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259198211884591013747316317 97199329456721630155243619)
      ·
        refine ⟨145798994185082445232865429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97199329456721630155243619 145798994185082445232865429)
        ·
          refine ⟨6834327852425739620290567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145798994185082445232865429 6834327852425739620290567)
          ·
            refine ⟨10251491778638609430435851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834327852425739620290567 10251491778638609430435851)
            ·
              refine ⟨15377237667957914145653777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251491778638609430435851 15377237667957914145653777)
              ·
                refine ⟨11532928250968435609240333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15377237667957914145653777 11532928250968435609240333)
                ·
                  refine ⟨4324848094113163353465125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11532928250968435609240333 4324848094113163353465125)
                  ·
                    refine ⟨810909017646218128774711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324848094113163353465125 810909017646218128774711)
                    ·
                      rfl

theorem cell23_4737719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_4737719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737719 prefixEnd_4737719 := by exact prefixLift 4737719
  have htrace : WordTrace (prefixWord ++ tailWord_4737719) baseStart_4737719 baseEnd_4737719 := by
    simpa [prefixWord, tailWord_4737719, baseEnd_4737719] using wordTrace_append hprefix tailTrace_4737719
  have hstable : (prefixWord ++ tailWord_4737719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737719).length < 2 ^ (prefixWord ++ tailWord_4737719).sum := by decide
  have hdescent : baseEnd_4737719 < baseStart_4737719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737736 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 1, 4]
def baseStart_4737736 : Nat := 118140960795 + 4737736 * 2 ^ 59
def prefixEnd_4737736 : Nat := 4983230072969 + 3 ^ 40 * 4737736 * 2
def baseEnd_4737736 : Nat := 810911927369926939937185

theorem tailTrace_4737736 : CollatzResearch.WordTrace tailWord_4737736 prefixEnd_4737736 810911927369926939937185 := by
  unfold tailWord_4737736
  simp only [CollatzResearch.WordTrace]
  refine ⟨86399713981999543867456531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115199618642666058489942041 86399713981999543867456531)
  ·
    refine ⟨129599570972999315801184797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86399713981999543867456531 129599570972999315801184797)
    ·
      refine ⟨48599839114874743425444299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129599570972999315801184797 48599839114874743425444299)
      ·
        refine ⟨72899758672312115138166449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48599839114874743425444299 72899758672312115138166449)
        ·
          refine ⟨54674819004234086353624837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72899758672312115138166449 54674819004234086353624837)
          ·
            refine ⟨10251528563293891191304657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54674819004234086353624837 10251528563293891191304657)
            ·
              refine ⟨7688646422470418393478493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10251528563293891191304657 7688646422470418393478493)
              ·
                refine ⟨2883242408426406897554435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7688646422470418393478493 2883242408426406897554435)
                ·
                  refine ⟨4324863612639610346331653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883242408426406897554435 4324863612639610346331653)
                  ·
                    refine ⟨810911927369926939937185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324863612639610346331653 810911927369926939937185)
                    ·
                      rfl

theorem cell23_4737736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_4737736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737736 prefixEnd_4737736 := by exact prefixLift 4737736
  have htrace : WordTrace (prefixWord ++ tailWord_4737736) baseStart_4737736 baseEnd_4737736 := by
    simpa [prefixWord, tailWord_4737736, baseEnd_4737736] using wordTrace_append hprefix tailTrace_4737736
  have hstable : (prefixWord ++ tailWord_4737736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737736).length < 2 ^ (prefixWord ++ tailWord_4737736).sum := by decide
  have hdescent : baseEnd_4737736 < baseStart_4737736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737749 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 8]
def baseStart_4737749 : Nat := 118140960795 + 4737749 * 2 ^ 59
def prefixEnd_4737749 : Nat := 4983230072969 + 3 ^ 40 * 4737749 * 2
def baseEnd_4737749 : Nat := 270304717484254363216555

theorem tailTrace_4737749 : CollatzResearch.WordTrace tailWord_4737749 prefixEnd_4737749 270304717484254363216555 := by
  unfold tailWord_4737749
  simp only [CollatzResearch.WordTrace]
  refine ⟨172799902112951990955136301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115199934741967993970090867 172799902112951990955136301)
  ·
    refine ⟨64799963292356996608176113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172799902112951990955136301 64799963292356996608176113)
    ·
      refine ⟨48599972469267747456132085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64799963292356996608176113 48599972469267747456132085)
      ·
        refine ⟨4556247418993851324012383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48599972469267747456132085 4556247418993851324012383)
        ·
          refine ⟨6834371128490776986018575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556247418993851324012383 6834371128490776986018575)
          ·
            refine ⟨10251556692736165479027863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834371128490776986018575 10251556692736165479027863)
            ·
              refine ⟨15377335039104248218541795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251556692736165479027863 15377335039104248218541795)
              ·
                refine ⟨23066002558656372327812693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15377335039104248218541795 23066002558656372327812693)
                ·
                  refine ⟨270304717484254363216555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23066002558656372327812693 270304717484254363216555)
                  ·
                    rfl

theorem cell23_4737749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_4737749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737749 prefixEnd_4737749 := by exact prefixLift 4737749
  have htrace : WordTrace (prefixWord ++ tailWord_4737749) baseStart_4737749 baseEnd_4737749 := by
    simpa [prefixWord, tailWord_4737749, baseEnd_4737749] using wordTrace_append hprefix tailTrace_4737749
  have hstable : (prefixWord ++ tailWord_4737749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737749).length < 2 ^ (prefixWord ++ tailWord_4737749).sum := by decide
  have hdescent : baseEnd_4737749 < baseStart_4737749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737759 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_4737759 : Nat := 118140960795 + 4737759 * 2 ^ 59
def prefixEnd_4737759 : Nat := 4983230072969 + 3 ^ 40 * 4737759 * 2
def baseEnd_4737759 : Nat := 2432747592164834229823949

theorem tailTrace_4737759 : CollatzResearch.WordTrace tailWord_4737759 prefixEnd_4737759 2432747592164834229823949 := by
  unfold tailWord_4737759
  simp only [CollatzResearch.WordTrace]
  refine ⟨172800266842915762663000331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115200177895277175108666887 172800266842915762663000331)
  ·
    refine ⟨259200400264373643994500497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172800266842915762663000331 259200400264373643994500497)
    ·
      refine ⟨194400300198280232995875373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259200400264373643994500497 194400300198280232995875373)
      ·
        refine ⟨72900112574355087373453265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194400300198280232995875373 72900112574355087373453265)
        ·
          refine ⟨54675084430766315530089949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72900112574355087373453265 54675084430766315530089949)
          ·
            refine ⟨20503156661537368323783731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54675084430766315530089949 20503156661537368323783731)
            ·
              refine ⟨30754734992306052485675597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20503156661537368323783731 30754734992306052485675597)
              ·
                refine ⟨11533025622114769682128349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30754734992306052485675597 11533025622114769682128349)
                ·
                  refine ⟨4324884608293038630798131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11533025622114769682128349 4324884608293038630798131)
                  ·
                    refine ⟨6487326912439557946197197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324884608293038630798131 6487326912439557946197197)
                    ·
                      refine ⟨2432747592164834229823949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487326912439557946197197 2432747592164834229823949)
                      ·
                        rfl

theorem cell23_4737759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_4737759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737759 prefixEnd_4737759 := by exact prefixLift 4737759
  have htrace : WordTrace (prefixWord ++ tailWord_4737759) baseStart_4737759 baseEnd_4737759 := by
    simpa [prefixWord, tailWord_4737759, baseEnd_4737759] using wordTrace_append hprefix tailTrace_4737759
  have hstable : (prefixWord ++ tailWord_4737759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737759).length < 2 ^ (prefixWord ++ tailWord_4737759).sum := by decide
  have hdescent : baseEnd_4737759 < baseStart_4737759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737810 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4737810 : Nat := 118140960795 + 4737810 * 2 ^ 59
def prefixEnd_4737810 : Nat := 4983230072969 + 3 ^ 40 * 4737810 * 2
def baseEnd_4737810 : Nat := 2432773779678213530286215

theorem tailTrace_4737810 : CollatzResearch.WordTrace tailWord_4737810 prefixEnd_4737810 2432773779678213530286215 := by
  unfold tailWord_4737810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43200531741432749593276721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115201417977153998915404589 43200531741432749593276721)
  ·
    refine ⟨32400398806074562194957541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43200531741432749593276721 32400398806074562194957541)
    ·
      refine ⟨6075074776138980411554539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32400398806074562194957541 6075074776138980411554539)
      ·
        refine ⟨9112612164208470617331809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075074776138980411554539 9112612164208470617331809)
        ·
          refine ⟨6834459123156352962998857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9112612164208470617331809 6834459123156352962998857)
          ·
            refine ⟨5125844342367264722249143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834459123156352962998857 5125844342367264722249143)
            ·
              refine ⟨7688766513550897083373715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125844342367264722249143 7688766513550897083373715)
              ·
                refine ⟨11533149770326345625060573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7688766513550897083373715 11533149770326345625060573)
                ·
                  refine ⟨4324931163872379609397715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11533149770326345625060573 4324931163872379609397715)
                  ·
                    refine ⟨6487396745808569414096573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324931163872379609397715 6487396745808569414096573)
                    ·
                      refine ⟨2432773779678213530286215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487396745808569414096573 2432773779678213530286215)
                      ·
                        rfl

theorem cell23_4737810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4737810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737810 prefixEnd_4737810 := by exact prefixLift 4737810
  have htrace : WordTrace (prefixWord ++ tailWord_4737810) baseStart_4737810 baseEnd_4737810 := by
    simpa [prefixWord, tailWord_4737810, baseEnd_4737810] using wordTrace_append hprefix tailTrace_4737810
  have hstable : (prefixWord ++ tailWord_4737810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737810).length < 2 ^ (prefixWord ++ tailWord_4737810).sum := by decide
  have hdescent : baseEnd_4737810 < baseStart_4737810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737826 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4737826 : Nat := 118140960795 + 4737826 * 2 ^ 59
def prefixEnd_4737826 : Nat := 4983230072969 + 3 ^ 40 * 4737826 * 2
def baseEnd_4737826 : Nat := 810927331789561822562047

theorem tailTrace_4737826 : CollatzResearch.WordTrace tailWord_4737826 prefixEnd_4737826 810927331789561822562047 := by
  unfold tailWord_4737826
  simp only [CollatzResearch.WordTrace]
  refine ⟨43200677633418258276422333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115201807022448688737126221 43200677633418258276422333)
  ·
    refine ⟨16200254112531846853658375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43200677633418258276422333 16200254112531846853658375)
    ·
      refine ⟨24300381168797770280487563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16200254112531846853658375 24300381168797770280487563)
      ·
        refine ⟨36450571753196655420731345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24300381168797770280487563 36450571753196655420731345)
        ·
          refine ⟨27337928814897491565548509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36450571753196655420731345 27337928814897491565548509)
          ·
            refine ⟨10251723305586559337080691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27337928814897491565548509 10251723305586559337080691)
            ·
              refine ⟨15377584958379839005621037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251723305586559337080691 15377584958379839005621037)
              ·
                refine ⟨5766594359392439627107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15377584958379839005621037 5766594359392439627107889)
                ·
                  refine ⟨4324945769544329720330917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766594359392439627107889 4324945769544329720330917)
                  ·
                    refine ⟨810927331789561822562047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324945769544329720330917 810927331789561822562047)
                    ·
                      rfl

theorem cell23_4737826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4737826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737826 prefixEnd_4737826 := by exact prefixLift 4737826
  have htrace : WordTrace (prefixWord ++ tailWord_4737826) baseStart_4737826 baseEnd_4737826 := by
    simpa [prefixWord, tailWord_4737826, baseEnd_4737826] using wordTrace_append hprefix tailTrace_4737826
  have hstable : (prefixWord ++ tailWord_4737826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737826).length < 2 ^ (prefixWord ++ tailWord_4737826).sum := by decide
  have hdescent : baseEnd_4737826 < baseStart_4737826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737853 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4737853 : Nat := 118140960795 + 4737853 * 2 ^ 59
def prefixEnd_4737853 : Nat := 4983230072969 + 3 ^ 40 * 4737853 * 2
def baseEnd_4737853 : Nat := 2432795859346356862048517

theorem tailTrace_4737853 : CollatzResearch.WordTrace tailWord_4737853 prefixEnd_4737853 2432795859346356862048517 := by
  unfold tailWord_4737853
  simp only [CollatzResearch.WordTrace]
  refine ⟨172803695304575216716922213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115202463536383477811281475 172803695304575216716922213)
  ·
    refine ⟨32400692869607853134422915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172803695304575216716922213 32400692869607853134422915)
    ·
      refine ⟨48601039304411779701634373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32400692869607853134422915 48601039304411779701634373)
      ·
        refine ⟨9112694869577208694056445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48601039304411779701634373 9112694869577208694056445)
        ·
          refine ⟨3417260576091453260271167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9112694869577208694056445 3417260576091453260271167)
          ·
            refine ⟨5125890864137179890406751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417260576091453260271167 5125890864137179890406751)
            ·
              refine ⟨7688836296205769835610127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125890864137179890406751 7688836296205769835610127)
              ·
                refine ⟨11533254444308654753415191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7688836296205769835610127 11533254444308654753415191)
                ·
                  refine ⟨17299881666462982130122787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11533254444308654753415191 17299881666462982130122787)
                  ·
                    refine ⟨25949822499694473195184181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17299881666462982130122787 25949822499694473195184181)
                    ·
                      refine ⟨2432795859346356862048517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25949822499694473195184181 2432795859346356862048517)
                      ·
                        rfl

theorem cell23_4737853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4737853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737853 prefixEnd_4737853 := by exact prefixLift 4737853
  have htrace : WordTrace (prefixWord ++ tailWord_4737853) baseStart_4737853 baseEnd_4737853 := by
    simpa [prefixWord, tailWord_4737853, baseEnd_4737853] using wordTrace_append hprefix tailTrace_4737853
  have hstable : (prefixWord ++ tailWord_4737853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737853).length < 2 ^ (prefixWord ++ tailWord_4737853).sum := by decide
  have hdescent : baseEnd_4737853 < baseStart_4737853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737860 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4737860 : Nat := 118140960795 + 4737860 * 2 ^ 59
def prefixEnd_4737860 : Nat := 4983230072969 + 3 ^ 40 * 4737860 * 2
def baseEnd_4737860 : Nat := 810933151236979444886995

theorem tailTrace_4737860 : CollatzResearch.WordTrace tailWord_4737860 prefixEnd_4737860 810933151236979444886995 := by
  unfold tailWord_4737860
  simp only [CollatzResearch.WordTrace]
  refine ⟨86401975307774928456213517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115202633743699904608284689 86401975307774928456213517)
  ·
    refine ⟨32400740740415598171080069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86401975307774928456213517 32400740740415598171080069)
    ·
      refine ⟨6075138888827924657077513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32400740740415598171080069 6075138888827924657077513)
      ·
        refine ⟨4556354166620943492808135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6075138888827924657077513 4556354166620943492808135)
        ·
          refine ⟨6834531249931415239212203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556354166620943492808135 6834531249931415239212203)
          ·
            refine ⟨10251796874897122858818305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834531249931415239212203 10251796874897122858818305)
            ·
              refine ⟨7688847656172842144113729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10251796874897122858818305 7688847656172842144113729)
              ·
                refine ⟨5766635742129631608085297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688847656172842144113729 5766635742129631608085297)
                ·
                  refine ⟨4324976806597223706063973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766635742129631608085297 4324976806597223706063973)
                  ·
                    refine ⟨810933151236979444886995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324976806597223706063973 810933151236979444886995)
                    ·
                      rfl

theorem cell23_4737860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4737860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737860 prefixEnd_4737860 := by exact prefixLift 4737860
  have htrace : WordTrace (prefixWord ++ tailWord_4737860) baseStart_4737860 baseEnd_4737860 := by
    simpa [prefixWord, tailWord_4737860, baseEnd_4737860] using wordTrace_append hprefix tailTrace_4737860
  have hstable : (prefixWord ++ tailWord_4737860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737860).length < 2 ^ (prefixWord ++ tailWord_4737860).sum := by decide
  have hdescent : baseEnd_4737860 < baseStart_4737860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737872 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_4737872 : Nat := 118140960795 + 4737872 * 2 ^ 59
def prefixEnd_4737872 : Nat := 4983230072969 + 3 ^ 40 * 4737872 * 2
def baseEnd_4737872 : Nat := 2432805615478792287710929

theorem tailTrace_4737872 : CollatzResearch.WordTrace tailWord_4737872 prefixEnd_4737872 2432805615478792287710929 := by
  unfold tailWord_4737872
  simp only [CollatzResearch.WordTrace]
  refine ⟨86402194145753191480931935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115202925527670921974575913 86402194145753191480931935)
  ·
    refine ⟨129603291218629787221397903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86402194145753191480931935 129603291218629787221397903)
    ·
      refine ⟨194404936827944680832096855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129603291218629787221397903 194404936827944680832096855)
      ·
        refine ⟨291607405241917021248145283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194404936827944680832096855 291607405241917021248145283)
        ·
          refine ⟨437411107862875531872217925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291607405241917021248145283 437411107862875531872217925)
          ·
            refine ⟨82014582724289162226040861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437411107862875531872217925 82014582724289162226040861)
            ·
              refine ⟨30755468521608435834765323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82014582724289162226040861 30755468521608435834765323)
              ·
                refine ⟨46133202782412653752147985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30755468521608435834765323 46133202782412653752147985)
                ·
                  refine ⟨34599902086809490314110989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46133202782412653752147985 34599902086809490314110989)
                  ·
                    refine ⟨12974963282553558867791621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34599902086809490314110989 12974963282553558867791621)
                    ·
                      refine ⟨2432805615478792287710929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12974963282553558867791621 2432805615478792287710929)
                      ·
                        rfl

theorem cell23_4737872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_4737872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737872 prefixEnd_4737872 := by exact prefixLift 4737872
  have htrace : WordTrace (prefixWord ++ tailWord_4737872) baseStart_4737872 baseEnd_4737872 := by
    simpa [prefixWord, tailWord_4737872, baseEnd_4737872] using wordTrace_append hprefix tailTrace_4737872
  have hstable : (prefixWord ++ tailWord_4737872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737872).length < 2 ^ (prefixWord ++ tailWord_4737872).sum := by decide
  have hdescent : baseEnd_4737872 < baseStart_4737872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737882 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_4737882 : Nat := 118140960795 + 4737882 * 2 ^ 59
def prefixEnd_4737882 : Nat := 4983230072969 + 3 ^ 40 * 4737882 * 2
def baseEnd_4737882 : Nat := 810936916761779082861961

theorem tailTrace_4737882 : CollatzResearch.WordTrace tailWord_4737882 prefixEnd_4737882 810936916761779082861961 := by
  unfold tailWord_4737882
  simp only [CollatzResearch.WordTrace]
  refine ⟨43201188255367538667431975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115203168680980103113151933 43201188255367538667431975)
  ·
    refine ⟨64801782383051308001147963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43201188255367538667431975 64801782383051308001147963)
    ·
      refine ⟨97202673574576962001721945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64801782383051308001147963 97202673574576962001721945)
      ·
        refine ⟨72902005180932721501291459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97202673574576962001721945 72902005180932721501291459)
        ·
          refine ⟨109353007771399082251937189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72902005180932721501291459 109353007771399082251937189)
          ·
            refine ⟨20503688957137327922238223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109353007771399082251937189 20503688957137327922238223)
            ·
              refine ⟨30755533435705991883357335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20503688957137327922238223 30755533435705991883357335)
              ·
                refine ⟨46133300153558987825036003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30755533435705991883357335 46133300153558987825036003)
                ·
                  refine ⟨69199950230338481737554005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46133300153558987825036003 69199950230338481737554005)
                  ·
                    refine ⟨810936916761779082861961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69199950230338481737554005 810936916761779082861961)
                    ·
                      rfl

theorem cell23_4737882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_4737882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737882 prefixEnd_4737882 := by exact prefixLift 4737882
  have htrace : WordTrace (prefixWord ++ tailWord_4737882) baseStart_4737882 baseEnd_4737882 := by
    simpa [prefixWord, tailWord_4737882, baseEnd_4737882] using wordTrace_append hprefix tailTrace_4737882
  have hstable : (prefixWord ++ tailWord_4737882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737882).length < 2 ^ (prefixWord ++ tailWord_4737882).sum := by decide
  have hdescent : baseEnd_4737882 < baseStart_4737882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737906 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4737906 : Nat := 118140960795 + 4737906 * 2 ^ 59
def prefixEnd_4737906 : Nat := 4983230072969 + 3 ^ 40 * 4737906 * 2
def baseEnd_4737906 : Nat := 2432823073821045154685773

theorem tailTrace_4737906 : CollatzResearch.WordTrace tailWord_4737906 prefixEnd_4737906 2432823073821045154685773 := by
  unfold tailWord_4737906
  simp only [CollatzResearch.WordTrace]
  refine ⟨43201407093345801692150393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115203752248922137845734381 43201407093345801692150393)
  ·
    refine ⟨32401055320009351269112795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43201407093345801692150393 32401055320009351269112795)
    ·
      refine ⟨48601582980014026903669193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32401055320009351269112795 48601582980014026903669193)
      ·
        refine ⟨36451187235010520177751895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48601582980014026903669193 36451187235010520177751895)
        ·
          refine ⟨54676780852515780266627843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36451187235010520177751895 54676780852515780266627843)
          ·
            refine ⟨82015171278773670399941765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54676780852515780266627843 82015171278773670399941765)
            ·
              refine ⟨15377844614770063199989081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82015171278773670399941765 15377844614770063199989081)
              ·
                refine ⟨11533383461077547399991811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15377844614770063199989081 11533383461077547399991811)
                ·
                  refine ⟨17300075191616321099987717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11533383461077547399991811 17300075191616321099987717)
                  ·
                    refine ⟨3243764098428060206247697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17300075191616321099987717 3243764098428060206247697)
                    ·
                      refine ⟨2432823073821045154685773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243764098428060206247697 2432823073821045154685773)
                      ·
                        rfl

theorem cell23_4737906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4737906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737906 prefixEnd_4737906 := by exact prefixLift 4737906
  have htrace : WordTrace (prefixWord ++ tailWord_4737906) baseStart_4737906 baseEnd_4737906 := by
    simpa [prefixWord, tailWord_4737906, baseEnd_4737906] using wordTrace_append hprefix tailTrace_4737906
  have hstable : (prefixWord ++ tailWord_4737906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737906).length < 2 ^ (prefixWord ++ tailWord_4737906).sum := by decide
  have hdescent : baseEnd_4737906 < baseStart_4737906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737910 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4737910 : Nat := 118140960795 + 4737910 * 2 ^ 59
def prefixEnd_4737910 : Nat := 4983230072969 + 3 ^ 40 * 4737910 * 2
def baseEnd_4737910 : Nat := 2432825127743663139035755

theorem tailTrace_4737910 : CollatzResearch.WordTrace tailWord_4737910 prefixEnd_4737910 2432825127743663139035755 := by
  unfold tailWord_4737910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800360891585544715734199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115203849510245810301164789 10800360891585544715734199)
  ·
    refine ⟨16200541337378317073601299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10800360891585544715734199 16200541337378317073601299)
    ·
      refine ⟨24300812006067475610401949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16200541337378317073601299 24300812006067475610401949)
      ·
        refine ⟨9112804502275303353900731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24300812006067475610401949 9112804502275303353900731)
        ·
          refine ⟨13669206753412955030851097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9112804502275303353900731 13669206753412955030851097)
          ·
            refine ⟨10251905065059716273138323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13669206753412955030851097 10251905065059716273138323)
            ·
              refine ⟨15377857597589574409707485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251905065059716273138323 15377857597589574409707485)
              ·
                refine ⟨5766696599096090403640307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15377857597589574409707485 5766696599096090403640307)
                ·
                  refine ⟨8650044898644135605460461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766696599096090403640307 8650044898644135605460461)
                  ·
                    refine ⟨3243766836991550852047673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8650044898644135605460461 3243766836991550852047673)
                    ·
                      refine ⟨2432825127743663139035755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243766836991550852047673 2432825127743663139035755)
                      ·
                        rfl

theorem cell23_4737910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4737910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737910 prefixEnd_4737910 := by exact prefixLift 4737910
  have htrace : WordTrace (prefixWord ++ tailWord_4737910) baseStart_4737910 baseEnd_4737910 := by
    simpa [prefixWord, tailWord_4737910, baseEnd_4737910] using wordTrace_append hprefix tailTrace_4737910
  have hstable : (prefixWord ++ tailWord_4737910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737910).length < 2 ^ (prefixWord ++ tailWord_4737910).sum := by decide
  have hdescent : baseEnd_4737910 < baseStart_4737910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737929 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 7]
def baseStart_4737929 : Nat := 118140960795 + 4737929 * 2 ^ 59
def prefixEnd_4737929 : Nat := 4983230072969 + 3 ^ 40 * 4737929 * 2
def baseEnd_4737929 : Nat := 270314987097344284966463

theorem tailTrace_4737929 : CollatzResearch.WordTrace tailWord_4737929 prefixEnd_4737929 270314987097344284966463 := by
  unfold tailWord_4737929
  simp only [CollatzResearch.WordTrace]
  refine ⟨172806467252299881696688841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115204311501533254464459227 172806467252299881696688841)
  ·
    refine ⟨129604850439224911272516631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172806467252299881696688841 129604850439224911272516631)
    ·
      refine ⟨194407275658837366908774947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129604850439224911272516631 194407275658837366908774947)
      ·
        refine ⟨291610913488256050363162421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194407275658837366908774947 291610913488256050363162421)
        ·
          refine ⟨27338523139524004721546477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 291610913488256050363162421 27338523139524004721546477)
          ·
            refine ⟨10251946177321501770579929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27338523139524004721546477 10251946177321501770579929)
            ·
              refine ⟨7688959632991126327934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10251946177321501770579929 7688959632991126327934947)
              ·
                refine ⟨11533439449486689491902421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7688959632991126327934947 11533439449486689491902421)
                ·
                  refine ⟨270314987097344284966463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11533439449486689491902421 270314987097344284966463)
                  ·
                    rfl

theorem cell23_4737929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_4737929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737929 prefixEnd_4737929 := by exact prefixLift 4737929
  have htrace : WordTrace (prefixWord ++ tailWord_4737929) baseStart_4737929 baseEnd_4737929 := by
    simpa [prefixWord, tailWord_4737929, baseEnd_4737929] using wordTrace_append hprefix tailTrace_4737929
  have hstable : (prefixWord ++ tailWord_4737929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737929).length < 2 ^ (prefixWord ++ tailWord_4737929).sum := by decide
  have hdescent : baseEnd_4737929 < baseStart_4737929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737996 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4737996 : Nat := 118140960795 + 4737996 * 2 ^ 59
def prefixEnd_4737996 : Nat := 4983230072969 + 3 ^ 40 * 4737996 * 2
def baseEnd_4737996 : Nat := 2432869287079949802560359

theorem tailTrace_4737996 : CollatzResearch.WordTrace tailWord_4737996 prefixEnd_4737996 2432869287079949802560359 := by
  unfold tailWord_4737996
  simp only [CollatzResearch.WordTrace]
  refine ⟨86404455471528576069688921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115205940628704768092918561 86404455471528576069688921)
  ·
    refine ⟨64803341603646432052266691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86404455471528576069688921 64803341603646432052266691)
    ·
      refine ⟨97205012405469648078400037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64803341603646432052266691 97205012405469648078400037)
      ·
        refine ⟨18225939826025559014700007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97205012405469648078400037 18225939826025559014700007)
        ·
          refine ⟨27338909739038338522050011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18225939826025559014700007 27338909739038338522050011)
          ·
            refine ⟨41008364608557507783075017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27338909739038338522050011 41008364608557507783075017)
            ·
              refine ⟨30756273456418130837306263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41008364608557507783075017 30756273456418130837306263)
              ·
                refine ⟨46134410184627196255959395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30756273456418130837306263 46134410184627196255959395)
                ·
                  refine ⟨69201615276940794383939093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46134410184627196255959395 69201615276940794383939093)
                  ·
                    refine ⟨3243825716106599736747145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69201615276940794383939093 3243825716106599736747145)
                    ·
                      refine ⟨2432869287079949802560359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243825716106599736747145 2432869287079949802560359)
                      ·
                        rfl

theorem cell23_4737996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4737996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737996 prefixEnd_4737996 := by exact prefixLift 4737996
  have htrace : WordTrace (prefixWord ++ tailWord_4737996) baseStart_4737996 baseEnd_4737996 := by
    simpa [prefixWord, tailWord_4737996, baseEnd_4737996] using wordTrace_append hprefix tailTrace_4737996
  have hstable : (prefixWord ++ tailWord_4737996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737996).length < 2 ^ (prefixWord ++ tailWord_4737996).sum := by decide
  have hdescent : baseEnd_4737996 < baseStart_4737996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738013 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4738013 : Nat := 118140960795 + 4738013 * 2 ^ 59
def prefixEnd_4738013 : Nat := 4983230072969 + 3 ^ 40 * 4738013 * 2
def baseEnd_4738013 : Nat := 2432878016251076236047781

theorem tailTrace_4738013 : CollatzResearch.WordTrace tailWord_4738013 prefixEnd_4738013 2432878016251076236047781 := by
  unfold tailWord_4738013
  simp only [CollatzResearch.WordTrace]
  refine ⟨172809530983995564042746693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115206353989330376028497795 172809530983995564042746693)
  ·
    refine ⟨32401787059499168258015005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172809530983995564042746693 32401787059499168258015005)
    ·
      refine ⟨12150670147312188096755627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32401787059499168258015005 12150670147312188096755627)
      ·
        refine ⟨18226005220968282145133441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12150670147312188096755627 18226005220968282145133441)
        ·
          refine ⟨13669503915726211608850081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18226005220968282145133441 13669503915726211608850081)
          ·
            refine ⟨10252127936794658706637561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13669503915726211608850081 10252127936794658706637561)
            ·
              refine ⟨7689095952595994029978171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10252127936794658706637561 7689095952595994029978171)
              ·
                refine ⟨11533643928893991044967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689095952595994029978171 11533643928893991044967257)
                ·
                  refine ⟨8650232946670493283725443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11533643928893991044967257 8650232946670493283725443)
                  ·
                    refine ⟨12975349420005739925588165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8650232946670493283725443 12975349420005739925588165)
                    ·
                      refine ⟨2432878016251076236047781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12975349420005739925588165 2432878016251076236047781)
                      ·
                        rfl

theorem cell23_4738013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4738013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738013 prefixEnd_4738013 := by exact prefixLift 4738013
  have htrace : WordTrace (prefixWord ++ tailWord_4738013) baseStart_4738013 baseEnd_4738013 := by
    simpa [prefixWord, tailWord_4738013, baseEnd_4738013] using wordTrace_append hprefix tailTrace_4738013
  have hstable : (prefixWord ++ tailWord_4738013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738013).length < 2 ^ (prefixWord ++ tailWord_4738013).sum := by decide
  have hdescent : baseEnd_4738013 < baseStart_4738013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738073 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 2, 3, 2]
def baseStart_4738073 : Nat := 118140960795 + 4738073 * 2 ^ 59
def prefixEnd_4738073 : Nat := 4983230072969 + 3 ^ 40 * 4738073 * 2
def baseEnd_4738073 : Nat := 2432908825090346001297505

theorem tailTrace_4738073 : CollatzResearch.WordTrace tailWord_4738073 prefixEnd_4738073 2432908825090346001297505 := by
  unfold tailWord_4738073
  simp only [CollatzResearch.WordTrace]
  refine ⟨172811719363778194289930873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115207812909185462859953915 172811719363778194289930873)
  ·
    refine ⟨129608789522833645717448155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172811719363778194289930873 129608789522833645717448155)
    ·
      refine ⟨194413184284250468576172233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129608789522833645717448155 194413184284250468576172233)
      ·
        refine ⟨145809888213187851432129175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194413184284250468576172233 145809888213187851432129175)
        ·
          refine ⟨218714832319781777148193763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145809888213187851432129175 218714832319781777148193763)
          ·
            refine ⟨328072248479672665722290645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218714832319781777148193763 328072248479672665722290645)
            ·
              refine ⟨7689193323742328102866187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 328072248479672665722290645 7689193323742328102866187)
              ·
                refine ⟨11533789985613492154299281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689193323742328102866187 11533789985613492154299281)
                ·
                  refine ⟨8650342489210119115724461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11533789985613492154299281 8650342489210119115724461)
                  ·
                    refine ⟨3243878433453794668396673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8650342489210119115724461 3243878433453794668396673)
                    ·
                      refine ⟨2432908825090346001297505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243878433453794668396673 2432908825090346001297505)
                      ·
                        rfl

theorem cell23_4738073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_4738073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738073 prefixEnd_4738073 := by exact prefixLift 4738073
  have htrace : WordTrace (prefixWord ++ tailWord_4738073) baseStart_4738073 baseEnd_4738073 := by
    simpa [prefixWord, tailWord_4738073, baseEnd_4738073] using wordTrace_append hprefix tailTrace_4738073
  have hstable : (prefixWord ++ tailWord_4738073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738073).length < 2 ^ (prefixWord ++ tailWord_4738073).sum := by decide
  have hdescent : baseEnd_4738073 < baseStart_4738073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738083 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 1, 5]
def baseStart_4738083 : Nat := 118140960795 + 4738083 * 2 ^ 59
def prefixEnd_4738083 : Nat := 4983230072969 + 3 ^ 40 * 4738083 * 2
def baseEnd_4738083 : Nat := 810971319965630320724153

theorem tailTrace_4738083 : CollatzResearch.WordTrace tailWord_4738083 prefixEnd_4738083 810971319965630320724153 := by
  unfold tailWord_4738083
  simp only [CollatzResearch.WordTrace]
  refine ⟨172812084093741965997794903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115208056062494643998529935 172812084093741965997794903)
  ·
    refine ⟨259218126140612948996692355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172812084093741965997794903 259218126140612948996692355)
    ·
      refine ⟨388827189210919423495038533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259218126140612948996692355 388827189210919423495038533)
      ·
        refine ⟨72905097977047391905319725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388827189210919423495038533 72905097977047391905319725)
        ·
          refine ⟨27339411741392771964494897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72905097977047391905319725 27339411741392771964494897)
          ·
            refine ⟨20504558806044578973371173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27339411741392771964494897 20504558806044578973371173)
            ·
              refine ⟨3844604776133358557507095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20504558806044578973371173 3844604776133358557507095)
              ·
                refine ⟨5766907164200037836260643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844604776133358557507095 5766907164200037836260643)
                ·
                  refine ⟨8650360746300056754390965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766907164200037836260643 8650360746300056754390965)
                  ·
                    refine ⟨810971319965630320724153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8650360746300056754390965 810971319965630320724153)
                    ·
                      rfl

theorem cell23_4738083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 5].length) (baseStart_4738083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738083 prefixEnd_4738083 := by exact prefixLift 4738083
  have htrace : WordTrace (prefixWord ++ tailWord_4738083) baseStart_4738083 baseEnd_4738083 := by
    simpa [prefixWord, tailWord_4738083, baseEnd_4738083] using wordTrace_append hprefix tailTrace_4738083
  have hstable : (prefixWord ++ tailWord_4738083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738083).length < 2 ^ (prefixWord ++ tailWord_4738083).sum := by decide
  have hdescent : baseEnd_4738083 < baseStart_4738083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738096 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_4738096 : Nat := 118140960795 + 4738096 * 2 ^ 59
def prefixEnd_4738096 : Nat := 4983230072969 + 3 ^ 40 * 4738096 * 2
def baseEnd_4738096 : Nat := 810973545048466470436633

theorem tailTrace_4738096 : CollatzResearch.WordTrace tailWord_4738096 prefixEnd_4738096 810973545048466470436633 := by
  unfold tailWord_4738096
  simp only [CollatzResearch.WordTrace]
  refine ⟨86406279121347434609009071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115208372161796579478678761 86406279121347434609009071)
  ·
    refine ⟨129609418682021151913513607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86406279121347434609009071 129609418682021151913513607)
    ·
      refine ⟨194414128023031727870270411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129609418682021151913513607 194414128023031727870270411)
      ·
        refine ⟨291621192034547591805405617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194414128023031727870270411 291621192034547591805405617)
        ·
          refine ⟨218715894025910693854054213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291621192034547591805405617 218715894025910693854054213)
          ·
            refine ⟨41009230129858255097635165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218715894025910693854054213 41009230129858255097635165)
            ·
              refine ⟨15378461298696845661613187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41009230129858255097635165 15378461298696845661613187)
              ·
                refine ⟨23067691948045268492419781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15378461298696845661613187 23067691948045268492419781)
                ·
                  refine ⟨4325192240258487842328709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23067691948045268492419781 4325192240258487842328709)
                  ·
                    refine ⟨810973545048466470436633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325192240258487842328709 810973545048466470436633)
                    ·
                      rfl

theorem cell23_4738096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_4738096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738096 prefixEnd_4738096 := by exact prefixLift 4738096
  have htrace : WordTrace (prefixWord ++ tailWord_4738096) baseStart_4738096 baseEnd_4738096 := by
    simpa [prefixWord, tailWord_4738096, baseEnd_4738096] using wordTrace_append hprefix tailTrace_4738096
  have hstable : (prefixWord ++ tailWord_4738096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738096).length < 2 ^ (prefixWord ++ tailWord_4738096).sum := by decide
  have hdescent : baseEnd_4738096 < baseStart_4738096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738099 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_4738099 : Nat := 118140960795 + 4738099 * 2 ^ 59
def prefixEnd_4738099 : Nat := 4983230072969 + 3 ^ 40 * 4738099 * 2
def baseEnd_4738099 : Nat := 2432922175587362899572385

theorem tailTrace_4738099 : CollatzResearch.WordTrace tailWord_4738099 prefixEnd_4738099 2432922175587362899572385 := by
  unfold tailWord_4738099
  simp only [CollatzResearch.WordTrace]
  refine ⟨172812667661684000730377351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115208445107789333820251567 172812667661684000730377351)
  ·
    refine ⟨259219001492526001095566027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172812667661684000730377351 259219001492526001095566027)
    ·
      refine ⟨388828502238789001643349041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259219001492526001095566027 388828502238789001643349041)
      ·
        refine ⟨291621376679091751232511781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388828502238789001643349041 291621376679091751232511781)
        ·
          refine ⟨54679008127329703356095959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291621376679091751232511781 54679008127329703356095959)
          ·
            refine ⟨82018512190994555034143939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54679008127329703356095959 82018512190994555034143939)
            ·
              refine ⟨123027768286491832551215909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82018512190994555034143939 123027768286491832551215909)
              ·
                refine ⟨23067706553717218603352983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123027768286491832551215909 23067706553717218603352983)
                ·
                  refine ⟨34601559830575827905029475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23067706553717218603352983 34601559830575827905029475)
                  ·
                    refine ⟨51902339745863741857544213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34601559830575827905029475 51902339745863741857544213)
                    ·
                      refine ⟨2432922175587362899572385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51902339745863741857544213 2432922175587362899572385)
                      ·
                        rfl

theorem cell23_4738099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_4738099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738099 prefixEnd_4738099 := by exact prefixLift 4738099
  have htrace : WordTrace (prefixWord ++ tailWord_4738099) baseStart_4738099 baseEnd_4738099 := by
    simpa [prefixWord, tailWord_4738099, baseEnd_4738099] using wordTrace_append hprefix tailTrace_4738099
  have hstable : (prefixWord ++ tailWord_4738099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738099).length < 2 ^ (prefixWord ++ tailWord_4738099).sum := by decide
  have hdescent : baseEnd_4738099 < baseStart_4738099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738106 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_4738106 : Nat := 118140960795 + 4738106 * 2 ^ 59
def prefixEnd_4738106 : Nat := 4983230072969 + 3 ^ 40 * 4738106 * 2
def baseEnd_4738106 : Nat := 2432925769951944372184853

theorem tailTrace_4738106 : CollatzResearch.WordTrace tailWord_4738106 prefixEnd_4738106 2432925769951944372184853 := by
  unfold tailWord_4738106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43203230743164660231470543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115208615315105760617254781 43203230743164660231470543)
  ·
    refine ⟨64804846114746990347205815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43203230743164660231470543 64804846114746990347205815)
    ·
      refine ⟨97207269172120485520808723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64804846114746990347205815 97207269172120485520808723)
      ·
        refine ⟨145810903758180728281213085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97207269172120485520808723 145810903758180728281213085)
        ·
          refine ⟨54679088909317773105454907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145810903758180728281213085 54679088909317773105454907)
          ·
            refine ⟨82018633363976659658182361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54679088909317773105454907 82018633363976659658182361)
            ·
              refine ⟨61513975022982494743636771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82018633363976659658182361 61513975022982494743636771)
              ·
                refine ⟨92270962534473742115455157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61513975022982494743636771 92270962534473742115455157)
                ·
                  refine ⟨8650402737606913323323921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92270962534473742115455157 8650402737606913323323921)
                  ·
                    refine ⟨6487802053205184992492941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8650402737606913323323921 6487802053205184992492941)
                    ·
                      refine ⟨2432925769951944372184853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487802053205184992492941 2432925769951944372184853)
                      ·
                        rfl

theorem cell23_4738106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_4738106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738106 prefixEnd_4738106 := by exact prefixLift 4738106
  have htrace : WordTrace (prefixWord ++ tailWord_4738106) baseStart_4738106 baseEnd_4738106 := by
    simpa [prefixWord, tailWord_4738106, baseEnd_4738106] using wordTrace_append hprefix tailTrace_4738106
  have hstable : (prefixWord ++ tailWord_4738106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738106).length < 2 ^ (prefixWord ++ tailWord_4738106).sum := by decide
  have hdescent : baseEnd_4738106 < baseStart_4738106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
