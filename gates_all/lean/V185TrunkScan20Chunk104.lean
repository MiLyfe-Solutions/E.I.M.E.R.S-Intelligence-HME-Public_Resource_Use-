import V185TrunkScan20Chunk103

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_632222 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_632222 : Nat := 118140960795 + 632222 * 2 ^ 59
def prefixEnd_632222 : Nat := 4983230072969 + 3 ^ 40 * 632222 * 2
def baseEnd_632222 : Nat := 288563347863938366415529

theorem tailTrace_632222 : CollatzResearch.WordTrace tailWord_632222 prefixEnd_632222 288563347863938366415529 := by
  unfold tailWord_632222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882378839446892970798365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15372687143716762510924613 2882378839446892970798365)
  ·
    refine ⟨1080892064792584864049387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2882378839446892970798365 1080892064792584864049387)
    ·
      refine ⟨1621338097188877296074081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080892064792584864049387 1621338097188877296074081)
      ·
        refine ⟨1216003572891657972055561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621338097188877296074081 1216003572891657972055561)
        ·
          refine ⟨912002679668743479041671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216003572891657972055561 912002679668743479041671)
          ·
            refine ⟨1368004019503115218562507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912002679668743479041671 1368004019503115218562507)
            ·
              refine ⟨2052006029254672827843761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368004019503115218562507 2052006029254672827843761)
              ·
                refine ⟨1539004521941004620882821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052006029254672827843761 1539004521941004620882821)
                ·
                  refine ⟨288563347863938366415529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539004521941004620882821 288563347863938366415529)
                  ·
                    rfl

theorem cell20_632222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_632222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632222 prefixEnd_632222 := by exact prefixLift 632222
  have htrace : WordTrace (prefixWord ++ tailWord_632222) baseStart_632222 baseEnd_632222 := by
    simpa [prefixWord, tailWord_632222, baseEnd_632222] using wordTrace_append hprefix tailTrace_632222
  have hstable : (prefixWord ++ tailWord_632222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632222).length < 2 ^ (prefixWord ++ tailWord_632222).sum := by decide
  have hdescent : baseEnd_632222 < baseStart_632222 := by decide
  rcases family_descends (prefixWord ++ tailWord_632222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632226 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_632226 : Nat := 118140960795 + 632226 * 2 ^ 59
def prefixEnd_632226 : Nat := 4983230072969 + 3 ^ 40 * 632226 * 2
def baseEnd_632226 : Nat := 288565173572932130282179

theorem tailTrace_632226 : CollatzResearch.WordTrace tailWord_632226 prefixEnd_632226 288565173572932130282179 := by
  unfold tailWord_632226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5764794151890163112383133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15372784405040434966355021 5764794151890163112383133)
  ·
    refine ⟨2161797806958811167143675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5764794151890163112383133 2161797806958811167143675)
    ·
      refine ⟨3242696710438216750715513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161797806958811167143675 3242696710438216750715513)
      ·
        refine ⟨2432022532828662563036635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242696710438216750715513 2432022532828662563036635)
        ·
          refine ⟨3648033799242993844554953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432022532828662563036635 3648033799242993844554953)
          ·
            refine ⟨2736025349432245383416215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648033799242993844554953 2736025349432245383416215)
            ·
              refine ⟨4104038024148368075124323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736025349432245383416215 4104038024148368075124323)
              ·
                refine ⟨6156057036222552112686485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104038024148368075124323 6156057036222552112686485)
                ·
                  refine ⟨288565173572932130282179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6156057036222552112686485 288565173572932130282179)
                  ·
                    rfl

theorem cell20_632226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_632226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632226 prefixEnd_632226 := by exact prefixLift 632226
  have htrace : WordTrace (prefixWord ++ tailWord_632226) baseStart_632226 baseEnd_632226 := by
    simpa [prefixWord, tailWord_632226, baseEnd_632226] using wordTrace_append hprefix tailTrace_632226
  have hstable : (prefixWord ++ tailWord_632226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632226).length < 2 ^ (prefixWord ++ tailWord_632226).sum := by decide
  have hdescent : baseEnd_632226 < baseStart_632226 := by decide
  rcases family_descends (prefixWord ++ tailWord_632226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632247 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_632247 : Nat := 118140960795 + 632247 * 2 ^ 59
def prefixEnd_632247 : Nat := 4983230072969 + 3 ^ 40 * 632247 * 2
def baseEnd_632247 : Nat := 288574758545149390582093

theorem tailTrace_632247 : CollatzResearch.WordTrace tailWord_632247 prefixEnd_632247 288574758545149390582093 := by
  unfold tailWord_632247
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059942540484573036046995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15373295026989715357364663 23059942540484573036046995)
  ·
    refine ⟨34589913810726859554070493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23059942540484573036046995 34589913810726859554070493)
    ·
      refine ⟨12971217679022572332776435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34589913810726859554070493 12971217679022572332776435)
      ·
        refine ⟨19456826518533858499164653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12971217679022572332776435 19456826518533858499164653)
        ·
          refine ⟨7296309944450196937186745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19456826518533858499164653 7296309944450196937186745)
          ·
            refine ⟨5472232458337647702890059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7296309944450196937186745 5472232458337647702890059)
            ·
              refine ⟨8208348687506471554335089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472232458337647702890059 8208348687506471554335089)
              ·
                refine ⟨6156261515629853665751317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8208348687506471554335089 6156261515629853665751317)
                ·
                  refine ⟨288574758545149390582093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6156261515629853665751317 288574758545149390582093)
                  ·
                    rfl

theorem cell20_632247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_632247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632247 prefixEnd_632247 := by exact prefixLift 632247
  have htrace : WordTrace (prefixWord ++ tailWord_632247) baseStart_632247 baseEnd_632247 := by
    simpa [prefixWord, tailWord_632247, baseEnd_632247] using wordTrace_append hprefix tailTrace_632247
  have hstable : (prefixWord ++ tailWord_632247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632247).length < 2 ^ (prefixWord ++ tailWord_632247).sum := by decide
  have hdescent : baseEnd_632247 < baseStart_632247 := by decide
  rcases family_descends (prefixWord ++ tailWord_632247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632260 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_632260 : Nat := 118140960795 + 632260 * 2 ^ 59
def prefixEnd_632260 : Nat := 4983230072969 + 3 ^ 40 * 632260 * 2
def baseEnd_632260 : Nat := 288580692099379123148707

theorem tailTrace_632260 : CollatzResearch.WordTrace tailWord_632260 prefixEnd_632260 288580692099379123148707 := by
  unfold tailWord_632260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530208344718738128135117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15373611126291650837513489 11530208344718738128135117)
  ·
    refine ⟨4323828129269526798050669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11530208344718738128135117 4323828129269526798050669)
    ·
      refine ⟨1621435548476072549269001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4323828129269526798050669 1621435548476072549269001)
      ·
        refine ⟨1216076661357054411951751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621435548476072549269001 1216076661357054411951751)
        ·
          refine ⟨1824114992035581617927627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216076661357054411951751 1824114992035581617927627)
          ·
            refine ⟨2736172488053372426891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824114992035581617927627 2736172488053372426891441)
            ·
              refine ⟨2052129366040029320168581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736172488053372426891441 2052129366040029320168581)
              ·
                refine ⟨384774256132505497531609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2052129366040029320168581 384774256132505497531609)
                ·
                  refine ⟨288580692099379123148707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384774256132505497531609 288580692099379123148707)
                  ·
                    rfl

theorem cell20_632260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_632260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632260 prefixEnd_632260 := by exact prefixLift 632260
  have htrace : WordTrace (prefixWord ++ tailWord_632260) baseStart_632260 baseEnd_632260 := by
    simpa [prefixWord, tailWord_632260, baseEnd_632260] using wordTrace_append hprefix tailTrace_632260
  have hstable : (prefixWord ++ tailWord_632260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632260).length < 2 ^ (prefixWord ++ tailWord_632260).sum := by decide
  have hdescent : baseEnd_632260 < baseStart_632260 := by decide
  rcases family_descends (prefixWord ++ tailWord_632260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632264 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_632264 : Nat := 118140960795 + 632264 * 2 ^ 59
def prefixEnd_632264 : Nat := 4983230072969 + 3 ^ 40 * 632264 * 2
def baseEnd_632264 : Nat := 288582517808372887015357

theorem tailTrace_632264 : CollatzResearch.WordTrace tailWord_632264 prefixEnd_632264 288582517808372887015357 := by
  unfold tailWord_632264
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530281290711492469707923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15373708387615323292943897 11530281290711492469707923)
  ·
    refine ⟨17295421936067238704561885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11530281290711492469707923 17295421936067238704561885)
    ·
      refine ⟨6485783226025214514210707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17295421936067238704561885 6485783226025214514210707)
      ·
        refine ⟨9728674839037821771316061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485783226025214514210707 9728674839037821771316061)
        ·
          refine ⟨3648253064639183164243523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9728674839037821771316061 3648253064639183164243523)
          ·
            refine ⟨5472379596958774746365285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648253064639183164243523 5472379596958774746365285)
            ·
              refine ⟨1026071174429770264943491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5472379596958774746365285 1026071174429770264943491)
              ·
                refine ⟨1539106761644655397415237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026071174429770264943491 1539106761644655397415237)
                ·
                  refine ⟨288582517808372887015357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539106761644655397415237 288582517808372887015357)
                  ·
                    rfl

theorem cell20_632264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_632264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632264 prefixEnd_632264 := by exact prefixLift 632264
  have htrace : WordTrace (prefixWord ++ tailWord_632264) baseStart_632264 baseEnd_632264 := by
    simpa [prefixWord, tailWord_632264, baseEnd_632264] using wordTrace_append hprefix tailTrace_632264
  have hstable : (prefixWord ++ tailWord_632264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632264).length < 2 ^ (prefixWord ++ tailWord_632264).sum := by decide
  have hdescent : baseEnd_632264 < baseStart_632264 := by decide
  rcases family_descends (prefixWord ++ tailWord_632264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632316 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_632316 : Nat := 118140960795 + 632316 * 2 ^ 59
def prefixEnd_632316 : Nat := 4983230072969 + 3 ^ 40 * 632316 * 2
def baseEnd_632316 : Nat := 288606252025291817281811

theorem tailTrace_632316 : CollatzResearch.WordTrace tailWord_632316 prefixEnd_632316 288606252025291817281811 := by
  unfold tailWord_632316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11531229588617298910154401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15374972784823065213539201 11531229588617298910154401)
  ·
    refine ⟨8648422191462974182615801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11531229588617298910154401 8648422191462974182615801)
    ·
      refine ⟨6486316643597230636961851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8648422191462974182615801 6486316643597230636961851)
      ·
        refine ⟨9729474965395845955442777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486316643597230636961851 9729474965395845955442777)
        ·
          refine ⟨7297106224046884466582083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9729474965395845955442777 7297106224046884466582083)
          ·
            refine ⟨10945659336070326699873125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297106224046884466582083 10945659336070326699873125)
            ·
              refine ⟨2052311125513186256226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10945659336070326699873125 2052311125513186256226211)
              ·
                refine ⟨3078466688269779384339317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052311125513186256226211 3078466688269779384339317)
                ·
                  refine ⟨288606252025291817281811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3078466688269779384339317 288606252025291817281811)
                  ·
                    rfl

theorem cell20_632316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_632316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632316 prefixEnd_632316 := by exact prefixLift 632316
  have htrace : WordTrace (prefixWord ++ tailWord_632316) baseStart_632316 baseEnd_632316 := by
    simpa [prefixWord, tailWord_632316, baseEnd_632316] using wordTrace_append hprefix tailTrace_632316
  have hstable : (prefixWord ++ tailWord_632316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632316).length < 2 ^ (prefixWord ++ tailWord_632316).sum := by decide
  have hdescent : baseEnd_632316 < baseStart_632316 := by decide
  rcases family_descends (prefixWord ++ tailWord_632316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632323 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_632323 : Nat := 118140960795 + 632323 * 2 ^ 59
def prefixEnd_632323 : Nat := 4983230072969 + 3 ^ 40 * 632323 * 2
def baseEnd_632323 : Nat := 288609447016030904048449

theorem tailTrace_632323 : CollatzResearch.WordTrace tailWord_632323 prefixEnd_632323 288609447016030904048449 := by
  unfold tailWord_632323
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062714488209238015813623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15375142992139492010542415 23062714488209238015813623)
  ·
    refine ⟨34594071732313857023720435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23062714488209238015813623 34594071732313857023720435)
    ·
      refine ⟨51891107598470785535580653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34594071732313857023720435 51891107598470785535580653)
      ·
        refine ⟨19459165349426544575842745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51891107598470785535580653 19459165349426544575842745)
        ·
          refine ⟨14594374012069908431882059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19459165349426544575842745 14594374012069908431882059)
          ·
            refine ⟨21891561018104862647823089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14594374012069908431882059 21891561018104862647823089)
            ·
              refine ⟨16418670763578646985867317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21891561018104862647823089 16418670763578646985867317)
              ·
                refine ⟨1539250384085498154925061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16418670763578646985867317 1539250384085498154925061)
                ·
                  refine ⟨288609447016030904048449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539250384085498154925061 288609447016030904048449)
                  ·
                    rfl

theorem cell20_632323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_632323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632323 prefixEnd_632323 := by exact prefixLift 632323
  have htrace : WordTrace (prefixWord ++ tailWord_632323) baseStart_632323 baseEnd_632323 := by
    simpa [prefixWord, tailWord_632323, baseEnd_632323] using wordTrace_append hprefix tailTrace_632323
  have hstable : (prefixWord ++ tailWord_632323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632323).length < 2 ^ (prefixWord ++ tailWord_632323).sum := by decide
  have hdescent : baseEnd_632323 < baseStart_632323 := by decide
  rcases family_descends (prefixWord ++ tailWord_632323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632354 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_632354 : Nat := 118140960795 + 632354 * 2 ^ 59
def prefixEnd_632354 : Nat := 4983230072969 + 3 ^ 40 * 632354 * 2
def baseEnd_632354 : Nat := 288623596260732574014989

theorem tailTrace_632354 : CollatzResearch.WordTrace tailWord_632354 prefixEnd_632354 288623596260732574014989 := by
  unfold tailWord_632354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765961287774232577548029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15375896767397953540128077 5765961287774232577548029)
  ·
    refine ⟨2162235482915337216580511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5765961287774232577548029 2162235482915337216580511)
    ·
      refine ⟨3243353224373005824870767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162235482915337216580511 3243353224373005824870767)
      ·
        refine ⟨4865029836559508737306151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243353224373005824870767 4865029836559508737306151)
        ·
          refine ⟨7297544754839263105959227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865029836559508737306151 7297544754839263105959227)
          ·
            refine ⟨10946317132258894658938841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297544754839263105959227 10946317132258894658938841)
            ·
              refine ⟨8209737849194170994204131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10946317132258894658938841 8209737849194170994204131)
              ·
                refine ⟨12314606773791256491306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209737849194170994204131 12314606773791256491306197)
                ·
                  refine ⟨288623596260732574014989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12314606773791256491306197 288623596260732574014989)
                  ·
                    rfl

theorem cell20_632354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_632354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632354 prefixEnd_632354 := by exact prefixLift 632354
  have htrace : WordTrace (prefixWord ++ tailWord_632354) baseStart_632354 baseEnd_632354 := by
    simpa [prefixWord, tailWord_632354, baseEnd_632354] using wordTrace_append hprefix tailTrace_632354
  have hstable : (prefixWord ++ tailWord_632354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632354).length < 2 ^ (prefixWord ++ tailWord_632354).sum := by decide
  have hdescent : baseEnd_632354 < baseStart_632354 := by decide
  rcases family_descends (prefixWord ++ tailWord_632354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632371 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_632371 : Nat := 118140960795 + 632371 * 2 ^ 59
def prefixEnd_632371 : Nat := 4983230072969 + 3 ^ 40 * 632371 * 2
def baseEnd_632371 : Nat := 288631355523956070448253

theorem tailTrace_632371 : CollatzResearch.WordTrace tailWord_632371 prefixEnd_632371 288631355523956070448253 := by
  unfold tailWord_632371
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064465192035342213560967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15376310128023561475707311 23064465192035342213560967)
  ·
    refine ⟨34596697788053013320341451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23064465192035342213560967 34596697788053013320341451)
    ·
      refine ⟨51895046682079519980512177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34596697788053013320341451 51895046682079519980512177)
      ·
        refine ⟨38921285011559639985384133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51895046682079519980512177 38921285011559639985384133)
        ·
          refine ⟨7297740939667432497259525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38921285011559639985384133 7297740939667432497259525)
          ·
            refine ⟨1368326426187643593236161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7297740939667432497259525 1368326426187643593236161)
            ·
              refine ⟨1026244819640732694927121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368326426187643593236161 1026244819640732694927121)
              ·
                refine ⟨769683614730549521195341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026244819640732694927121 769683614730549521195341)
                ·
                  refine ⟨288631355523956070448253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769683614730549521195341 288631355523956070448253)
                  ·
                    rfl

theorem cell20_632371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_632371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632371 prefixEnd_632371 := by exact prefixLift 632371
  have htrace : WordTrace (prefixWord ++ tailWord_632371) baseStart_632371 baseEnd_632371 := by
    simpa [prefixWord, tailWord_632371, baseEnd_632371] using wordTrace_append hprefix tailTrace_632371
  have hstable : (prefixWord ++ tailWord_632371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632371).length < 2 ^ (prefixWord ++ tailWord_632371).sum := by decide
  have hdescent : baseEnd_632371 < baseStart_632371 := by decide
  rcases family_descends (prefixWord ++ tailWord_632371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632381 : List Nat := [1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_632381 : Nat := 118140960795 + 632381 * 2 ^ 59
def prefixEnd_632381 : Nat := 4983230072969 + 3 ^ 40 * 632381 * 2
def baseEnd_632381 : Nat := 96211973265480160038293

theorem tailTrace_632381 : CollatzResearch.WordTrace tailWord_632381 prefixEnd_632381 96211973265480160038293 := by
  unfold tailWord_632381
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064829921999113921424997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15376553281332742614283331 23064829921999113921424997)
  ·
    refine ⟨4324655610374833860267187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23064829921999113921424997 4324655610374833860267187)
    ·
      refine ⟨6486983415562250790400781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324655610374833860267187 6486983415562250790400781)
      ·
        refine ⟨2432618780835844046400293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6486983415562250790400781 2432618780835844046400293)
        ·
          refine ⟨456116021406720758700055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2432618780835844046400293 456116021406720758700055)
          ·
            refine ⟨684174032110081138050083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456116021406720758700055 684174032110081138050083)
            ·
              refine ⟨1026261048165121707075125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684174032110081138050083 1026261048165121707075125)
              ·
                refine ⟨96211973265480160038293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1026261048165121707075125 96211973265480160038293)
                ·
                  rfl

theorem cell20_632381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_632381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632381 prefixEnd_632381 := by exact prefixLift 632381
  have htrace : WordTrace (prefixWord ++ tailWord_632381) baseStart_632381 baseEnd_632381 := by
    simpa [prefixWord, tailWord_632381, baseEnd_632381] using wordTrace_append hprefix tailTrace_632381
  have hstable : (prefixWord ++ tailWord_632381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632381).length < 2 ^ (prefixWord ++ tailWord_632381).sum := by decide
  have hdescent : baseEnd_632381 < baseStart_632381 := by decide
  rcases family_descends (prefixWord ++ tailWord_632381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632402 : List Nat := [3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_632402 : Nat := 118140960795 + 632402 * 2 ^ 59
def prefixEnd_632402 : Nat := 4983230072969 + 3 ^ 40 * 632402 * 2
def baseEnd_632402 : Nat := 96215168256219246804931

theorem tailTrace_632402 : CollatzResearch.WordTrace tailWord_632402 prefixEnd_632402 96215168256219246804931 := by
  unfold tailWord_632402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766398963730758626984865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15377063903282023005292973 5766398963730758626984865)
  ·
    refine ⟨4324799222798068970238649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766398963730758626984865 4324799222798068970238649)
    ·
      refine ⟨3243599417098551727678987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4324799222798068970238649 3243599417098551727678987)
      ·
        refine ⟨4865399125647827591518481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243599417098551727678987 4865399125647827591518481)
        ·
          refine ⟨3649049344235870693638861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865399125647827591518481 3649049344235870693638861)
          ·
            refine ⟨1368393504088451510114573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3649049344235870693638861 1368393504088451510114573)
            ·
              refine ⟨513147564033169316292965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368393504088451510114573 513147564033169316292965)
              ·
                refine ⟨96215168256219246804931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513147564033169316292965 96215168256219246804931)
                ·
                  rfl

theorem cell20_632402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_632402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632402 prefixEnd_632402 := by exact prefixLift 632402
  have htrace : WordTrace (prefixWord ++ tailWord_632402) baseStart_632402 baseEnd_632402 := by
    simpa [prefixWord, tailWord_632402, baseEnd_632402] using wordTrace_append hprefix tailTrace_632402
  have hstable : (prefixWord ++ tailWord_632402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632402).length < 2 ^ (prefixWord ++ tailWord_632402).sum := by decide
  have hdescent : baseEnd_632402 < baseStart_632402 := by decide
  rcases family_descends (prefixWord ++ tailWord_632402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632412 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_632412 : Nat := 118140960795 + 632412 * 2 ^ 59
def prefixEnd_632412 : Nat := 4983230072969 + 3 ^ 40 * 632412 * 2
def baseEnd_632412 : Nat := 288650069041142150081419

theorem tailTrace_632412 : CollatzResearch.WordTrace tailWord_632412 prefixEnd_632412 288650069041142150081419 := by
  unfold tailWord_632412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11532980292443403107901745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15377307056591204143868993 11532980292443403107901745)
  ·
    refine ⟨8649735219332552330926309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11532980292443403107901745 8649735219332552330926309)
    ·
      refine ⟨1621825353624853562048683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8649735219332552330926309 1621825353624853562048683)
      ·
        refine ⟨2432738030437280343073025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621825353624853562048683 2432738030437280343073025)
        ·
          refine ⟨1824553522827960257304769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432738030437280343073025 1824553522827960257304769)
          ·
            refine ⟨1368415142120970192978577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824553522827960257304769 1368415142120970192978577)
            ·
              refine ⟨1026311356590727644733933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368415142120970192978577 1026311356590727644733933)
              ·
                refine ⟨384866758721522866775225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026311356590727644733933 384866758721522866775225)
                ·
                  refine ⟨288650069041142150081419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384866758721522866775225 288650069041142150081419)
                  ·
                    rfl

theorem cell20_632412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_632412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632412 prefixEnd_632412 := by exact prefixLift 632412
  have htrace : WordTrace (prefixWord ++ tailWord_632412) baseStart_632412 baseEnd_632412 := by
    simpa [prefixWord, tailWord_632412, baseEnd_632412] using wordTrace_append hprefix tailTrace_632412
  have hstable : (prefixWord ++ tailWord_632412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632412).length < 2 ^ (prefixWord ++ tailWord_632412).sum := by decide
  have hdescent : baseEnd_632412 < baseStart_632412 := by decide
  rcases family_descends (prefixWord ++ tailWord_632412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632426 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_632426 : Nat := 118140960795 + 632426 * 2 ^ 59
def prefixEnd_632426 : Nat := 4983230072969 + 3 ^ 40 * 632426 * 2
def baseEnd_632426 : Nat := 288656459022620323614695

theorem tailTrace_632426 : CollatzResearch.WordTrace tailWord_632426 prefixEnd_632426 288656459022620323614695 := by
  unfold tailWord_632426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766617801709021651703283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15377647471224057737875421 5766617801709021651703283)
  ·
    refine ⟨8649926702563532477554925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766617801709021651703283 8649926702563532477554925)
    ·
      refine ⟨3243722513461324679083097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8649926702563532477554925 3243722513461324679083097)
      ·
        refine ⟨2432791885095993509312323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3243722513461324679083097 2432791885095993509312323)
        ·
          refine ⟨3649187827643990263968485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432791885095993509312323 3649187827643990263968485)
          ·
            refine ⟨684222717683248174494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3649187827643990263968485 684222717683248174494091)
            ·
              refine ⟨1026334076524872261741137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684222717683248174494091 1026334076524872261741137)
              ·
                refine ⟨769750557393654196305853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026334076524872261741137 769750557393654196305853)
                ·
                  refine ⟨288656459022620323614695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769750557393654196305853 288656459022620323614695)
                  ·
                    rfl

theorem cell20_632426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_632426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632426 prefixEnd_632426 := by exact prefixLift 632426
  have htrace : WordTrace (prefixWord ++ tailWord_632426) baseStart_632426 baseEnd_632426 := by
    simpa [prefixWord, tailWord_632426, baseEnd_632426] using wordTrace_append hprefix tailTrace_632426
  have hstable : (prefixWord ++ tailWord_632426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632426).length < 2 ^ (prefixWord ++ tailWord_632426).sum := by decide
  have hdescent : baseEnd_632426 < baseStart_632426 := by decide
  rcases family_descends (prefixWord ++ tailWord_632426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632444 : List Nat := [2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_632444 : Nat := 118140960795 + 632444 * 2 ^ 59
def prefixEnd_632444 : Nat := 4983230072969 + 3 ^ 40 * 632444 * 2
def baseEnd_632444 : Nat := 96221558237697420338207

theorem tailTrace_632444 : CollatzResearch.WordTrace tailWord_632444 prefixEnd_632444 96221558237697420338207 := by
  unfold tailWord_632444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533563860385437840484193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15378085147180583787312257 11533563860385437840484193)
  ·
    refine ⟨8650172895289078380363145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11533563860385437840484193 8650172895289078380363145)
    ·
      refine ⟨6487629671466808785272359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8650172895289078380363145 6487629671466808785272359)
      ·
        refine ⟨9731444507200213177908539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487629671466808785272359 9731444507200213177908539)
        ·
          refine ⟨14597166760800319766862809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731444507200213177908539 14597166760800319766862809)
          ·
            refine ⟨10947875070600239825147107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14597166760800319766862809 10947875070600239825147107)
            ·
              refine ⟨16421812605900359737720661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947875070600239825147107 16421812605900359737720661)
              ·
                refine ⟨96221558237697420338207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16421812605900359737720661 96221558237697420338207)
                ·
                  rfl

theorem cell20_632444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_632444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632444 prefixEnd_632444 := by exact prefixLift 632444
  have htrace : WordTrace (prefixWord ++ tailWord_632444) baseStart_632444 baseEnd_632444 := by
    simpa [prefixWord, tailWord_632444, baseEnd_632444] using wordTrace_append hprefix tailTrace_632444
  have hstable : (prefixWord ++ tailWord_632444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632444).length < 2 ^ (prefixWord ++ tailWord_632444).sum := by decide
  have hdescent : baseEnd_632444 < baseStart_632444 := by decide
  rcases family_descends (prefixWord ++ tailWord_632444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632471 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 2]
def baseStart_632471 : Nat := 118140960795 + 632471 * 2 ^ 59
def prefixEnd_632471 : Nat := 4983230072969 + 3 ^ 40 * 632471 * 2
def baseEnd_632471 : Nat := 288676998248800167114511

theorem tailTrace_632471 : CollatzResearch.WordTrace tailWord_632471 prefixEnd_632471 288676998248800167114511 := by
  unfold tailWord_632471
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068112491673059292201267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15378741661115372861467511 23068112491673059292201267)
  ·
    refine ⟨34602168737509588938301901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23068112491673059292201267 34602168737509588938301901)
    ·
      refine ⟨12975813276566095851863213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34602168737509588938301901 12975813276566095851863213)
      ·
        refine ⟨4865929978712285944448705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12975813276566095851863213 4865929978712285944448705)
        ·
          refine ⟨3649447484034214458336529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865929978712285944448705 3649447484034214458336529)
          ·
            refine ⟨2737085613025660843752397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649447484034214458336529 2737085613025660843752397)
            ·
              refine ⟨1026407104884622816407149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2737085613025660843752397 1026407104884622816407149)
              ·
                refine ⟨384902664331733556152681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026407104884622816407149 384902664331733556152681)
                ·
                  refine ⟨288676998248800167114511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384902664331733556152681 288676998248800167114511)
                  ·
                    rfl

theorem cell20_632471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2].length) (baseStart_632471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632471 prefixEnd_632471 := by exact prefixLift 632471
  have htrace : WordTrace (prefixWord ++ tailWord_632471) baseStart_632471 baseEnd_632471 := by
    simpa [prefixWord, tailWord_632471, baseEnd_632471] using wordTrace_append hprefix tailTrace_632471
  have hstable : (prefixWord ++ tailWord_632471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632471).length < 2 ^ (prefixWord ++ tailWord_632471).sum := by decide
  have hdescent : baseEnd_632471 < baseStart_632471 := by decide
  rcases family_descends (prefixWord ++ tailWord_632471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632478 : List Nat := [4, 3, 1, 1, 1, 4, 6]
def baseStart_632478 : Nat := 118140960795 + 632478 * 2 ^ 59
def prefixEnd_632478 : Nat := 4983230072969 + 3 ^ 40 * 632478 * 2
def baseEnd_632478 : Nat := 32075577026615472653461

theorem tailTrace_632478 : CollatzResearch.WordTrace tailWord_632478 prefixEnd_632478 32075577026615472653461 := by
  unfold tailWord_632478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883545975330962435963261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15378911868431799658470725 2883545975330962435963261)
  ·
    refine ⟨1081329740749110913486223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2883545975330962435963261 1081329740749110913486223)
    ·
      refine ⟨1621994611123666370229335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081329740749110913486223 1621994611123666370229335)
      ·
        refine ⟨2432991916685499555344003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621994611123666370229335 2432991916685499555344003)
        ·
          refine ⟨3649487875028249333016005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432991916685499555344003 3649487875028249333016005)
          ·
            refine ⟨684278976567796749940501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3649487875028249333016005 684278976567796749940501)
            ·
              refine ⟨32075577026615472653461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 684278976567796749940501 32075577026615472653461)
              ·
                rfl

theorem cell20_632478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_632478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632478 prefixEnd_632478 := by exact prefixLift 632478
  have htrace : WordTrace (prefixWord ++ tailWord_632478) baseStart_632478 baseEnd_632478 := by
    simpa [prefixWord, tailWord_632478, baseEnd_632478] using wordTrace_append hprefix tailTrace_632478
  have hstable : (prefixWord ++ tailWord_632478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632478).length < 2 ^ (prefixWord ++ tailWord_632478).sum := by decide
  have hdescent : baseEnd_632478 < baseStart_632478 := by decide
  rcases family_descends (prefixWord ++ tailWord_632478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_632489 : Nat := 118140960795 + 632489 * 2 ^ 59
def prefixEnd_632489 : Nat := 4983230072969 + 3 ^ 40 * 632489 * 2
def baseEnd_632489 : Nat := 288685213939272104514437

theorem tailTrace_632489 : CollatzResearch.WordTrace tailWord_632489 prefixEnd_632489 288685213939272104514437 := by
  unfold tailWord_632489
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068769005607848366356521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15379179337071898910904347 23068769005607848366356521)
  ·
    refine ⟨17301576754205886274767391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23068769005607848366356521 17301576754205886274767391)
    ·
      refine ⟨25952365131308829412151087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17301576754205886274767391 25952365131308829412151087)
      ·
        refine ⟨38928547696963244118226631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25952365131308829412151087 38928547696963244118226631)
        ·
          refine ⟨58392821545444866177339947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38928547696963244118226631 58392821545444866177339947)
          ·
            refine ⟨87589232318167299266009921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58392821545444866177339947 87589232318167299266009921)
            ·
              refine ⟨65691924238625474449507441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87589232318167299266009921 65691924238625474449507441)
              ·
                refine ⟨49268943178969105837130581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65691924238625474449507441 49268943178969105837130581)
                ·
                  refine ⟨288685213939272104514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49268943178969105837130581 288685213939272104514437)
                  ·
                    rfl

theorem cell20_632489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_632489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632489 prefixEnd_632489 := by exact prefixLift 632489
  have htrace : WordTrace (prefixWord ++ tailWord_632489) baseStart_632489 baseEnd_632489 := by
    simpa [prefixWord, tailWord_632489, baseEnd_632489] using wordTrace_append hprefix tailTrace_632489
  have hstable : (prefixWord ++ tailWord_632489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632489).length < 2 ^ (prefixWord ++ tailWord_632489).sum := by decide
  have hdescent : baseEnd_632489 < baseStart_632489 := by decide
  rcases family_descends (prefixWord ++ tailWord_632489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632520 : List Nat := [2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_632520 : Nat := 118140960795 + 632520 * 2 ^ 59
def prefixEnd_632520 : Nat := 4983230072969 + 3 ^ 40 * 632520 * 2
def baseEnd_632520 : Nat := 96233121061324591493659

theorem tailTrace_632520 : CollatzResearch.WordTrace tailWord_632520 prefixEnd_632520 96233121061324591493659 := by
  unfold tailWord_632520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534949834247770330367507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15379933112330360440490009 11534949834247770330367507)
  ·
    refine ⟨17302424751371655495551261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534949834247770330367507 17302424751371655495551261)
    ·
      refine ⟨6488409281764370810831723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17302424751371655495551261 6488409281764370810831723)
      ·
        refine ⟨9732613922646556216247585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488409281764370810831723 9732613922646556216247585)
        ·
          refine ⟨7299460441984917162185689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9732613922646556216247585 7299460441984917162185689)
          ·
            refine ⟨5474595331488687871639267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7299460441984917162185689 5474595331488687871639267)
            ·
              refine ⟨8211892997233031807458901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474595331488687871639267 8211892997233031807458901)
              ·
                refine ⟨96233121061324591493659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8211892997233031807458901 96233121061324591493659)
                ·
                  rfl

theorem cell20_632520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_632520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632520 prefixEnd_632520 := by exact prefixLift 632520
  have htrace : WordTrace (prefixWord ++ tailWord_632520) baseStart_632520 baseEnd_632520 := by
    simpa [prefixWord, tailWord_632520, baseEnd_632520] using wordTrace_append hprefix tailTrace_632520
  have hstable : (prefixWord ++ tailWord_632520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632520).length < 2 ^ (prefixWord ++ tailWord_632520).sum := by decide
  have hdescent : baseEnd_632520 < baseStart_632520 := by decide
  rcases family_descends (prefixWord ++ tailWord_632520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632527 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_632527 : Nat := 118140960795 + 632527 * 2 ^ 59
def prefixEnd_632527 : Nat := 4983230072969 + 3 ^ 40 * 632527 * 2
def baseEnd_632527 : Nat := 288702558174712861247615

theorem tailTrace_632527 : CollatzResearch.WordTrace tailWord_632527 prefixEnd_632527 288702558174712861247615 := by
  unfold tailWord_632527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070154979470180856239835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15380103319646787237493223 23070154979470180856239835)
  ·
    refine ⟨34605232469205271284359753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23070154979470180856239835 34605232469205271284359753)
    ·
      refine ⟨25953924351903953463269815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34605232469205271284359753 25953924351903953463269815)
      ·
        refine ⟨38930886527855930194904723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25953924351903953463269815 38930886527855930194904723)
        ·
          refine ⟨58396329791783895292357085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38930886527855930194904723 58396329791783895292357085)
          ·
            refine ⟨21898623671918960734633907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58396329791783895292357085 21898623671918960734633907)
            ·
              refine ⟨32847935507878441101950861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21898623671918960734633907 32847935507878441101950861)
              ·
                refine ⟨12317975815454415413231573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32847935507878441101950861 12317975815454415413231573)
                ·
                  refine ⟨288702558174712861247615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12317975815454415413231573 288702558174712861247615)
                  ·
                    rfl

theorem cell20_632527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_632527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632527 prefixEnd_632527 := by exact prefixLift 632527
  have htrace : WordTrace (prefixWord ++ tailWord_632527) baseStart_632527 baseEnd_632527 := by
    simpa [prefixWord, tailWord_632527, baseEnd_632527] using wordTrace_append hprefix tailTrace_632527
  have hstable : (prefixWord ++ tailWord_632527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632527).length < 2 ^ (prefixWord ++ tailWord_632527).sum := by decide
  have hdescent : baseEnd_632527 < baseStart_632527 := by decide
  rcases family_descends (prefixWord ++ tailWord_632527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632544 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_632544 : Nat := 118140960795 + 632544 * 2 ^ 59
def prefixEnd_632544 : Nat := 4983230072969 + 3 ^ 40 * 632544 * 2
def baseEnd_632544 : Nat := 288710317437936357680879

theorem tailTrace_632544 : CollatzResearch.WordTrace tailWord_632544 prefixEnd_632544 288710317437936357680879 := by
  unfold tailWord_632544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535387510204296379804343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15380516680272395173072457 11535387510204296379804343)
  ·
    refine ⟨17303081265306444569706515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11535387510204296379804343 17303081265306444569706515)
    ·
      refine ⟨25954621897959666854559773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17303081265306444569706515 25954621897959666854559773)
      ·
        refine ⟨9732983211734875070459915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25954621897959666854559773 9732983211734875070459915)
        ·
          refine ⟨14599474817602312605689873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732983211734875070459915 14599474817602312605689873)
          ·
            refine ⟨10949606113201734454267405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14599474817602312605689873 10949606113201734454267405)
            ·
              refine ⟨4106102292450650420350277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10949606113201734454267405 4106102292450650420350277)
              ·
                refine ⟨769894179834496953815677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4106102292450650420350277 769894179834496953815677)
                ·
                  refine ⟨288710317437936357680879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769894179834496953815677 288710317437936357680879)
                  ·
                    rfl

theorem cell20_632544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_632544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632544 prefixEnd_632544 := by exact prefixLift 632544
  have htrace : WordTrace (prefixWord ++ tailWord_632544) baseStart_632544 baseEnd_632544 := by
    simpa [prefixWord, tailWord_632544, baseEnd_632544] using wordTrace_append hprefix tailTrace_632544
  have hstable : (prefixWord ++ tailWord_632544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632544).length < 2 ^ (prefixWord ++ tailWord_632544).sum := by decide
  have hdescent : baseEnd_632544 < baseStart_632544 := by decide
  rcases family_descends (prefixWord ++ tailWord_632544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632564 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_632564 : Nat := 118140960795 + 632564 * 2 ^ 59
def prefixEnd_632564 : Nat := 4983230072969 + 3 ^ 40 * 632564 * 2
def baseEnd_632564 : Nat := 288719445982905177014131

theorem tailTrace_632564 : CollatzResearch.WordTrace tailWord_632564 prefixEnd_632564 288719445982905177014131 := by
  unfold tailWord_632564
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535752240168068087668373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15381002986890757450224497 11535752240168068087668373)
  ·
    refine ⟨540738386257878191609455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11535752240168068087668373 540738386257878191609455)
    ·
      refine ⟨811107579386817287414183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540738386257878191609455 811107579386817287414183)
      ·
        refine ⟨1216661369080225931121275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811107579386817287414183 1216661369080225931121275)
        ·
          refine ⟨1824992053620338896681913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216661369080225931121275 1824992053620338896681913)
          ·
            refine ⟨1368744040215254172511435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824992053620338896681913 1368744040215254172511435)
            ·
              refine ⟨2053116060322881258767153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368744040215254172511435 2053116060322881258767153)
              ·
                refine ⟨1539837045242160944075365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053116060322881258767153 1539837045242160944075365)
                ·
                  refine ⟨288719445982905177014131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539837045242160944075365 288719445982905177014131)
                  ·
                    rfl

theorem cell20_632564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_632564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632564 prefixEnd_632564 := by exact prefixLift 632564
  have htrace : WordTrace (prefixWord ++ tailWord_632564) baseStart_632564 baseEnd_632564 := by
    simpa [prefixWord, tailWord_632564, baseEnd_632564] using wordTrace_append hprefix tailTrace_632564
  have hstable : (prefixWord ++ tailWord_632564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632564).length < 2 ^ (prefixWord ++ tailWord_632564).sum := by decide
  have hdescent : baseEnd_632564 < baseStart_632564 := by decide
  rcases family_descends (prefixWord ++ tailWord_632564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632599 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_632599 : Nat := 118140960795 + 632599 * 2 ^ 59
def prefixEnd_632599 : Nat := 4983230072969 + 3 ^ 40 * 632599 * 2
def baseEnd_632599 : Nat := 288735420936600610847321

theorem tailTrace_632599 : CollatzResearch.WordTrace tailWord_632599 prefixEnd_632599 288735420936600610847321 := by
  unfold tailWord_632599
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072781035209337152860851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381854023472891435240567 23072781035209337152860851)
  ·
    refine ⟨34609171552814005729291277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072781035209337152860851 34609171552814005729291277)
    ·
      refine ⟨12978439332305252148484229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34609171552814005729291277 12978439332305252148484229)
      ·
        refine ⟨2433457374807234777840793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12978439332305252148484229 2433457374807234777840793)
        ·
          refine ⟨1825093031105426083380595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433457374807234777840793 1825093031105426083380595)
          ·
            refine ⟨2737639546658139125070893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825093031105426083380595 2737639546658139125070893)
            ·
              refine ⟨1026614829996802171901585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2737639546658139125070893 1026614829996802171901585)
              ·
                refine ⟨769961122497601628926189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026614829996802171901585 769961122497601628926189)
                ·
                  refine ⟨288735420936600610847321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769961122497601628926189 288735420936600610847321)
                  ·
                    rfl

theorem cell20_632599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_632599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632599 prefixEnd_632599 := by exact prefixLift 632599
  have htrace : WordTrace (prefixWord ++ tailWord_632599) baseStart_632599 baseEnd_632599 := by
    simpa [prefixWord, tailWord_632599, baseEnd_632599] using wordTrace_append hprefix tailTrace_632599
  have hstable : (prefixWord ++ tailWord_632599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632599).length < 2 ^ (prefixWord ++ tailWord_632599).sum := by decide
  have hdescent : baseEnd_632599 < baseStart_632599 := by decide
  rcases family_descends (prefixWord ++ tailWord_632599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632603 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_632603 : Nat := 118140960795 + 632603 * 2 ^ 59
def prefixEnd_632603 : Nat := 4983230072969 + 3 ^ 40 * 632603 * 2
def baseEnd_632603 : Nat := 288737246645594374713971

theorem tailTrace_632603 : CollatzResearch.WordTrace tailWord_632603 prefixEnd_632603 288737246645594374713971 := by
  unfold tailWord_632603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072926927194845836006463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381951284796563890670975 23072926927194845836006463)
  ·
    refine ⟨34609390390792268754009695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072926927194845836006463 34609390390792268754009695)
    ·
      refine ⟨51914085586188403131014543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34609390390792268754009695 51914085586188403131014543)
      ·
        refine ⟨77871128379282604696521815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51914085586188403131014543 77871128379282604696521815)
        ·
          refine ⟨116806692568923907044782723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77871128379282604696521815 116806692568923907044782723)
          ·
            refine ⟨175210038853385860567174085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116806692568923907044782723 175210038853385860567174085)
            ·
              refine ⟨32851882285009848856345141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175210038853385860567174085 32851882285009848856345141)
              ·
                refine ⟨3079863964219673330282357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32851882285009848856345141 3079863964219673330282357)
                ·
                  refine ⟨288737246645594374713971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079863964219673330282357 288737246645594374713971)
                  ·
                    rfl

theorem cell20_632603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_632603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632603 prefixEnd_632603 := by exact prefixLift 632603
  have htrace : WordTrace (prefixWord ++ tailWord_632603) baseStart_632603 baseEnd_632603 := by
    simpa [prefixWord, tailWord_632603, baseEnd_632603] using wordTrace_append hprefix tailTrace_632603
  have hstable : (prefixWord ++ tailWord_632603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632603).length < 2 ^ (prefixWord ++ tailWord_632603).sum := by decide
  have hdescent : baseEnd_632603 < baseStart_632603 := by decide
  rcases family_descends (prefixWord ++ tailWord_632603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632616 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_632616 : Nat := 118140960795 + 632616 * 2 ^ 59
def prefixEnd_632616 : Nat := 4983230072969 + 3 ^ 40 * 632616 * 2
def baseEnd_632616 : Nat := 288743180199824107280585

theorem tailTrace_632616 : CollatzResearch.WordTrace tailWord_632616 prefixEnd_632616 288743180199824107280585 := by
  unfold tailWord_632616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536700538073874528114851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15382267384098499370819801 11536700538073874528114851)
  ·
    refine ⟨17305050807110811792172277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536700538073874528114851 17305050807110811792172277)
    ·
      refine ⟨1622348513166638605516151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17305050807110811792172277 1622348513166638605516151)
      ·
        refine ⟨2433522769749957908274227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622348513166638605516151 2433522769749957908274227)
        ·
          refine ⟨3650284154624936862411341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433522769749957908274227 3650284154624936862411341)
          ·
            refine ⟨1368856557984351323404253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3650284154624936862411341 1368856557984351323404253)
            ·
              refine ⟨513321209244131746276595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368856557984351323404253 513321209244131746276595)
              ·
                refine ⟨769981813866197619414893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513321209244131746276595 769981813866197619414893)
                ·
                  refine ⟨288743180199824107280585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769981813866197619414893 288743180199824107280585)
                  ·
                    rfl

theorem cell20_632616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_632616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632616 prefixEnd_632616 := by exact prefixLift 632616
  have htrace : WordTrace (prefixWord ++ tailWord_632616) baseStart_632616 baseEnd_632616 := by
    simpa [prefixWord, tailWord_632616, baseEnd_632616] using wordTrace_append hprefix tailTrace_632616
  have hstable : (prefixWord ++ tailWord_632616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632616).length < 2 ^ (prefixWord ++ tailWord_632616).sum := by decide
  have hdescent : baseEnd_632616 < baseStart_632616 := by decide
  rcases family_descends (prefixWord ++ tailWord_632616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632630 : List Nat := [5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_632630 : Nat := 118140960795 + 632630 * 2 ^ 59
def prefixEnd_632630 : Nat := 4983230072969 + 3 ^ 40 * 632630 * 2
def baseEnd_632630 : Nat := 96249856727100760271287

theorem tailTrace_632630 : CollatzResearch.WordTrace tailWord_632630 prefixEnd_632630 96249856727100760271287 := by
  unfold tailWord_632630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442119481131064340452459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15382607798731352964826229 1442119481131064340452459)
  ·
    refine ⟨2163179221696596510678689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442119481131064340452459 2163179221696596510678689)
    ·
      refine ⟨1622384416272447383009017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163179221696596510678689 1622384416272447383009017)
      ·
        refine ⟨1216788312204335537256763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622384416272447383009017 1216788312204335537256763)
        ·
          refine ⟨1825182468306503305885145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216788312204335537256763 1825182468306503305885145)
          ·
            refine ⟨1368886851229877479413859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825182468306503305885145 1368886851229877479413859)
            ·
              refine ⟨2053330276844816219120789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368886851229877479413859 2053330276844816219120789)
              ·
                refine ⟨96249856727100760271287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2053330276844816219120789 96249856727100760271287)
                ·
                  rfl

theorem cell20_632630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_632630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632630 prefixEnd_632630 := by exact prefixLift 632630
  have htrace : WordTrace (prefixWord ++ tailWord_632630) baseStart_632630 baseEnd_632630 := by
    simpa [prefixWord, tailWord_632630, baseEnd_632630] using wordTrace_append hprefix tailTrace_632630
  have hstable : (prefixWord ++ tailWord_632630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632630).length < 2 ^ (prefixWord ++ tailWord_632630).sum := by decide
  have hdescent : baseEnd_632630 < baseStart_632630 := by decide
  rcases family_descends (prefixWord ++ tailWord_632630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632658 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_632658 : Nat := 118140960795 + 632658 * 2 ^ 59
def prefixEnd_632658 : Nat := 4983230072969 + 3 ^ 40 * 632658 * 2
def baseEnd_632658 : Nat := 288762350144258627880413

theorem tailTrace_632658 : CollatzResearch.WordTrace tailWord_632658 prefixEnd_632658 288762350144258627880413 := by
  unfold tailWord_632658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768733235498897557314657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15383288627997060152839085 5768733235498897557314657)
  ·
    refine ⟨4326549926624173167985993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5768733235498897557314657 4326549926624173167985993)
    ·
      refine ⟨3244912444968129875989495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4326549926624173167985993 3244912444968129875989495)
      ·
        refine ⟨4867368667452194813984243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244912444968129875989495 4867368667452194813984243)
        ·
          refine ⟨7301053001178292220976365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867368667452194813984243 7301053001178292220976365)
          ·
            refine ⟨2737894875441859582866137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7301053001178292220976365 2737894875441859582866137)
            ·
              refine ⟨2053421156581394687149603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737894875441859582866137 2053421156581394687149603)
              ·
                refine ⟨3080131734872092030724405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053421156581394687149603 3080131734872092030724405)
                ·
                  refine ⟨288762350144258627880413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080131734872092030724405 288762350144258627880413)
                  ·
                    rfl

theorem cell20_632658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_632658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632658 prefixEnd_632658 := by exact prefixLift 632658
  have htrace : WordTrace (prefixWord ++ tailWord_632658) baseStart_632658 baseEnd_632658 := by
    simpa [prefixWord, tailWord_632658, baseEnd_632658] using wordTrace_append hprefix tailTrace_632658
  have hstable : (prefixWord ++ tailWord_632658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632658).length < 2 ^ (prefixWord ++ tailWord_632658).sum := by decide
  have hdescent : baseEnd_632658 < baseStart_632658 := by decide
  rcases family_descends (prefixWord ++ tailWord_632658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632668 : List Nat := [2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_632668 : Nat := 118140960795 + 632668 * 2 ^ 59
def prefixEnd_632668 : Nat := 4983230072969 + 3 ^ 40 * 632668 * 2
def baseEnd_632668 : Nat := 96255638138914345849013

theorem tailTrace_632668 : CollatzResearch.WordTrace tailWord_632668 prefixEnd_632668 96255638138914345849013 := by
  unfold tailWord_632668
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537648835979680968561329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15383531781306241291415105 11537648835979680968561329)
  ·
    refine ⟨8653236626984760726420997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11537648835979680968561329 8653236626984760726420997)
    ·
      refine ⟨1622481867559642636203937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8653236626984760726420997 1622481867559642636203937)
      ·
        refine ⟨1216861400669731977152953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622481867559642636203937 1216861400669731977152953)
        ·
          refine ⟨912646050502298982864715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216861400669731977152953 912646050502298982864715)
          ·
            refine ⟨1368969075753448474297073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912646050502298982864715 1368969075753448474297073)
            ·
              refine ⟨1026726806815086355722805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368969075753448474297073 1026726806815086355722805)
              ·
                refine ⟨96255638138914345849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1026726806815086355722805 96255638138914345849013)
                ·
                  rfl

theorem cell20_632668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_632668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632668 prefixEnd_632668 := by exact prefixLift 632668
  have htrace : WordTrace (prefixWord ++ tailWord_632668) baseStart_632668 baseEnd_632668 := by
    simpa [prefixWord, tailWord_632668, baseEnd_632668] using wordTrace_append hprefix tailTrace_632668
  have hstable : (prefixWord ++ tailWord_632668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632668).length < 2 ^ (prefixWord ++ tailWord_632668).sum := by decide
  have hdescent : baseEnd_632668 < baseStart_632668 := by decide
  rcases family_descends (prefixWord ++ tailWord_632668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632672 : List Nat := [2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_632672 : Nat := 118140960795 + 632672 * 2 ^ 59
def prefixEnd_632672 : Nat := 4983230072969 + 3 ^ 40 * 632672 * 2
def baseEnd_632672 : Nat := 96256246708578933804563

theorem tailTrace_632672 : CollatzResearch.WordTrace tailWord_632672 prefixEnd_632672 96256246708578933804563 := by
  unfold tailWord_632672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537721781972435310134135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15383629042629913746845513 11537721781972435310134135)
  ·
    refine ⟨17306582672958652965201203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537721781972435310134135 17306582672958652965201203)
    ·
      refine ⟨25959874009437979447801805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17306582672958652965201203 25959874009437979447801805)
      ·
        refine ⟨9734952753539242292925677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25959874009437979447801805 9734952753539242292925677)
        ·
          refine ⟨3650607282577215859847129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9734952753539242292925677 3650607282577215859847129)
          ·
            refine ⟨2737955461932911894885347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3650607282577215859847129 2737955461932911894885347)
            ·
              refine ⟨4106933192899367842328021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737955461932911894885347 4106933192899367842328021)
              ·
                refine ⟨96256246708578933804563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4106933192899367842328021 96256246708578933804563)
                ·
                  rfl

theorem cell20_632672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_632672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632672 prefixEnd_632672 := by exact prefixLift 632672
  have htrace : WordTrace (prefixWord ++ tailWord_632672) baseStart_632672 baseEnd_632672 := by
    simpa [prefixWord, tailWord_632672, baseEnd_632672] using wordTrace_append hprefix tailTrace_632672
  have hstable : (prefixWord ++ tailWord_632672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632672).length < 2 ^ (prefixWord ++ tailWord_632672).sum := by decide
  have hdescent : baseEnd_632672 < baseStart_632672 := by decide
  rcases family_descends (prefixWord ++ tailWord_632672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632675 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_632675 : Nat := 118140960795 + 632675 * 2 ^ 59
def prefixEnd_632675 : Nat := 4983230072969 + 3 ^ 40 * 632675 * 2
def baseEnd_632675 : Nat := 288770109407482124313677

theorem tailTrace_632675 : CollatzResearch.WordTrace tailWord_632675 prefixEnd_632675 288770109407482124313677 := by
  unfold tailWord_632675
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075552982934002132627479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15383701988622668088418319 23075552982934002132627479)
  ·
    refine ⟨34613329474401003198941219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23075552982934002132627479 34613329474401003198941219)
    ·
      refine ⟨51919994211601504798411829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34613329474401003198941219 51919994211601504798411829)
      ·
        refine ⟨4867499457337641074851109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51919994211601504798411829 4867499457337641074851109)
        ·
          refine ⟨912656148250807701534583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4867499457337641074851109 912656148250807701534583)
          ·
            refine ⟨1368984222376211552301875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912656148250807701534583 1368984222376211552301875)
            ·
              refine ⟨2053476333564317328452813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368984222376211552301875 2053476333564317328452813)
              ·
                refine ⟨770053625086618998169805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053476333564317328452813 770053625086618998169805)
                ·
                  refine ⟨288770109407482124313677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770053625086618998169805 288770109407482124313677)
                  ·
                    rfl

theorem cell20_632675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_632675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632675 prefixEnd_632675 := by exact prefixLift 632675
  have htrace : WordTrace (prefixWord ++ tailWord_632675) baseStart_632675 baseEnd_632675 := by
    simpa [prefixWord, tailWord_632675, baseEnd_632675] using wordTrace_append hprefix tailTrace_632675
  have hstable : (prefixWord ++ tailWord_632675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632675).length < 2 ^ (prefixWord ++ tailWord_632675).sum := by decide
  have hdescent : baseEnd_632675 < baseStart_632675 := by decide
  rcases family_descends (prefixWord ++ tailWord_632675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632727 : List Nat := [1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_632727 : Nat := 118140960795 + 632727 * 2 ^ 59
def prefixEnd_632727 : Nat := 4983230072969 + 3 ^ 40 * 632727 * 2
def baseEnd_632727 : Nat := 96264614541467018193377

theorem tailTrace_632727 : CollatzResearch.WordTrace tailWord_632727 prefixEnd_632727 96264614541467018193377 := by
  unfold tailWord_632727
  simp only [CollatzResearch.WordTrace]
  refine ⟨23077449578745615013520435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15384966385830410009013623 23077449578745615013520435)
  ·
    refine ⟨34616174368118422520280653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23077449578745615013520435 34616174368118422520280653)
    ·
      refine ⟨12981065388044408445105245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34616174368118422520280653 12981065388044408445105245)
      ·
        refine ⟨4867899520516653166914467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12981065388044408445105245 4867899520516653166914467)
        ·
          refine ⟨7301849280774979750371701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867899520516653166914467 7301849280774979750371701)
          ·
            refine ⟨684548370072654351597347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7301849280774979750371701 684548370072654351597347)
            ·
              refine ⟨1026822555108981527396021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684548370072654351597347 1026822555108981527396021)
              ·
                refine ⟨96264614541467018193377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1026822555108981527396021 96264614541467018193377)
                ·
                  rfl

theorem cell20_632727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_632727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632727 prefixEnd_632727 := by exact prefixLift 632727
  have htrace : WordTrace (prefixWord ++ tailWord_632727) baseStart_632727 baseEnd_632727 := by
    simpa [prefixWord, tailWord_632727, baseEnd_632727] using wordTrace_append hprefix tailTrace_632727
  have hstable : (prefixWord ++ tailWord_632727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632727).length < 2 ^ (prefixWord ++ tailWord_632727).sum := by decide
  have hdescent : baseEnd_632727 < baseStart_632727 := by decide
  rcases family_descends (prefixWord ++ tailWord_632727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632750 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_632750 : Nat := 118140960795 + 632750 * 2 ^ 59
def prefixEnd_632750 : Nat := 4983230072969 + 3 ^ 40 * 632750 * 2
def baseEnd_632750 : Nat := 288804341451115196813371

theorem tailTrace_632750 : CollatzResearch.WordTrace tailWord_632750 prefixEnd_632750 288804341451115196813371 := by
  unfold tailWord_632750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884786057207786242700963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15385525638441526627738469 2884786057207786242700963)
  ·
    refine ⟨4327179085811679364051445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884786057207786242700963 4327179085811679364051445)
    ·
      refine ⟨405673039294844940379823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4327179085811679364051445 405673039294844940379823)
      ·
        refine ⟨608509558942267410569735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405673039294844940379823 608509558942267410569735)
        ·
          refine ⟨912764338413401115854603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608509558942267410569735 912764338413401115854603)
          ·
            refine ⟨1369146507620101673781905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912764338413401115854603 1369146507620101673781905)
            ·
              refine ⟨1026859880715076255336429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369146507620101673781905 1026859880715076255336429)
              ·
                refine ⟨385072455268153595751161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026859880715076255336429 385072455268153595751161)
                ·
                  refine ⟨288804341451115196813371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385072455268153595751161 288804341451115196813371)
                  ·
                    rfl

theorem cell20_632750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_632750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632750 prefixEnd_632750 := by exact prefixLift 632750
  have htrace : WordTrace (prefixWord ++ tailWord_632750) baseStart_632750 baseEnd_632750 := by
    simpa [prefixWord, tailWord_632750, baseEnd_632750] using wordTrace_append hprefix tailTrace_632750
  have hstable : (prefixWord ++ tailWord_632750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632750).length < 2 ^ (prefixWord ++ tailWord_632750).sum := by decide
  have hdescent : baseEnd_632750 < baseStart_632750 := by decide
  rcases family_descends (prefixWord ++ tailWord_632750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632755 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_632755 : Nat := 118140960795 + 632755 * 2 ^ 59
def prefixEnd_632755 : Nat := 4983230072969 + 3 ^ 40 * 632755 * 2
def baseEnd_632755 : Nat := 288806623587357401646683

theorem tailTrace_632755 : CollatzResearch.WordTrace tailWord_632755 prefixEnd_632755 288806623587357401646683 := by
  unfold tailWord_632755
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078470822644175795539719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15385647215096117197026479 23078470822644175795539719)
  ·
    refine ⟨34617706233966263693309579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078470822644175795539719 34617706233966263693309579)
    ·
      refine ⟨51926559350949395539964369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617706233966263693309579 51926559350949395539964369)
      ·
        refine ⟨38944919513212046654973277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51926559350949395539964369 38944919513212046654973277)
        ·
          refine ⟨14604344817454517495614979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38944919513212046654973277 14604344817454517495614979)
          ·
            refine ⟨21906517226181776243422469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14604344817454517495614979 21906517226181776243422469)
            ·
              refine ⟨4107471979909083045641713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21906517226181776243422469 4107471979909083045641713)
              ·
                refine ⟨3080603984931812284231285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107471979909083045641713 3080603984931812284231285)
                ·
                  refine ⟨288806623587357401646683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080603984931812284231285 288806623587357401646683)
                  ·
                    rfl

theorem cell20_632755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_632755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632755 prefixEnd_632755 := by exact prefixLift 632755
  have htrace : WordTrace (prefixWord ++ tailWord_632755) baseStart_632755 baseEnd_632755 := by
    simpa [prefixWord, tailWord_632755, baseEnd_632755] using wordTrace_append hprefix tailTrace_632755
  have hstable : (prefixWord ++ tailWord_632755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632755).length < 2 ^ (prefixWord ++ tailWord_632755).sum := by decide
  have hdescent : baseEnd_632755 < baseStart_632755 := by decide
  rcases family_descends (prefixWord ++ tailWord_632755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632779 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_632779 : Nat := 118140960795 + 632779 * 2 ^ 59
def prefixEnd_632779 : Nat := 4983230072969 + 3 ^ 40 * 632779 * 2
def baseEnd_632779 : Nat := 288817577841319984846585

theorem tailTrace_632779 : CollatzResearch.WordTrace tailWord_632779 prefixEnd_632779 288817577841319984846585 := by
  unfold tailWord_632779
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079346174557227894413391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15386230783038151929608927 23079346174557227894413391)
  ·
    refine ⟨34619019261835841841620087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23079346174557227894413391 34619019261835841841620087)
    ·
      refine ⟨51928528892753762762430131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34619019261835841841620087 51928528892753762762430131)
      ·
        refine ⟨77892793339130644143645197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51928528892753762762430131 77892793339130644143645197)
        ·
          refine ⟨29209797502173991553866949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77892793339130644143645197 29209797502173991553866949)
          ·
            refine ⟨5476837031657623416350053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29209797502173991553866949 5476837031657623416350053)
            ·
              refine ⟨1026906943435804390565635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5476837031657623416350053 1026906943435804390565635)
              ·
                refine ⟨1540360415153706585848453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026906943435804390565635 1540360415153706585848453)
                ·
                  refine ⟨288817577841319984846585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540360415153706585848453 288817577841319984846585)
                  ·
                    rfl

theorem cell20_632779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_632779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632779 prefixEnd_632779 := by exact prefixLift 632779
  have htrace : WordTrace (prefixWord ++ tailWord_632779) baseStart_632779 baseEnd_632779 := by
    simpa [prefixWord, tailWord_632779, baseEnd_632779] using wordTrace_append hprefix tailTrace_632779
  have hstable : (prefixWord ++ tailWord_632779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632779).length < 2 ^ (prefixWord ++ tailWord_632779).sum := by decide
  have hdescent : baseEnd_632779 < baseStart_632779 := by decide
  rcases family_descends (prefixWord ++ tailWord_632779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632803 : List Nat := [1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_632803 : Nat := 118140960795 + 632803 * 2 ^ 59
def prefixEnd_632803 : Nat := 4983230072969 + 3 ^ 40 * 632803 * 2
def baseEnd_632803 : Nat := 96276177365094189348829

theorem tailTrace_632803 : CollatzResearch.WordTrace tailWord_632803 prefixEnd_632803 96276177365094189348829 := by
  unfold tailWord_632803
  simp only [CollatzResearch.WordTrace]
  refine ⟨23080221526470279993287063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15386814350980186662191375 23080221526470279993287063)
  ·
    refine ⟨34620332289705419989930595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23080221526470279993287063 34620332289705419989930595)
    ·
      refine ⟨51930498434558129984895893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34620332289705419989930595 51930498434558129984895893)
      ·
        refine ⟨2434242114119912343041995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51930498434558129984895893 2434242114119912343041995)
        ·
          refine ⟨3651363171179868514562993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434242114119912343041995 3651363171179868514562993)
          ·
            refine ⟨2738522378384901385922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3651363171179868514562993 2738522378384901385922245)
            ·
              refine ⟨513472945947169009860421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2738522378384901385922245 513472945947169009860421)
              ·
                refine ⟨96276177365094189348829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513472945947169009860421 96276177365094189348829)
                ·
                  rfl

theorem cell20_632803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_632803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632803 prefixEnd_632803 := by exact prefixLift 632803
  have htrace : WordTrace (prefixWord ++ tailWord_632803) baseStart_632803 baseEnd_632803 := by
    simpa [prefixWord, tailWord_632803, baseEnd_632803] using wordTrace_append hprefix tailTrace_632803
  have hstable : (prefixWord ++ tailWord_632803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632803).length < 2 ^ (prefixWord ++ tailWord_632803).sum := by decide
  have hdescent : baseEnd_632803 < baseStart_632803 := by decide
  rcases family_descends (prefixWord ++ tailWord_632803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632876 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_632876 : Nat := 118140960795 + 632876 * 2 ^ 59
def prefixEnd_632876 : Nat := 4983230072969 + 3 ^ 40 * 632876 * 2
def baseEnd_632876 : Nat := 288861851284418758612855

theorem tailTrace_632876 : CollatzResearch.WordTrace tailWord_632876 prefixEnd_632876 288861851284418758612855 := by
  unfold tailWord_632876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541442027602906730347241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15388589370137208973796321 11541442027602906730347241)
  ·
    refine ⟨8656081520702180047760431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11541442027602906730347241 8656081520702180047760431)
    ·
      refine ⟨12984122281053270071640647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656081520702180047760431 12984122281053270071640647)
      ·
        refine ⟨19476183421579905107460971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12984122281053270071640647 19476183421579905107460971)
        ·
          refine ⟨29214275132369857661191457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19476183421579905107460971 29214275132369857661191457)
          ·
            refine ⟨21910706349277393245893593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29214275132369857661191457 21910706349277393245893593)
            ·
              refine ⟨16433029761958044934420195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21910706349277393245893593 16433029761958044934420195)
              ·
                refine ⟨24649544642937067401630293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16433029761958044934420195 24649544642937067401630293)
                ·
                  refine ⟨288861851284418758612855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24649544642937067401630293 288861851284418758612855)
                  ·
                    rfl

theorem cell20_632876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_632876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632876 prefixEnd_632876 := by exact prefixLift 632876
  have htrace : WordTrace (prefixWord ++ tailWord_632876) baseStart_632876 baseEnd_632876 := by
    simpa [prefixWord, tailWord_632876, baseEnd_632876] using wordTrace_append hprefix tailTrace_632876
  have hstable : (prefixWord ++ tailWord_632876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632876).length < 2 ^ (prefixWord ++ tailWord_632876).sum := by decide
  have hdescent : baseEnd_632876 < baseStart_632876 := by decide
  rcases family_descends (prefixWord ++ tailWord_632876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632889 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 2]
def baseStart_632889 : Nat := 118140960795 + 632889 * 2 ^ 59
def prefixEnd_632889 : Nat := 4983230072969 + 3 ^ 40 * 632889 * 2
def baseEnd_632889 : Nat := 288867784838648491179469

theorem tailTrace_632889 : CollatzResearch.WordTrace tailWord_632889 prefixEnd_632889 288867784838648491179469 := by
  unfold tailWord_632889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23083358204158716680917721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15388905469439144453945147 23083358204158716680917721)
  ·
    refine ⟨17312518653119037510688291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23083358204158716680917721 17312518653119037510688291)
    ·
      refine ⟨25968777979678556266032437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17312518653119037510688291 25968777979678556266032437)
      ·
        refine ⟨2434572935594864649940541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25968777979678556266032437 2434572935594864649940541)
        ·
          refine ⟨912964850848074243727703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434572935594864649940541 912964850848074243727703)
          ·
            refine ⟨1369447276272111365591555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912964850848074243727703 1369447276272111365591555)
            ·
              refine ⟨2054170914408167048387333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369447276272111365591555 2054170914408167048387333)
              ·
                refine ⟨385157046451531321572625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2054170914408167048387333 385157046451531321572625)
                ·
                  refine ⟨288867784838648491179469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385157046451531321572625 288867784838648491179469)
                  ·
                    rfl

theorem cell20_632889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_632889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632889 prefixEnd_632889 := by exact prefixLift 632889
  have htrace : WordTrace (prefixWord ++ tailWord_632889) baseStart_632889 baseEnd_632889 := by
    simpa [prefixWord, tailWord_632889, baseEnd_632889] using wordTrace_append hprefix tailTrace_632889
  have hstable : (prefixWord ++ tailWord_632889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632889).length < 2 ^ (prefixWord ++ tailWord_632889).sum := by decide
  have hdescent : baseEnd_632889 < baseStart_632889 := by decide
  rcases family_descends (prefixWord ++ tailWord_632889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632893 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_632893 : Nat := 118140960795 + 632893 * 2 ^ 59
def prefixEnd_632893 : Nat := 4983230072969 + 3 ^ 40 * 632893 * 2
def baseEnd_632893 : Nat := 288869610547642255046119

theorem tailTrace_632893 : CollatzResearch.WordTrace tailWord_632893 prefixEnd_632893 288869610547642255046119 := by
  unfold tailWord_632893
  simp only [CollatzResearch.WordTrace]
  refine ⟨23083504096144225364063333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15389002730762816909375555 23083504096144225364063333)
  ·
    refine ⟨4328157018027042255761875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23083504096144225364063333 4328157018027042255761875)
    ·
      refine ⟨6492235527040563383642813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4328157018027042255761875 6492235527040563383642813)
      ·
        refine ⟨2434588322640211268866055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6492235527040563383642813 2434588322640211268866055)
        ·
          refine ⟨3651882483960316903299083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434588322640211268866055 3651882483960316903299083)
          ·
            refine ⟨5477823725940475354948625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651882483960316903299083 5477823725940475354948625)
            ·
              refine ⟨4108367794455356516211469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477823725940475354948625 4108367794455356516211469)
              ·
                refine ⟨1540637922920758693579301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108367794455356516211469 1540637922920758693579301)
                ·
                  refine ⟨288869610547642255046119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540637922920758693579301 288869610547642255046119)
                  ·
                    rfl

theorem cell20_632893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_632893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632893 prefixEnd_632893 := by exact prefixLift 632893
  have htrace : WordTrace (prefixWord ++ tailWord_632893) baseStart_632893 baseEnd_632893 := by
    simpa [prefixWord, tailWord_632893, baseEnd_632893] using wordTrace_append hprefix tailTrace_632893
  have hstable : (prefixWord ++ tailWord_632893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632893).length < 2 ^ (prefixWord ++ tailWord_632893).sum := by decide
  have hdescent : baseEnd_632893 < baseStart_632893 := by decide
  rcases family_descends (prefixWord ++ tailWord_632893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632917 : List Nat := [1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_632917 : Nat := 118140960795 + 632917 * 2 ^ 59
def prefixEnd_632917 : Nat := 4983230072969 + 3 ^ 40 * 632917 * 2
def baseEnd_632917 : Nat := 96293521600534946082007

theorem tailTrace_632917 : CollatzResearch.WordTrace tailWord_632917 prefixEnd_632917 96293521600534946082007 := by
  unfold tailWord_632917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084379448057277462937005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15389586298704851641958003 23084379448057277462937005)
  ·
    refine ⟨8656642293021479048601377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23084379448057277462937005 8656642293021479048601377)
    ·
      refine ⟨6492481719766109286451033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8656642293021479048601377 6492481719766109286451033)
      ·
        refine ⟨4869361289824581964838275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6492481719766109286451033 4869361289824581964838275)
        ·
          refine ⟨7304041934736872947257413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869361289824581964838275 7304041934736872947257413)
          ·
            refine ⟨1369507862763163677610765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7304041934736872947257413 1369507862763163677610765)
            ·
              refine ⟨513565448536186379104037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1369507862763163677610765 513565448536186379104037)
              ·
                refine ⟨96293521600534946082007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513565448536186379104037 96293521600534946082007)
                ·
                  rfl

theorem cell20_632917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_632917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632917 prefixEnd_632917 := by exact prefixLift 632917
  have htrace : WordTrace (prefixWord ++ tailWord_632917) baseStart_632917 baseEnd_632917 := by
    simpa [prefixWord, tailWord_632917, baseEnd_632917] using wordTrace_append hprefix tailTrace_632917
  have hstable : (prefixWord ++ tailWord_632917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632917).length < 2 ^ (prefixWord ++ tailWord_632917).sum := by decide
  have hdescent : baseEnd_632917 < baseStart_632917 := by decide
  rcases family_descends (prefixWord ++ tailWord_632917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632945 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_632945 : Nat := 118140960795 + 632945 * 2 ^ 59
def prefixEnd_632945 : Nat := 4983230072969 + 3 ^ 40 * 632945 * 2
def baseEnd_632945 : Nat := 288893344764561185312573

theorem tailTrace_632945 : CollatzResearch.WordTrace tailWord_632945 prefixEnd_632945 288893344764561185312573 := by
  unfold tailWord_632945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23085400691955838244956289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15390267127970558829970859 23085400691955838244956289)
  ·
    refine ⟨17314050518966878683717217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23085400691955838244956289 17314050518966878683717217)
    ·
      refine ⟨12985537889225159012787913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17314050518966878683717217 12985537889225159012787913)
      ·
        refine ⟨9739153416918869259590935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12985537889225159012787913 9739153416918869259590935)
        ·
          refine ⟨14608730125378303889386403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739153416918869259590935 14608730125378303889386403)
          ·
            refine ⟨21913095188067455834079605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608730125378303889386403 21913095188067455834079605)
            ·
              refine ⟨2054352673881323984444963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21913095188067455834079605 2054352673881323984444963)
              ·
                refine ⟨3081529010821985976667445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054352673881323984444963 3081529010821985976667445)
                ·
                  refine ⟨288893344764561185312573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081529010821985976667445 288893344764561185312573)
                  ·
                    rfl

theorem cell20_632945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_632945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632945 prefixEnd_632945 := by exact prefixLift 632945
  have htrace : WordTrace (prefixWord ++ tailWord_632945) baseStart_632945 baseEnd_632945 := by
    simpa [prefixWord, tailWord_632945, baseEnd_632945] using wordTrace_append hprefix tailTrace_632945
  have hstable : (prefixWord ++ tailWord_632945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632945).length < 2 ^ (prefixWord ++ tailWord_632945).sum := by decide
  have hdescent : baseEnd_632945 < baseStart_632945 := by decide
  rcases family_descends (prefixWord ++ tailWord_632945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633013 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_633013 : Nat := 118140960795 + 633013 * 2 ^ 59
def prefixEnd_633013 : Nat := 4983230072969 + 3 ^ 40 * 633013 * 2
def baseEnd_633013 : Nat := 288924381817455171045629

theorem tailTrace_633013 : CollatzResearch.WordTrace tailWord_633013 prefixEnd_633013 288924381817455171045629 := by
  unfold tailWord_633013
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087880855709485858431693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15391920570472990572287795 23087880855709485858431693)
  ·
    refine ⟨8657955320891057196911885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23087880855709485858431693 8657955320891057196911885)
    ·
      refine ⟨3246733245334146448841957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8657955320891057196911885 3246733245334146448841957)
      ·
        refine ⟨608762483500152459157867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3246733245334146448841957 608762483500152459157867)
        ·
          refine ⟨913143725250228688736801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608762483500152459157867 913143725250228688736801)
          ·
            refine ⟨684857793937671516552601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913143725250228688736801 684857793937671516552601)
            ·
              refine ⟨513643345453253637414451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684857793937671516552601 513643345453253637414451)
              ·
                refine ⟨770465018179880456121677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513643345453253637414451 770465018179880456121677)
                ·
                  refine ⟨288924381817455171045629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770465018179880456121677 288924381817455171045629)
                  ·
                    rfl

theorem cell20_633013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_633013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633013 prefixEnd_633013 := by exact prefixLift 633013
  have htrace : WordTrace (prefixWord ++ tailWord_633013) baseStart_633013 baseEnd_633013 := by
    simpa [prefixWord, tailWord_633013, baseEnd_633013] using wordTrace_append hprefix tailTrace_633013
  have hstable : (prefixWord ++ tailWord_633013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633013).length < 2 ^ (prefixWord ++ tailWord_633013).sum := by decide
  have hdescent : baseEnd_633013 < baseStart_633013 := by decide
  rcases family_descends (prefixWord ++ tailWord_633013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633035 : List Nat := [1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_633035 : Nat := 118140960795 + 633035 * 2 ^ 59
def prefixEnd_633035 : Nat := 4983230072969 + 3 ^ 40 * 633035 * 2
def baseEnd_633035 : Nat := 96311474405640290770735

theorem tailTrace_633035 : CollatzResearch.WordTrace tailWord_633035 prefixEnd_633035 96311474405640290770735 := by
  unfold tailWord_633035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23088683261629783615732559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15392455507753189077155039 23088683261629783615732559)
  ·
    refine ⟨34633024892444675423598839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23088683261629783615732559 34633024892444675423598839)
    ·
      refine ⟨51949537338667013135398259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34633024892444675423598839 51949537338667013135398259)
      ·
        refine ⟨77924306008000519703097389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51949537338667013135398259 77924306008000519703097389)
        ·
          refine ⟨29221614753000194888661521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77924306008000519703097389 29221614753000194888661521)
          ·
            refine ⟨21916211064750146166496141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29221614753000194888661521 21916211064750146166496141)
            ·
              refine ⟨8218579149281304812436053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21916211064750146166496141 8218579149281304812436053)
              ·
                refine ⟨96311474405640290770735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8218579149281304812436053 96311474405640290770735)
                ·
                  rfl

theorem cell20_633035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_633035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633035 prefixEnd_633035 := by exact prefixLift 633035
  have htrace : WordTrace (prefixWord ++ tailWord_633035) baseStart_633035 baseEnd_633035 := by
    simpa [prefixWord, tailWord_633035, baseEnd_633035] using wordTrace_append hprefix tailTrace_633035
  have hstable : (prefixWord ++ tailWord_633035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633035).length < 2 ^ (prefixWord ++ tailWord_633035).sum := by decide
  have hdescent : baseEnd_633035 < baseStart_633035 := by decide
  rcases family_descends (prefixWord ++ tailWord_633035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633100 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_633100 : Nat := 118140960795 + 633100 * 2 ^ 59
def prefixEnd_633100 : Nat := 4983230072969 + 3 ^ 40 * 633100 * 2
def baseEnd_633100 : Nat := 288964090988069535145273

theorem tailTrace_633100 : CollatzResearch.WordTrace tailWord_633100 prefixEnd_633100 288964090988069535145273 := by
  unfold tailWord_633100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11545527003197149858424377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15394036004262866477899169 11545527003197149858424377)
  ·
    refine ⟨8659145252397862393818283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11545527003197149858424377 8659145252397862393818283)
    ·
      refine ⟨12988717878596793590727425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8659145252397862393818283 12988717878596793590727425)
      ·
        refine ⟨9741538408947595193045569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12988717878596793590727425 9741538408947595193045569)
        ·
          refine ⟨7306153806710696394784177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9741538408947595193045569 7306153806710696394784177)
          ·
            refine ⟨5479615355033022296088133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7306153806710696394784177 5479615355033022296088133)
            ·
              refine ⟨1027427879068691680516525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5479615355033022296088133 1027427879068691680516525)
              ·
                refine ⟨385285454650759380193697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027427879068691680516525 385285454650759380193697)
                ·
                  refine ⟨288964090988069535145273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385285454650759380193697 288964090988069535145273)
                  ·
                    rfl

theorem cell20_633100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_633100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633100 prefixEnd_633100 := by exact prefixLift 633100
  have htrace : WordTrace (prefixWord ++ tailWord_633100) baseStart_633100 baseEnd_633100 := by
    simpa [prefixWord, tailWord_633100, baseEnd_633100] using wordTrace_append hprefix tailTrace_633100
  have hstable : (prefixWord ++ tailWord_633100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633100).length < 2 ^ (prefixWord ++ tailWord_633100).sum := by decide
  have hdescent : baseEnd_633100 < baseStart_633100 := by decide
  rcases family_descends (prefixWord ++ tailWord_633100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633114 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_633114 : Nat := 118140960795 + 633114 * 2 ^ 59
def prefixEnd_633114 : Nat := 4983230072969 + 3 ^ 40 * 633114 * 2
def baseEnd_633114 : Nat := 288970480969547708678549

theorem tailTrace_633114 : CollatzResearch.WordTrace tailWord_633114 prefixEnd_633114 288970480969547708678549 := by
  unfold tailWord_633114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772891157085895026964599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15394376418895720071905597 5772891157085895026964599)
  ·
    refine ⟨8659336735628842540446899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5772891157085895026964599 8659336735628842540446899)
    ·
      refine ⟨12989005103443263810670349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8659336735628842540446899 12989005103443263810670349)
      ·
        refine ⟨4870876913791223929001381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12989005103443263810670349 4870876913791223929001381)
        ·
          refine ⟨913289421335854486687759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4870876913791223929001381 913289421335854486687759)
          ·
            refine ⟨1369934132003781730031639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913289421335854486687759 1369934132003781730031639)
            ·
              refine ⟨2054901198005672595047459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369934132003781730031639 2054901198005672595047459)
              ·
                refine ⟨3082351797008508892571189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054901198005672595047459 3082351797008508892571189)
                ·
                  refine ⟨288970480969547708678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082351797008508892571189 288970480969547708678549)
                  ·
                    rfl

theorem cell20_633114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_633114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633114 prefixEnd_633114 := by exact prefixLift 633114
  have htrace : WordTrace (prefixWord ++ tailWord_633114) baseStart_633114 baseEnd_633114 := by
    simpa [prefixWord, tailWord_633114, baseEnd_633114] using wordTrace_append hprefix tailTrace_633114
  have hstable : (prefixWord ++ tailWord_633114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633114).length < 2 ^ (prefixWord ++ tailWord_633114).sum := by decide
  have hdescent : baseEnd_633114 < baseStart_633114 := by decide
  rcases family_descends (prefixWord ++ tailWord_633114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633135 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_633135 : Nat := 118140960795 + 633135 * 2 ^ 59
def prefixEnd_633135 : Nat := 4983230072969 + 3 ^ 40 * 633135 * 2
def baseEnd_633135 : Nat := 288980065941764968978463

theorem tailTrace_633135 : CollatzResearch.WordTrace tailWord_633135 prefixEnd_633135 288980065941764968978463 := by
  unfold tailWord_633135
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092330561267500694372859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15394887040845000462915239 23092330561267500694372859)
  ·
    refine ⟨34638495841901251041559289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23092330561267500694372859 34638495841901251041559289)
    ·
      refine ⟨25978871881425938281169467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34638495841901251041559289 25978871881425938281169467)
      ·
        refine ⟨38968307822138907421754201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25978871881425938281169467 38968307822138907421754201)
        ·
          refine ⟨29226230866604180566315651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38968307822138907421754201 29226230866604180566315651)
          ·
            refine ⟨43839346299906270849473477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29226230866604180566315651 43839346299906270849473477)
            ·
              refine ⟨8219877431232425784276277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43839346299906270849473477 8219877431232425784276277)
              ·
                refine ⟨770613509178039917275901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8219877431232425784276277 770613509178039917275901)
                ·
                  refine ⟨288980065941764968978463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770613509178039917275901 288980065941764968978463)
                  ·
                    rfl

theorem cell20_633135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_633135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633135 prefixEnd_633135 := by exact prefixLift 633135
  have htrace : WordTrace (prefixWord ++ tailWord_633135) baseStart_633135 baseEnd_633135 := by
    simpa [prefixWord, tailWord_633135, baseEnd_633135] using wordTrace_append hprefix tailTrace_633135
  have hstable : (prefixWord ++ tailWord_633135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633135).length < 2 ^ (prefixWord ++ tailWord_633135).sum := by decide
  have hdescent : baseEnd_633135 < baseStart_633135 := by decide
  rcases family_descends (prefixWord ++ tailWord_633135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633145 : List Nat := [1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_633145 : Nat := 118140960795 + 633145 * 2 ^ 59
def prefixEnd_633145 : Nat := 4983230072969 + 3 ^ 40 * 633145 * 2
def baseEnd_633145 : Nat := 96328210071416459548363

theorem tailTrace_633145 : CollatzResearch.WordTrace tailWord_633145 prefixEnd_633145 96328210071416459548363 := by
  unfold tailWord_633145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092695291231272402236889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395130194154181601491259 23092695291231272402236889)
  ·
    refine ⟨17319521468423454301677667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23092695291231272402236889 17319521468423454301677667)
    ·
      refine ⟨25979282202635181452516501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17319521468423454301677667 25979282202635181452516501)
      ·
        refine ⟨1217778853248524130586711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25979282202635181452516501 1217778853248524130586711)
        ·
          refine ⟨1826668279872786195880067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217778853248524130586711 1826668279872786195880067)
          ·
            refine ⟨2740002419809179293820101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826668279872786195880067 2740002419809179293820101)
            ·
              refine ⟨513750453714221117591269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2740002419809179293820101 513750453714221117591269)
              ·
                refine ⟨96328210071416459548363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513750453714221117591269 96328210071416459548363)
                ·
                  rfl

theorem cell20_633145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_633145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633145 prefixEnd_633145 := by exact prefixLift 633145
  have htrace : WordTrace (prefixWord ++ tailWord_633145) baseStart_633145 baseEnd_633145 := by
    simpa [prefixWord, tailWord_633145, baseEnd_633145] using wordTrace_append hprefix tailTrace_633145
  have hstable : (prefixWord ++ tailWord_633145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633145).length < 2 ^ (prefixWord ++ tailWord_633145).sum := by decide
  have hdescent : baseEnd_633145 < baseStart_633145 := by decide
  rcases family_descends (prefixWord ++ tailWord_633145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633182 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_633182 : Nat := 118140960795 + 633182 * 2 ^ 59
def prefixEnd_633182 : Nat := 4983230072969 + 3 ^ 40 * 633182 * 2
def baseEnd_633182 : Nat := 289001518022441694411605

theorem tailTrace_633182 : CollatzResearch.WordTrace tailWord_633182 prefixEnd_633182 289001518022441694411605 := by
  unfold tailWord_633182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886755599012153465166725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15396029861398151814222533 2886755599012153465166725)
  ·
    refine ⟨541266674814778774718761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2886755599012153465166725 541266674814778774718761)
    ·
      refine ⟨405950006111084081039071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541266674814778774718761 405950006111084081039071)
      ·
        refine ⟨608925009166626121558607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405950006111084081039071 608925009166626121558607)
        ·
          refine ⟨913387513749939182337911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608925009166626121558607 913387513749939182337911)
          ·
            refine ⟨1370081270624908773506867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913387513749939182337911 1370081270624908773506867)
            ·
              refine ⟨2055121905937363160260301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370081270624908773506867 2055121905937363160260301)
              ·
                refine ⟨770670714726511185097613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055121905937363160260301 770670714726511185097613)
                ·
                  refine ⟨289001518022441694411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770670714726511185097613 289001518022441694411605)
                  ·
                    rfl

theorem cell20_633182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_633182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633182 prefixEnd_633182 := by exact prefixLift 633182
  have htrace : WordTrace (prefixWord ++ tailWord_633182) baseStart_633182 baseEnd_633182 := by
    simpa [prefixWord, tailWord_633182, baseEnd_633182] using wordTrace_append hprefix tailTrace_633182
  have hstable : (prefixWord ++ tailWord_633182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633182).length < 2 ^ (prefixWord ++ tailWord_633182).sum := by decide
  have hdescent : baseEnd_633182 < baseStart_633182 := by decide
  rcases family_descends (prefixWord ++ tailWord_633182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633186 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_633186 : Nat := 118140960795 + 633186 * 2 ^ 59
def prefixEnd_633186 : Nat := 4983230072969 + 3 ^ 40 * 633186 * 2
def baseEnd_633186 : Nat := 289003343731435458278255

theorem tailTrace_633186 : CollatzResearch.WordTrace tailWord_633186 prefixEnd_633186 289003343731435458278255 := by
  unfold tailWord_633186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773547671020684101119853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15396127122721824269652941 5773547671020684101119853)
  ·
    refine ⟨2165080376632756537919945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5773547671020684101119853 2165080376632756537919945)
    ·
      refine ⟨1623810282474567403439959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2165080376632756537919945 1623810282474567403439959)
      ·
        refine ⟨2435715423711851105159939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623810282474567403439959 2435715423711851105159939)
        ·
          refine ⟨3653573135567776657739909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435715423711851105159939 3653573135567776657739909)
          ·
            refine ⟨685044962918958123326233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3653573135567776657739909 685044962918958123326233)
            ·
              refine ⟨513783722189218592494675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685044962918958123326233 513783722189218592494675)
              ·
                refine ⟨770675583283827888742013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513783722189218592494675 770675583283827888742013)
                ·
                  refine ⟨289003343731435458278255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770675583283827888742013 289003343731435458278255)
                  ·
                    rfl

theorem cell20_633186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_633186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633186 prefixEnd_633186 := by exact prefixLift 633186
  have htrace : WordTrace (prefixWord ++ tailWord_633186) baseStart_633186 baseEnd_633186 := by
    simpa [prefixWord, tailWord_633186, baseEnd_633186] using wordTrace_append hprefix tailTrace_633186
  have hstable : (prefixWord ++ tailWord_633186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633186).length < 2 ^ (prefixWord ++ tailWord_633186).sum := by decide
  have hdescent : baseEnd_633186 < baseStart_633186 := by decide
  rcases family_descends (prefixWord ++ tailWord_633186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633225 : List Nat := [1, 2, 1, 1, 6, 9]
def baseStart_633225 : Nat := 118140960795 + 633225 * 2 ^ 59
def prefixEnd_633225 : Nat := 4983230072969 + 3 ^ 40 * 633225 * 2
def baseEnd_633225 : Nat := 10704486829412024295485

theorem tailTrace_633225 : CollatzResearch.WordTrace tailWord_633225 prefixEnd_633225 10704486829412024295485 := by
  unfold tailWord_633225
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095613130941446065149129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15397075420627630710099419 23095613130941446065149129)
  ·
    refine ⟨17321709848206084548861847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23095613130941446065149129 17321709848206084548861847)
    ·
      refine ⟨25982564772309126823292771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17321709848206084548861847 25982564772309126823292771)
      ·
        refine ⟨38973847158463690234939157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25982564772309126823292771 38973847158463690234939157)
        ·
          refine ⟨1826899085552985479762773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38973847158463690234939157 1826899085552985479762773)
          ·
            refine ⟨10704486829412024295485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1826899085552985479762773 10704486829412024295485)
            ·
              rfl

theorem cell20_633225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_633225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633225 prefixEnd_633225 := by exact prefixLift 633225
  have htrace : WordTrace (prefixWord ++ tailWord_633225) baseStart_633225 baseEnd_633225 := by
    simpa [prefixWord, tailWord_633225, baseEnd_633225] using wordTrace_append hprefix tailTrace_633225
  have hstable : (prefixWord ++ tailWord_633225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633225).length < 2 ^ (prefixWord ++ tailWord_633225).sum := by decide
  have hdescent : baseEnd_633225 < baseStart_633225 := by decide
  rcases family_descends (prefixWord ++ tailWord_633225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633228 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_633228 : Nat := 118140960795 + 633228 * 2 ^ 59
def prefixEnd_633228 : Nat := 4983230072969 + 3 ^ 40 * 633228 * 2
def baseEnd_633228 : Nat := 289022513675869978878083

theorem tailTrace_633228 : CollatzResearch.WordTrace tailWord_633228 prefixEnd_633228 289022513675869978878083 := by
  unfold tailWord_633228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11547861274965288788754169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15397148366620385051672225 11547861274965288788754169)
  ·
    refine ⟨8660895956223966591565627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11547861274965288788754169 8660895956223966591565627)
    ·
      refine ⟨12991343934335949887348441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8660895956223966591565627 12991343934335949887348441)
      ·
        refine ⟨9743507950751962415511331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12991343934335949887348441 9743507950751962415511331)
        ·
          refine ⟨14615261926127943623266997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743507950751962415511331 14615261926127943623266997)
          ·
            refine ⟨1370180805574494714681281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14615261926127943623266997 1370180805574494714681281)
            ·
              refine ⟨1027635604180871036010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370180805574494714681281 1027635604180871036010961)
              ·
                refine ⟨770726703135653277008221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027635604180871036010961 770726703135653277008221)
                ·
                  refine ⟨289022513675869978878083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770726703135653277008221 289022513675869978878083)
                  ·
                    rfl

theorem cell20_633228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_633228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633228 prefixEnd_633228 := by exact prefixLift 633228
  have htrace : WordTrace (prefixWord ++ tailWord_633228) baseStart_633228 baseEnd_633228 := by
    simpa [prefixWord, tailWord_633228, baseEnd_633228] using wordTrace_append hprefix tailTrace_633228
  have hstable : (prefixWord ++ tailWord_633228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633228).length < 2 ^ (prefixWord ++ tailWord_633228).sum := by decide
  have hdescent : baseEnd_633228 < baseStart_633228 := by decide
  rcases family_descends (prefixWord ++ tailWord_633228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633242 : List Nat := [3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_633242 : Nat := 118140960795 + 633242 * 2 ^ 59
def prefixEnd_633242 : Nat := 4983230072969 + 3 ^ 40 * 633242 * 2
def baseEnd_633242 : Nat := 96342967885782717470453

theorem tailTrace_633242 : CollatzResearch.WordTrace tailWord_633242 prefixEnd_633242 96342967885782717470453 := by
  unfold tailWord_633242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774058292969964492129495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15397488781253238645678653 5774058292969964492129495)
  ·
    refine ⟨8661087439454946738194243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774058292969964492129495 8661087439454946738194243)
    ·
      refine ⟨12991631159182420107291365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8661087439454946738194243 12991631159182420107291365)
      ·
        refine ⟨2435930842346703770117131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12991631159182420107291365 2435930842346703770117131)
        ·
          refine ⟨3653896263520055655175697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435930842346703770117131 3653896263520055655175697)
          ·
            refine ⟨2740422197640041741381773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3653896263520055655175697 2740422197640041741381773)
            ·
              refine ⟨1027658324115015653018165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2740422197640041741381773 1027658324115015653018165)
              ·
                refine ⟨96342967885782717470453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1027658324115015653018165 96342967885782717470453)
                ·
                  rfl

theorem cell20_633242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_633242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633242 prefixEnd_633242 := by exact prefixLift 633242
  have htrace : WordTrace (prefixWord ++ tailWord_633242) baseStart_633242 baseEnd_633242 := by
    simpa [prefixWord, tailWord_633242, baseEnd_633242] using wordTrace_append hprefix tailTrace_633242
  have hstable : (prefixWord ++ tailWord_633242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633242).length < 2 ^ (prefixWord ++ tailWord_633242).sum := by decide
  have hdescent : baseEnd_633242 < baseStart_633242 := by decide
  rcases family_descends (prefixWord ++ tailWord_633242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633269 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 2]
def baseStart_633269 : Nat := 118140960795 + 633269 * 2 ^ 59
def prefixEnd_633269 : Nat := 4983230072969 + 3 ^ 40 * 633269 * 2
def baseEnd_633269 : Nat := 289041227193056058511249

theorem tailTrace_633269 : CollatzResearch.WordTrace tailWord_633269 prefixEnd_633269 289041227193056058511249 := by
  unfold tailWord_633269
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097217942782041579750861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15398145295188027719833907 23097217942782041579750861)
  ·
    refine ⟨8661456728543265592406573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23097217942782041579750861 8661456728543265592406573)
    ·
      refine ⟨3248046273203724597152465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8661456728543265592406573 3248046273203724597152465)
      ·
        refine ⟨2436034704902793447864349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248046273203724597152465 2436034704902793447864349)
        ·
          refine ⟨913513014338547542949131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2436034704902793447864349 913513014338547542949131)
          ·
            refine ⟨1370269521507821314423697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913513014338547542949131 1370269521507821314423697)
            ·
              refine ⟨1027702141130865985817773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370269521507821314423697 1027702141130865985817773)
              ·
                refine ⟨385388302924074744681665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027702141130865985817773 385388302924074744681665)
                ·
                  refine ⟨289041227193056058511249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385388302924074744681665 289041227193056058511249)
                  ·
                    rfl

theorem cell20_633269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_633269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633269 prefixEnd_633269 := by exact prefixLift 633269
  have htrace : WordTrace (prefixWord ++ tailWord_633269) baseStart_633269 baseEnd_633269 := by
    simpa [prefixWord, tailWord_633269, baseEnd_633269] using wordTrace_append hprefix tailTrace_633269
  have hstable : (prefixWord ++ tailWord_633269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633269).length < 2 ^ (prefixWord ++ tailWord_633269).sum := by decide
  have hdescent : baseEnd_633269 < baseStart_633269 := by decide
  rcases family_descends (prefixWord ++ tailWord_633269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633287 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_633287 : Nat := 118140960795 + 633287 * 2 ^ 59
def prefixEnd_633287 : Nat := 4983230072969 + 3 ^ 40 * 633287 * 2
def baseEnd_633287 : Nat := 289049442883527995911175

theorem tailTrace_633287 : CollatzResearch.WordTrace tailWord_633287 prefixEnd_633287 289049442883527995911175 := by
  unfold tailWord_633287
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097874456716830653906115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15398582971144553769270743 23097874456716830653906115)
  ·
    refine ⟨34646811685075245980859173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23097874456716830653906115 34646811685075245980859173)
    ·
      refine ⟨6496277190951608621411095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34646811685075245980859173 6496277190951608621411095)
      ·
        refine ⟨9744415786427412932116643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496277190951608621411095 9744415786427412932116643)
        ·
          refine ⟨14616623679641119398174965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9744415786427412932116643 14616623679641119398174965)
          ·
            refine ⟨1370308469966354943578903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14616623679641119398174965 1370308469966354943578903)
            ·
              refine ⟨2055462704949532415368355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370308469966354943578903 2055462704949532415368355)
              ·
                refine ⟨3083194057424298623052533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055462704949532415368355 3083194057424298623052533)
                ·
                  refine ⟨289049442883527995911175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083194057424298623052533 289049442883527995911175)
                  ·
                    rfl

theorem cell20_633287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_633287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633287 prefixEnd_633287 := by exact prefixLift 633287
  have htrace : WordTrace (prefixWord ++ tailWord_633287) baseStart_633287 baseEnd_633287 := by
    simpa [prefixWord, tailWord_633287, baseEnd_633287] using wordTrace_append hprefix tailTrace_633287
  have hstable : (prefixWord ++ tailWord_633287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633287).length < 2 ^ (prefixWord ++ tailWord_633287).sum := by decide
  have hdescent : baseEnd_633287 < baseStart_633287 := by decide
  rcases family_descends (prefixWord ++ tailWord_633287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633314 : List Nat := [3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_633314 : Nat := 118140960795 + 633314 * 2 ^ 59
def prefixEnd_633314 : Nat := 4983230072969 + 3 ^ 40 * 633314 * 2
def baseEnd_633314 : Nat := 96353922139745300670355

theorem tailTrace_633314 : CollatzResearch.WordTrace tailWord_633314 prefixEnd_633314 96353922139745300670355 := by
  unfold tailWord_633314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774714806904753566284749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15399239485079342843425997 5774714806904753566284749)
  ·
    refine ⟨2165518052589282587356781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5774714806904753566284749 2165518052589282587356781)
    ·
      refine ⟨812069269720980970258793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2165518052589282587356781 812069269720980970258793)
      ·
        refine ⟨609051952290735727694095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812069269720980970258793 609051952290735727694095)
        ·
          refine ⟨913577928436103591541143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609051952290735727694095 913577928436103591541143)
          ·
            refine ⟨1370366892654155387311715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913577928436103591541143 1370366892654155387311715)
            ·
              refine ⟨2055550338981233080967573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370366892654155387311715 2055550338981233080967573)
              ·
                refine ⟨96353922139745300670355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2055550338981233080967573 96353922139745300670355)
                ·
                  rfl

theorem cell20_633314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_633314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633314 prefixEnd_633314 := by exact prefixLift 633314
  have htrace : WordTrace (prefixWord ++ tailWord_633314) baseStart_633314 baseEnd_633314 := by
    simpa [prefixWord, tailWord_633314, baseEnd_633314] using wordTrace_append hprefix tailTrace_633314
  have hstable : (prefixWord ++ tailWord_633314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633314).length < 2 ^ (prefixWord ++ tailWord_633314).sum := by decide
  have hdescent : baseEnd_633314 < baseStart_633314 := by decide
  rcases family_descends (prefixWord ++ tailWord_633314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633345 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 2]
def baseStart_633345 : Nat := 118140960795 + 633345 * 2 ^ 59
def prefixEnd_633345 : Nat := 4983230072969 + 3 ^ 40 * 633345 * 2
def baseEnd_633345 : Nat := 289075915663937571977605

theorem tailTrace_633345 : CollatzResearch.WordTrace tailWord_633345 prefixEnd_633345 289075915663937571977605 := by
  unfold tailWord_633345
  simp only [CollatzResearch.WordTrace]
  refine ⟨23099989890506706559517489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15399993260337804373011659 23099989890506706559517489)
  ·
    refine ⟨17324992417880029919638117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23099989890506706559517489 17324992417880029919638117)
    ·
      refine ⟨3248436078352505609932147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17324992417880029919638117 3248436078352505609932147)
      ·
        refine ⟨4872654117528758414898221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248436078352505609932147 4872654117528758414898221)
        ·
          refine ⟨1827245294073284405586833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4872654117528758414898221 1827245294073284405586833)
          ·
            refine ⟨1370433970554963304190125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827245294073284405586833 1370433970554963304190125)
            ·
              refine ⟨513912738958111239071297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1370433970554963304190125 513912738958111239071297)
              ·
                refine ⟨385434554218583429303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513912738958111239071297 385434554218583429303473)
                ·
                  refine ⟨289075915663937571977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385434554218583429303473 289075915663937571977605)
                  ·
                    rfl

theorem cell20_633345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_633345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633345 prefixEnd_633345 := by exact prefixLift 633345
  have htrace : WordTrace (prefixWord ++ tailWord_633345) baseStart_633345 baseEnd_633345 := by
    simpa [prefixWord, tailWord_633345, baseEnd_633345] using wordTrace_append hprefix tailTrace_633345
  have hstable : (prefixWord ++ tailWord_633345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633345).length < 2 ^ (prefixWord ++ tailWord_633345).sum := by decide
  have hdescent : baseEnd_633345 < baseStart_633345 := by decide
  rcases family_descends (prefixWord ++ tailWord_633345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633349 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 2]
def baseStart_633349 : Nat := 118140960795 + 633349 * 2 ^ 59
def prefixEnd_633349 : Nat := 4983230072969 + 3 ^ 40 * 633349 * 2
def baseEnd_633349 : Nat := 289077741372931335844255

theorem tailTrace_633349 : CollatzResearch.WordTrace tailWord_633349 prefixEnd_633349 289077741372931335844255 := by
  unfold tailWord_633349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100135782492215242663101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400090521661476828442067 23100135782492215242663101)
  ·
    refine ⟨8662550918434580715998663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23100135782492215242663101 8662550918434580715998663)
    ·
      refine ⟨12993826377651871073997995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662550918434580715998663 12993826377651871073997995)
      ·
        refine ⟨19490739566477806610996993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12993826377651871073997995 19490739566477806610996993)
        ·
          refine ⟨14618054674858354958247745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19490739566477806610996993 14618054674858354958247745)
          ·
            refine ⟨10963541006143766218685809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14618054674858354958247745 10963541006143766218685809)
            ·
              refine ⟨8222655754607824664014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10963541006143766218685809 8222655754607824664014357)
              ·
                refine ⟨385436988497241781125673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8222655754607824664014357 385436988497241781125673)
                ·
                  refine ⟨289077741372931335844255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385436988497241781125673 289077741372931335844255)
                  ·
                    rfl

theorem cell20_633349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_633349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633349 prefixEnd_633349 := by exact prefixLift 633349
  have htrace : WordTrace (prefixWord ++ tailWord_633349) baseStart_633349 baseEnd_633349 := by
    simpa [prefixWord, tailWord_633349, baseEnd_633349] using wordTrace_append hprefix tailTrace_633349
  have hstable : (prefixWord ++ tailWord_633349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633349).length < 2 ^ (prefixWord ++ tailWord_633349).sum := by decide
  have hdescent : baseEnd_633349 < baseStart_633349 := by decide
  rcases family_descends (prefixWord ++ tailWord_633349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633356 : List Nat := [2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_633356 : Nat := 118140960795 + 633356 * 2 ^ 59
def prefixEnd_633356 : Nat := 4983230072969 + 3 ^ 40 * 633356 * 2
def baseEnd_633356 : Nat := 96360312121223474203631

theorem tailTrace_633356 : CollatzResearch.WordTrace tailWord_633356 prefixEnd_633356 96360312121223474203631 := by
  unfold tailWord_633356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550195546733427719083961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15400260728977903625445281 11550195546733427719083961)
  ·
    refine ⟨8662646660050070789312971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11550195546733427719083961 8662646660050070789312971)
    ·
      refine ⟨12993969990075106183969457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662646660050070789312971 12993969990075106183969457)
      ·
        refine ⟨9745477492556329637977093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12993969990075106183969457 9745477492556329637977093)
        ·
          refine ⟨1827277029854311807120705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9745477492556329637977093 1827277029854311807120705)
          ·
            refine ⟨1370457772390733855340529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827277029854311807120705 1370457772390733855340529)
            ·
              refine ⟨1027843329293050391505397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370457772390733855340529 1027843329293050391505397)
              ·
                refine ⟨96360312121223474203631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1027843329293050391505397 96360312121223474203631)
                ·
                  rfl

theorem cell20_633356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_633356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633356 prefixEnd_633356 := by exact prefixLift 633356
  have htrace : WordTrace (prefixWord ++ tailWord_633356) baseStart_633356 baseEnd_633356 := by
    simpa [prefixWord, tailWord_633356, baseEnd_633356] using wordTrace_append hprefix tailTrace_633356
  have hstable : (prefixWord ++ tailWord_633356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633356).length < 2 ^ (prefixWord ++ tailWord_633356).sum := by decide
  have hdescent : baseEnd_633356 < baseStart_633356 := by decide
  rcases family_descends (prefixWord ++ tailWord_633356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633363 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_633363 : Nat := 118140960795 + 633363 * 2 ^ 59
def prefixEnd_633363 : Nat := 4983230072969 + 3 ^ 40 * 633363 * 2
def baseEnd_633363 : Nat := 289084131354409509377531

theorem tailTrace_633363 : CollatzResearch.WordTrace tailWord_633363 prefixEnd_633363 289084131354409509377531 := by
  unfold tailWord_633363
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100646404441495633672743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400430936294330422448495 23100646404441495633672743)
  ·
    refine ⟨34650969606662243450509115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23100646404441495633672743 34650969606662243450509115)
    ·
      refine ⟨51976454409993365175763673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34650969606662243450509115 51976454409993365175763673)
      ·
        refine ⟨38982340807495023881822755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51976454409993365175763673 38982340807495023881822755)
        ·
          refine ⟨58473511211242535822734133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38982340807495023881822755 58473511211242535822734133)
          ·
            refine ⟨5481891676053987733381325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58473511211242535822734133 5481891676053987733381325)
            ·
              refine ⟨2055709378520245400017997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5481891676053987733381325 2055709378520245400017997)
              ·
                refine ⟨770891016945092025006749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055709378520245400017997 770891016945092025006749)
                ·
                  refine ⟨289084131354409509377531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770891016945092025006749 289084131354409509377531)
                  ·
                    rfl

theorem cell20_633363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_633363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633363 prefixEnd_633363 := by exact prefixLift 633363
  have htrace : WordTrace (prefixWord ++ tailWord_633363) baseStart_633363 baseEnd_633363 := by
    simpa [prefixWord, tailWord_633363, baseEnd_633363] using wordTrace_append hprefix tailTrace_633363
  have hstable : (prefixWord ++ tailWord_633363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633363).length < 2 ^ (prefixWord ++ tailWord_633363).sum := by decide
  have hdescent : baseEnd_633363 < baseStart_633363 := by decide
  rcases family_descends (prefixWord ++ tailWord_633363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633370 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_633370 : Nat := 118140960795 + 633370 * 2 ^ 59
def prefixEnd_633370 : Nat := 4983230072969 + 3 ^ 40 * 633370 * 2
def baseEnd_633370 : Nat := 289087326345148596144169

theorem tailTrace_633370 : CollatzResearch.WordTrace tailWord_633370 prefixEnd_633370 289087326345148596144169 := by
  unfold tailWord_633370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775225428854033957294391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15400601143610757219451709 5775225428854033957294391)
  ·
    refine ⟨8662838143281050935941587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775225428854033957294391 8662838143281050935941587)
    ·
      refine ⟨12994257214921576403912381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662838143281050935941587 12994257214921576403912381)
      ·
        refine ⟨4872846455595591151467143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12994257214921576403912381 4872846455595591151467143)
        ·
          refine ⟨7309269683393386727200715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872846455595591151467143 7309269683393386727200715)
          ·
            refine ⟨10963904525090080090801073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309269683393386727200715 10963904525090080090801073)
            ·
              refine ⟨8222928393817560068100805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10963904525090080090801073 8222928393817560068100805)
              ·
                refine ⟨1541799073840792512768901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8222928393817560068100805 1541799073840792512768901)
                ·
                  refine ⟨289087326345148596144169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541799073840792512768901 289087326345148596144169)
                  ·
                    rfl

theorem cell20_633370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_633370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633370 prefixEnd_633370 := by exact prefixLift 633370
  have htrace : WordTrace (prefixWord ++ tailWord_633370) baseStart_633370 baseEnd_633370 := by
    simpa [prefixWord, tailWord_633370, baseEnd_633370] using wordTrace_append hprefix tailTrace_633370
  have hstable : (prefixWord ++ tailWord_633370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633370).length < 2 ^ (prefixWord ++ tailWord_633370).sum := by decide
  have hdescent : baseEnd_633370 < baseStart_633370 := by decide
  rcases family_descends (prefixWord ++ tailWord_633370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633377 : List Nat := [1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_633377 : Nat := 118140960795 + 633377 * 2 ^ 59
def prefixEnd_633377 : Nat := 4983230072969 + 3 ^ 40 * 633377 * 2
def baseEnd_633377 : Nat := 96363507111962560970269

theorem tailTrace_633377 : CollatzResearch.WordTrace tailWord_633377 prefixEnd_633377 96363507111962560970269 := by
  unfold tailWord_633377
  simp only [CollatzResearch.WordTrace]
  refine ⟨23101157026390776024682385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400771350927184016454923 23101157026390776024682385)
  ·
    refine ⟨17325867769793082018511789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23101157026390776024682385 17325867769793082018511789)
    ·
      refine ⟨6497200413672405756941921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17325867769793082018511789 6497200413672405756941921)
      ·
        refine ⟨4872900310254304317706441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497200413672405756941921 4872900310254304317706441)
        ·
          refine ⟨3654675232690728238279831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872900310254304317706441 3654675232690728238279831)
          ·
            refine ⟨5482012849036092357419747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654675232690728238279831 5482012849036092357419747)
            ·
              refine ⟨8223019273554138536129621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482012849036092357419747 8223019273554138536129621)
              ·
                refine ⟨96363507111962560970269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8223019273554138536129621 96363507111962560970269)
                ·
                  rfl

theorem cell20_633377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_633377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633377 prefixEnd_633377 := by exact prefixLift 633377
  have htrace : WordTrace (prefixWord ++ tailWord_633377) baseStart_633377 baseEnd_633377 := by
    simpa [prefixWord, tailWord_633377, baseEnd_633377] using wordTrace_append hprefix tailTrace_633377
  have hstable : (prefixWord ++ tailWord_633377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633377).length < 2 ^ (prefixWord ++ tailWord_633377).sum := by decide
  have hdescent : baseEnd_633377 < baseStart_633377 := by decide
  rcases family_descends (prefixWord ++ tailWord_633377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633396 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_633396 : Nat := 118140960795 + 633396 * 2 ^ 59
def prefixEnd_633396 : Nat := 4983230072969 + 3 ^ 40 * 633396 * 2
def baseEnd_633396 : Nat := 289099193453608061277397

theorem tailTrace_633396 : CollatzResearch.WordTrace tailWord_633396 prefixEnd_633396 289099193453608061277397 := by
  unfold tailWord_633396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550925006660971134812021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15401233342214628179749361 11550925006660971134812021)
  ·
    refine ⟨1082899219374466043888627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11550925006660971134812021 1082899219374466043888627)
    ·
      refine ⟨1624348829061699065832941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082899219374466043888627 1624348829061699065832941)
      ·
        refine ⟨609130810898137149687353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1624348829061699065832941 609130810898137149687353)
        ·
          refine ⟨456848108173602862265515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609130810898137149687353 456848108173602862265515)
          ·
            refine ⟨685272162260404293398273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456848108173602862265515 685272162260404293398273)
            ·
              refine ⟨513954121695303220048705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685272162260404293398273 513954121695303220048705)
              ·
                refine ⟨385465591271477415036529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513954121695303220048705 385465591271477415036529)
                ·
                  refine ⟨289099193453608061277397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385465591271477415036529 289099193453608061277397)
                  ·
                    rfl

theorem cell20_633396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_633396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633396 prefixEnd_633396 := by exact prefixLift 633396
  have htrace : WordTrace (prefixWord ++ tailWord_633396) baseStart_633396 baseEnd_633396 := by
    simpa [prefixWord, tailWord_633396, baseEnd_633396] using wordTrace_append hprefix tailTrace_633396
  have hstable : (prefixWord ++ tailWord_633396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633396).length < 2 ^ (prefixWord ++ tailWord_633396).sum := by decide
  have hdescent : baseEnd_633396 < baseStart_633396 := by decide
  rcases family_descends (prefixWord ++ tailWord_633396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633404 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_633404 : Nat := 118140960795 + 633404 * 2 ^ 59
def prefixEnd_633404 : Nat := 4983230072969 + 3 ^ 40 * 633404 * 2
def baseEnd_633404 : Nat := 289102844871595589010697

theorem tailTrace_633404 : CollatzResearch.WordTrace tailWord_633404 prefixEnd_633404 289102844871595589010697 := by
  unfold tailWord_633404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11551070898646479817957633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15401427864861973090610177 11551070898646479817957633)
  ·
    refine ⟨8663303173984859863468225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11551070898646479817957633 8663303173984859863468225)
    ·
      refine ⟨6497477380488644897601169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8663303173984859863468225 6497477380488644897601169)
      ·
        refine ⟨4873108035366483673200877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497477380488644897601169 4873108035366483673200877)
        ·
          refine ⟨1827415513262431377450329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4873108035366483673200877 1827415513262431377450329)
          ·
            refine ⟨1370561634946823533087747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827415513262431377450329 1370561634946823533087747)
            ·
              refine ⟨2055842452420235299631621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370561634946823533087747 2055842452420235299631621)
              ·
                refine ⟨385470459828794118680929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2055842452420235299631621 385470459828794118680929)
                ·
                  refine ⟨289102844871595589010697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385470459828794118680929 289102844871595589010697)
                  ·
                    rfl

theorem cell20_633404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_633404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633404 prefixEnd_633404 := by exact prefixLift 633404
  have htrace : WordTrace (prefixWord ++ tailWord_633404) baseStart_633404 baseEnd_633404 := by
    simpa [prefixWord, tailWord_633404, baseEnd_633404] using wordTrace_append hprefix tailTrace_633404
  have hstable : (prefixWord ++ tailWord_633404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633404).length < 2 ^ (prefixWord ++ tailWord_633404).sum := by decide
  have hdescent : baseEnd_633404 < baseStart_633404 := by decide
  rcases family_descends (prefixWord ++ tailWord_633404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633463 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 2]
def baseStart_633463 : Nat := 118140960795 + 633463 * 2 ^ 59
def prefixEnd_633463 : Nat := 4983230072969 + 3 ^ 40 * 633463 * 2
def baseEnd_633463 : Nat := 289129774079253606043789

theorem tailTrace_633463 : CollatzResearch.WordTrace tailWord_633463 prefixEnd_633463 289129774079253606043789 := by
  unfold tailWord_633463
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104293704079212712313043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15402862469386141808208695 23104293704079212712313043)
  ·
    refine ⟨34656440556118819068469565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23104293704079212712313043 34656440556118819068469565)
    ·
      refine ⟨12996165208544557150676087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34656440556118819068469565 12996165208544557150676087)
      ·
        refine ⟨19494247812816835726014131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12996165208544557150676087 19494247812816835726014131)
        ·
          refine ⟨29241371719225253589021197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19494247812816835726014131 29241371719225253589021197)
          ·
            refine ⟨10965514394709470095882949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29241371719225253589021197 10965514394709470095882949)
            ·
              refine ⟨2056033949008025642978053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10965514394709470095882949 2056033949008025642978053)
              ·
                refine ⟨385506365439004808058385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2056033949008025642978053 385506365439004808058385)
                ·
                  refine ⟨289129774079253606043789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385506365439004808058385 289129774079253606043789)
                  ·
                    rfl

theorem cell20_633463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2].length) (baseStart_633463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633463 prefixEnd_633463 := by exact prefixLift 633463
  have htrace : WordTrace (prefixWord ++ tailWord_633463) baseStart_633463 baseEnd_633463 := by
    simpa [prefixWord, tailWord_633463, baseEnd_633463] using wordTrace_append hprefix tailTrace_633463
  have hstable : (prefixWord ++ tailWord_633463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633463).length < 2 ^ (prefixWord ++ tailWord_633463).sum := by decide
  have hdescent : baseEnd_633463 < baseStart_633463 := by decide
  rcases family_descends (prefixWord ++ tailWord_633463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633514 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_633514 : Nat := 118140960795 + 633514 * 2 ^ 59
def prefixEnd_633514 : Nat := 4983230072969 + 3 ^ 40 * 633514 * 2
def baseEnd_633514 : Nat := 289153051868924095343581

theorem tailTrace_633514 : CollatzResearch.WordTrace tailWord_633514 prefixEnd_633514 289153051868924095343581 := by
  unfold tailWord_633514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776538456723612105604899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15404102551262965614946397 5776538456723612105604899)
  ·
    refine ⟨8664807685085418158407349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5776538456723612105604899 8664807685085418158407349)
    ·
      refine ⟨812325720476757952350689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8664807685085418158407349 812325720476757952350689)
      ·
        refine ⟨609244290357568464263017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812325720476757952350689 609244290357568464263017)
        ·
          refine ⟨456933217768176348197263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609244290357568464263017 456933217768176348197263)
          ·
            refine ⟨685399826652264522295895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456933217768176348197263 685399826652264522295895)
            ·
              refine ⟨1028099739978396783443843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685399826652264522295895 1028099739978396783443843)
              ·
                refine ⟨1542149609967595175165765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028099739978396783443843 1542149609967595175165765)
                ·
                  refine ⟨289153051868924095343581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542149609967595175165765 289153051868924095343581)
                  ·
                    rfl

theorem cell20_633514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_633514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633514 prefixEnd_633514 := by exact prefixLift 633514
  have htrace : WordTrace (prefixWord ++ tailWord_633514) baseStart_633514 baseEnd_633514 := by
    simpa [prefixWord, tailWord_633514, baseEnd_633514] using wordTrace_append hprefix tailTrace_633514
  have hstable : (prefixWord ++ tailWord_633514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633514).length < 2 ^ (prefixWord ++ tailWord_633514).sum := by decide
  have hdescent : baseEnd_633514 < baseStart_633514 := by decide
  rcases family_descends (prefixWord ++ tailWord_633514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633518 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_633518 : Nat := 118140960795 + 633518 * 2 ^ 59
def prefixEnd_633518 : Nat := 4983230072969 + 3 ^ 40 * 633518 * 2
def baseEnd_633518 : Nat := 289154877577917859210231

theorem tailTrace_633518 : CollatzResearch.WordTrace tailWord_633518 prefixEnd_633518 289154877577917859210231 := by
  unfold tailWord_633518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888287464859994638195651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15404199812586638070376805 2888287464859994638195651)
  ·
    refine ⟨4332431197289991957293477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2888287464859994638195651 4332431197289991957293477)
    ·
      refine ⟨812330849491873491992527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4332431197289991957293477 812330849491873491992527)
      ·
        refine ⟨1218496274237810237988791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812330849491873491992527 1218496274237810237988791)
        ·
          refine ⟨1827744411356715356983187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218496274237810237988791 1827744411356715356983187)
          ·
            refine ⟨2741616617035073035474781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827744411356715356983187 2741616617035073035474781)
            ·
              refine ⟨1028106231388152388303043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2741616617035073035474781 1028106231388152388303043)
              ·
                refine ⟨1542159347082228582454565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028106231388152388303043 1542159347082228582454565)
                ·
                  refine ⟨289154877577917859210231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542159347082228582454565 289154877577917859210231)
                  ·
                    rfl

theorem cell20_633518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_633518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633518 prefixEnd_633518 := by exact prefixLift 633518
  have htrace : WordTrace (prefixWord ++ tailWord_633518) baseStart_633518 baseEnd_633518 := by
    simpa [prefixWord, tailWord_633518, baseEnd_633518] using wordTrace_append hprefix tailTrace_633518
  have hstable : (prefixWord ++ tailWord_633518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633518).length < 2 ^ (prefixWord ++ tailWord_633518).sum := by decide
  have hdescent : baseEnd_633518 < baseStart_633518 := by decide
  rcases family_descends (prefixWord ++ tailWord_633518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633573 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 2]
def baseStart_633573 : Nat := 118140960795 + 633573 * 2 ^ 59
def prefixEnd_633573 : Nat := 4983230072969 + 3 ^ 40 * 633573 * 2
def baseEnd_633573 : Nat := 289179981076582112376673

theorem tailTrace_633573 : CollatzResearch.WordTrace tailWord_633573 prefixEnd_633573 289179981076582112376673 := by
  unfold tailWord_633573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108305733680701498817373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15405537155787134332544915 23108305733680701498817373)
  ·
    refine ⟨8665614650130263062056515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23108305733680701498817373 8665614650130263062056515)
    ·
      refine ⟨12998421975195394593084773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665614650130263062056515 12998421975195394593084773)
      ·
        refine ⟨2437204120349136486203395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12998421975195394593084773 2437204120349136486203395)
        ·
          refine ⟨3655806180523704729305093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437204120349136486203395 3655806180523704729305093)
          ·
            refine ⟨685463658848194636744705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3655806180523704729305093 685463658848194636744705)
            ·
              refine ⟨514097744136145977558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685463658848194636744705 514097744136145977558529)
              ·
                refine ⟨385573308102109483168897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514097744136145977558529 385573308102109483168897)
                ·
                  refine ⟨289179981076582112376673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385573308102109483168897 289179981076582112376673)
                  ·
                    rfl

theorem cell20_633573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_633573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633573 prefixEnd_633573 := by exact prefixLift 633573
  have htrace : WordTrace (prefixWord ++ tailWord_633573) baseStart_633573 baseEnd_633573 := by
    simpa [prefixWord, tailWord_633573, baseEnd_633573] using wordTrace_append hprefix tailTrace_633573
  have hstable : (prefixWord ++ tailWord_633573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633573).length < 2 ^ (prefixWord ++ tailWord_633573).sum := by decide
  have hdescent : baseEnd_633573 < baseStart_633573 := by decide
  rcases family_descends (prefixWord ++ tailWord_633573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633612 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_633612 : Nat := 118140960795 + 633612 * 2 ^ 59
def prefixEnd_633612 : Nat := 4983230072969 + 3 ^ 40 * 633612 * 2
def baseEnd_633612 : Nat := 289197781739271310076513

theorem tailTrace_633612 : CollatzResearch.WordTrace tailWord_633612 prefixEnd_633612 289197781739271310076513 := by
  unfold tailWord_633612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554864090269705579743545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15406485453692940772991393 11554864090269705579743545)
  ·
    refine ⟨8666148067702279184807659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11554864090269705579743545 8666148067702279184807659)
    ·
      refine ⟨12999222101553418777211489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8666148067702279184807659 12999222101553418777211489)
      ·
        refine ⟨9749416576165064082908617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12999222101553418777211489 9749416576165064082908617)
        ·
          refine ⟨7312062432123798062181463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9749416576165064082908617 7312062432123798062181463)
          ·
            refine ⟨10968093648185697093272195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312062432123798062181463 10968093648185697093272195)
            ·
              refine ⟨16452140472278545639908293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968093648185697093272195 16452140472278545639908293)
              ·
                refine ⟨3084776338552227307482805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16452140472278545639908293 3084776338552227307482805)
                ·
                  refine ⟨289197781739271310076513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3084776338552227307482805 289197781739271310076513)
                  ·
                    rfl

theorem cell20_633612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_633612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633612 prefixEnd_633612 := by exact prefixLift 633612
  have htrace : WordTrace (prefixWord ++ tailWord_633612) baseStart_633612 baseEnd_633612 := by
    simpa [prefixWord, tailWord_633612, baseEnd_633612] using wordTrace_append hprefix tailTrace_633612
  have hstable : (prefixWord ++ tailWord_633612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633612).length < 2 ^ (prefixWord ++ tailWord_633612).sum := by decide
  have hdescent : baseEnd_633612 < baseStart_633612 := by decide
  rcases family_descends (prefixWord ++ tailWord_633612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633615 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 2]
def baseStart_633615 : Nat := 118140960795 + 633615 * 2 ^ 59
def prefixEnd_633615 : Nat := 4983230072969 + 3 ^ 40 * 633615 * 2
def baseEnd_633615 : Nat := 289199151021016632976501

theorem tailTrace_633615 : CollatzResearch.WordTrace tailWord_633615 prefixEnd_633615 289199151021016632976501 := by
  unfold tailWord_633615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23109837599528542671846299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15406558399685695114564199 23109837599528542671846299)
  ·
    refine ⟨34664756399292814007769449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23109837599528542671846299 34664756399292814007769449)
    ·
      refine ⟨25998567299469610505827087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34664756399292814007769449 25998567299469610505827087)
      ·
        refine ⟨38997850949204415758740631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25998567299469610505827087 38997850949204415758740631)
        ·
          refine ⟨58496776423806623638110947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38997850949204415758740631 58496776423806623638110947)
          ·
            refine ⟨87745164635709935457166421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58496776423806623638110947 87745164635709935457166421)
            ·
              refine ⟨1028263648074725806138669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 87745164635709935457166421 1028263648074725806138669)
              ·
                refine ⟨385598868028022177302001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028263648074725806138669 385598868028022177302001)
                ·
                  refine ⟨289199151021016632976501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385598868028022177302001 289199151021016632976501)
                  ·
                    rfl

theorem cell20_633615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2].length) (baseStart_633615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633615 prefixEnd_633615 := by exact prefixLift 633615
  have htrace : WordTrace (prefixWord ++ tailWord_633615) baseStart_633615 baseEnd_633615 := by
    simpa [prefixWord, tailWord_633615, baseEnd_633615] using wordTrace_append hprefix tailTrace_633615
  have hstable : (prefixWord ++ tailWord_633615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633615).length < 2 ^ (prefixWord ++ tailWord_633615).sum := by decide
  have hdescent : baseEnd_633615 < baseStart_633615 := by decide
  rcases family_descends (prefixWord ++ tailWord_633615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633619 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_633619 : Nat := 118140960795 + 633619 * 2 ^ 59
def prefixEnd_633619 : Nat := 4983230072969 + 3 ^ 40 * 633619 * 2
def baseEnd_633619 : Nat := 289200976730010396843151

theorem tailTrace_633619 : CollatzResearch.WordTrace tailWord_633619 prefixEnd_633619 289200976730010396843151 := by
  unfold tailWord_633619
  simp only [CollatzResearch.WordTrace]
  refine ⟨23109983491514051354991911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15406655661009367569994607 23109983491514051354991911)
  ·
    refine ⟨34664975237271077032487867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23109983491514051354991911 34664975237271077032487867)
    ·
      refine ⟨51997462855906615548731801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34664975237271077032487867 51997462855906615548731801)
      ·
        refine ⟨38998097141929961661548851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51997462855906615548731801 38998097141929961661548851)
        ·
          refine ⟨58497145712894942492323277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38998097141929961661548851 58497145712894942492323277)
          ·
            refine ⟨21936429642335603434621229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58497145712894942492323277 21936429642335603434621229)
            ·
              refine ⟨8226161115875851287982961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21936429642335603434621229 8226161115875851287982961)
              ·
                refine ⟨6169620836906888465987221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226161115875851287982961 6169620836906888465987221)
                ·
                  refine ⟨289200976730010396843151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169620836906888465987221 289200976730010396843151)
                  ·
                    rfl

theorem cell20_633619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_633619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633619 prefixEnd_633619 := by exact prefixLift 633619
  have htrace : WordTrace (prefixWord ++ tailWord_633619) baseStart_633619 baseEnd_633619 := by
    simpa [prefixWord, tailWord_633619, baseEnd_633619] using wordTrace_append hprefix tailTrace_633619
  have hstable : (prefixWord ++ tailWord_633619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633619).length < 2 ^ (prefixWord ++ tailWord_633619).sum := by decide
  have hdescent : baseEnd_633619 < baseStart_633619 := by decide
  rcases family_descends (prefixWord ++ tailWord_633619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633642 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_633642 : Nat := 118140960795 + 633642 * 2 ^ 59
def prefixEnd_633642 : Nat := 4983230072969 + 3 ^ 40 * 633642 * 2
def baseEnd_633642 : Nat := 289211474556724539076391

theorem tailTrace_633642 : CollatzResearch.WordTrace tailWord_633642 prefixEnd_633642 289211474556724539076391 := by
  unfold tailWord_633642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777705592607681570769795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15407214913620484188719453 5777705592607681570769795)
  ·
    refine ⟨8666558388911522356154693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5777705592607681570769795 8666558388911522356154693)
    ·
      refine ⟨1624979697920910441779005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8666558388911522356154693 1624979697920910441779005)
      ·
        refine ⟨609367386720341415667127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1624979697920910441779005 609367386720341415667127)
        ·
          refine ⟨914051080080512123500691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609367386720341415667127 914051080080512123500691)
          ·
            refine ⟨1371076620120768185251037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914051080080512123500691 1371076620120768185251037)
            ·
              refine ⟨514153732545288069469139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371076620120768185251037 514153732545288069469139)
              ·
                refine ⟨771230598817932104203709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514153732545288069469139 771230598817932104203709)
                ·
                  refine ⟨289211474556724539076391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771230598817932104203709 289211474556724539076391)
                  ·
                    rfl

theorem cell20_633642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_633642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633642 prefixEnd_633642 := by exact prefixLift 633642
  have htrace : WordTrace (prefixWord ++ tailWord_633642) baseStart_633642 baseEnd_633642 := by
    simpa [prefixWord, tailWord_633642, baseEnd_633642] using wordTrace_append hprefix tailTrace_633642
  have hstable : (prefixWord ++ tailWord_633642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633642).length < 2 ^ (prefixWord ++ tailWord_633642).sum := by decide
  have hdescent : baseEnd_633642 < baseStart_633642 := by decide
  rcases family_descends (prefixWord ++ tailWord_633642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633677 : List Nat := [1, 6, 1, 2, 2, 2, 6]
def baseStart_633677 : Nat := 118140960795 + 633677 * 2 ^ 59
def prefixEnd_633677 : Nat := 4983230072969 + 3 ^ 40 * 633677 * 2
def baseEnd_633677 : Nat := 32136383278935552545509

theorem tailTrace_633677 : CollatzResearch.WordTrace tailWord_633677 prefixEnd_633677 32136383278935552545509 := by
  unfold tailWord_633677
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112098925303927260603285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15408065950202618173735523 23112098925303927260603285)
  ·
    refine ⟨1083379637123621590340779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23112098925303927260603285 1083379637123621590340779)
    ·
      refine ⟨1625069455685432385511169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083379637123621590340779 1625069455685432385511169)
      ·
        refine ⟨1218802091764074289133377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625069455685432385511169 1218802091764074289133377)
        ·
          refine ⟨914101568823055716850033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218802091764074289133377 914101568823055716850033)
          ·
            refine ⟨685576176617291787637525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914101568823055716850033 685576176617291787637525)
            ·
              refine ⟨32136383278935552545509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 685576176617291787637525 32136383278935552545509)
              ·
                rfl

theorem cell20_633677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_633677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633677 prefixEnd_633677 := by exact prefixLift 633677
  have htrace : WordTrace (prefixWord ++ tailWord_633677) baseStart_633677 baseEnd_633677 := by
    simpa [prefixWord, tailWord_633677, baseEnd_633677] using wordTrace_append hprefix tailTrace_633677
  have hstable : (prefixWord ++ tailWord_633677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633677).length < 2 ^ (prefixWord ++ tailWord_633677).sum := by decide
  have hdescent : baseEnd_633677 < baseStart_633677 := by decide
  rcases family_descends (prefixWord ++ tailWord_633677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633767 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_633767 : Nat := 118140960795 + 633767 * 2 ^ 59
def prefixEnd_633767 : Nat := 4983230072969 + 3 ^ 40 * 633767 * 2
def baseEnd_633767 : Nat := 289268527962779659909213

theorem tailTrace_633767 : CollatzResearch.WordTrace tailWord_633767 prefixEnd_633767 289268527962779659909213 := by
  unfold tailWord_633767
  simp only [CollatzResearch.WordTrace]
  refine ⟨23115381494977872631379555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15410254329985248420919703 23115381494977872631379555)
  ·
    refine ⟨34673072242466808947069333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23115381494977872631379555 34673072242466808947069333)
    ·
      refine ⟨1625300261365631669393875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34673072242466808947069333 1625300261365631669393875)
      ·
        refine ⟨2437950392048447504090813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625300261365631669393875 2437950392048447504090813)
        ·
          refine ⟨914231397018167814034055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2437950392048447504090813 914231397018167814034055)
          ·
            refine ⟨1371347095527251721051083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914231397018167814034055 1371347095527251721051083)
            ·
              refine ⟨2057020643290877581576625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371347095527251721051083 2057020643290877581576625)
              ·
                refine ⟨1542765482468158186182469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057020643290877581576625 1542765482468158186182469)
                ·
                  refine ⟨289268527962779659909213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542765482468158186182469 289268527962779659909213)
                  ·
                    rfl

theorem cell20_633767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_633767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633767 prefixEnd_633767 := by exact prefixLift 633767
  have htrace : WordTrace (prefixWord ++ tailWord_633767) baseStart_633767 baseEnd_633767 := by
    simpa [prefixWord, tailWord_633767, baseEnd_633767] using wordTrace_append hprefix tailTrace_633767
  have hstable : (prefixWord ++ tailWord_633767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633767).length < 2 ^ (prefixWord ++ tailWord_633767).sum := by decide
  have hdescent : baseEnd_633767 < baseStart_633767 := by decide
  rcases family_descends (prefixWord ++ tailWord_633767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_633771 : Nat := 118140960795 + 633771 * 2 ^ 59
def prefixEnd_633771 : Nat := 4983230072969 + 3 ^ 40 * 633771 * 2
def baseEnd_633771 : Nat := 289270353671773423775863

theorem tailTrace_633771 : CollatzResearch.WordTrace tailWord_633771 prefixEnd_633771 289270353671773423775863 := by
  unfold tailWord_633771
  simp only [CollatzResearch.WordTrace]
  refine ⟨23115527386963381314525167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15410351591308920876350111 23115527386963381314525167)
  ·
    refine ⟨34673291080445071971787751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23115527386963381314525167 34673291080445071971787751)
    ·
      refine ⟨52009936620667607957681627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34673291080445071971787751 52009936620667607957681627)
      ·
        refine ⟨78014904931001411936522441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52009936620667607957681627 78014904931001411936522441)
        ·
          refine ⟨58511178698251058952391831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78014904931001411936522441 58511178698251058952391831)
          ·
            refine ⟨87766768047376588428587747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58511178698251058952391831 87766768047376588428587747)
            ·
              refine ⟨131650152071064882642881621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87766768047376588428587747 131650152071064882642881621)
              ·
                refine ⟨1542775219582791593471269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 131650152071064882642881621 1542775219582791593471269)
                ·
                  refine ⟨289270353671773423775863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542775219582791593471269 289270353671773423775863)
                  ·
                    rfl

theorem cell20_633771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_633771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633771 prefixEnd_633771 := by exact prefixLift 633771
  have htrace : WordTrace (prefixWord ++ tailWord_633771) baseStart_633771 baseEnd_633771 := by
    simpa [prefixWord, tailWord_633771, baseEnd_633771] using wordTrace_append hprefix tailTrace_633771
  have hstable : (prefixWord ++ tailWord_633771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633771).length < 2 ^ (prefixWord ++ tailWord_633771).sum := by decide
  have hdescent : baseEnd_633771 < baseStart_633771 := by decide
  rcases family_descends (prefixWord ++ tailWord_633771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633864 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_633864 : Nat := 118140960795 + 633864 * 2 ^ 59
def prefixEnd_633864 : Nat := 4983230072969 + 3 ^ 40 * 633864 * 2
def baseEnd_633864 : Nat := 289312801405878433675483

theorem tailTrace_633864 : CollatzResearch.WordTrace tailWord_633864 prefixEnd_633864 289312801405878433675483 := by
  unfold tailWord_633864
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559459687813229098830323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15412612917084305465107097 11559459687813229098830323)
  ·
    refine ⟨17339189531719843648245485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11559459687813229098830323 17339189531719843648245485)
    ·
      refine ⟨6502196074394941368092057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17339189531719843648245485 6502196074394941368092057)
      ·
        refine ⟨4876647055796206026069043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6502196074394941368092057 4876647055796206026069043)
        ·
          refine ⟨7314970583694309039103565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876647055796206026069043 7314970583694309039103565)
          ·
            refine ⟨2743113968885365889663837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7314970583694309039103565 2743113968885365889663837)
            ·
              refine ⟨1028667738332012208623939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2743113968885365889663837 1028667738332012208623939)
              ·
                refine ⟨1543001607498018312935909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028667738332012208623939 1543001607498018312935909)
                ·
                  refine ⟨289312801405878433675483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543001607498018312935909 289312801405878433675483)
                  ·
                    rfl

theorem cell20_633864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_633864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633864 prefixEnd_633864 := by exact prefixLift 633864
  have htrace : WordTrace (prefixWord ++ tailWord_633864) baseStart_633864 baseEnd_633864 := by
    simpa [prefixWord, tailWord_633864, baseEnd_633864] using wordTrace_append hprefix tailTrace_633864
  have hstable : (prefixWord ++ tailWord_633864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633864).length < 2 ^ (prefixWord ++ tailWord_633864).sum := by decide
  have hdescent : baseEnd_633864 < baseStart_633864 := by decide
  rcases family_descends (prefixWord ++ tailWord_633864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633923 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_633923 : Nat := 118140960795 + 633923 * 2 ^ 59
def prefixEnd_633923 : Nat := 4983230072969 + 3 ^ 40 * 633923 * 2
def baseEnd_633923 : Nat := 289339730613536450708575

theorem tailTrace_633923 : CollatzResearch.WordTrace tailWord_633923 prefixEnd_633923 289339730613536450708575 := by
  unfold tailWord_633923
  simp only [CollatzResearch.WordTrace]
  refine ⟨23121071282412711274058423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15414047521608474182705615 23121071282412711274058423)
  ·
    refine ⟨34681606923619066911087635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23121071282412711274058423 34681606923619066911087635)
    ·
      refine ⟨52022410385428600366631453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34681606923619066911087635 52022410385428600366631453)
      ·
        refine ⟨19508403894535725137486795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52022410385428600366631453 19508403894535725137486795)
        ·
          refine ⟨29262605841803587706230193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19508403894535725137486795 29262605841803587706230193)
          ·
            refine ⟨21946954381352690779672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29262605841803587706230193 21946954381352690779672645)
            ·
              refine ⟨4115053946503629521188621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21946954381352690779672645 4115053946503629521188621)
              ·
                refine ⟨1543145229938861070445733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115053946503629521188621 1543145229938861070445733)
                ·
                  refine ⟨289339730613536450708575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543145229938861070445733 289339730613536450708575)
                  ·
                    rfl

theorem cell20_633923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_633923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633923 prefixEnd_633923 := by exact prefixLift 633923
  have htrace : WordTrace (prefixWord ++ tailWord_633923) baseStart_633923 baseEnd_633923 := by
    simpa [prefixWord, tailWord_633923, baseEnd_633923] using wordTrace_append hprefix tailTrace_633923
  have hstable : (prefixWord ++ tailWord_633923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633923).length < 2 ^ (prefixWord ++ tailWord_633923).sum := by decide
  have hdescent : baseEnd_633923 < baseStart_633923 := by decide
  rcases family_descends (prefixWord ++ tailWord_633923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633957 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 2]
def baseStart_633957 : Nat := 118140960795 + 633957 * 2 ^ 59
def prefixEnd_633957 : Nat := 4983230072969 + 3 ^ 40 * 633957 * 2
def baseEnd_633957 : Nat := 289355249139983443575103

theorem tailTrace_633957 : CollatzResearch.WordTrace tailWord_633957 prefixEnd_633957 289355249139983443575103 := by
  unfold tailWord_633957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23122311364289535080796125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15414874242859690053864083 23122311364289535080796125)
  ·
    refine ⟨8670866761608575655298547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23122311364289535080796125 8670866761608575655298547)
    ·
      refine ⟨13006300142412863482947821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8670866761608575655298547 13006300142412863482947821)
      ·
        refine ⟨4877362553404823806105433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13006300142412863482947821 4877362553404823806105433)
        ·
          refine ⟨3658021915053617854579075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877362553404823806105433 3658021915053617854579075)
          ·
            refine ⟨5487032872580426781868613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658021915053617854579075 5487032872580426781868613)
            ·
              refine ⟨1028818663608830021600365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5487032872580426781868613 1028818663608830021600365)
              ·
                refine ⟨385806998853311258100137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028818663608830021600365 385806998853311258100137)
                ·
                  refine ⟨289355249139983443575103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385806998853311258100137 289355249139983443575103)
                  ·
                    rfl

theorem cell20_633957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_633957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633957 prefixEnd_633957 := by exact prefixLift 633957
  have htrace : WordTrace (prefixWord ++ tailWord_633957) baseStart_633957 baseEnd_633957 := by
    simpa [prefixWord, tailWord_633957, baseEnd_633957] using wordTrace_append hprefix tailTrace_633957
  have hstable : (prefixWord ++ tailWord_633957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633957).length < 2 ^ (prefixWord ++ tailWord_633957).sum := by decide
  have hdescent : baseEnd_633957 < baseStart_633957 := by decide
  rcases family_descends (prefixWord ++ tailWord_633957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633968 : List Nat := [2, 1, 1, 1, 5, 1, 9]
def baseStart_633968 : Nat := 118140960795 + 633968 * 2 ^ 59
def prefixEnd_633968 : Nat := 4983230072969 + 3 ^ 40 * 633968 * 2
def baseEnd_633968 : Nat := 32151141093301810467599

theorem tailTrace_633968 : CollatzResearch.WordTrace tailWord_633968 prefixEnd_633968 32151141093301810467599 := by
  unfold tailWord_633968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561356283624841979723279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15415141711499789306297705 11561356283624841979723279)
  ·
    refine ⟨17342034425437262969584919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561356283624841979723279 17342034425437262969584919)
    ·
      refine ⟨26013051638155894454377379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17342034425437262969584919 26013051638155894454377379)
      ·
        refine ⟨39019577457233841681566069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26013051638155894454377379 39019577457233841681566069)
        ·
          refine ⟨3658085386615672657646819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39019577457233841681566069 3658085386615672657646819)
          ·
            refine ⟨5487128079923508986470229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658085386615672657646819 5487128079923508986470229)
            ·
              refine ⟨32151141093301810467599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5487128079923508986470229 32151141093301810467599)
              ·
                rfl

theorem cell20_633968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_633968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633968 prefixEnd_633968 := by exact prefixLift 633968
  have htrace : WordTrace (prefixWord ++ tailWord_633968) baseStart_633968 baseEnd_633968 := by
    simpa [prefixWord, tailWord_633968, baseEnd_633968] using wordTrace_append hprefix tailTrace_633968
  have hstable : (prefixWord ++ tailWord_633968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633968).length < 2 ^ (prefixWord ++ tailWord_633968).sum := by decide
  have hdescent : baseEnd_633968 < baseStart_633968 := by decide
  rcases family_descends (prefixWord ++ tailWord_633968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633988 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_633988 : Nat := 118140960795 + 633988 * 2 ^ 59
def prefixEnd_633988 : Nat := 4983230072969 + 3 ^ 40 * 633988 * 2
def baseEnd_633988 : Nat := 289369398384685113541643

theorem tailTrace_633988 : CollatzResearch.WordTrace tailWord_633988 prefixEnd_633988 289369398384685113541643 := by
  unfold tailWord_633988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561721013588613687587309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15415628018118151583449745 11561721013588613687587309)
  ·
    refine ⟨4335645380095730132845241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11561721013588613687587309 4335645380095730132845241)
    ·
      refine ⟨3251734035071797599633931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4335645380095730132845241 3251734035071797599633931)
      ·
        refine ⟨4877601052607696399450897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251734035071797599633931 4877601052607696399450897)
        ·
          refine ⟨3658200789455772299588173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877601052607696399450897 3658200789455772299588173)
          ·
            refine ⟨1371825296045914612345565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658200789455772299588173 1371825296045914612345565)
            ·
              refine ⟨514434486017217979629587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371825296045914612345565 514434486017217979629587)
              ·
                refine ⟨771651729025826969444381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514434486017217979629587 771651729025826969444381)
                ·
                  refine ⟨289369398384685113541643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771651729025826969444381 289369398384685113541643)
                  ·
                    rfl

theorem cell20_633988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_633988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_633988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_633988 prefixEnd_633988 := by exact prefixLift 633988
  have htrace : WordTrace (prefixWord ++ tailWord_633988) baseStart_633988 baseEnd_633988 := by
    simpa [prefixWord, tailWord_633988, baseEnd_633988] using wordTrace_append hprefix tailTrace_633988
  have hstable : (prefixWord ++ tailWord_633988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633988).length < 2 ^ (prefixWord ++ tailWord_633988).sum := by decide
  have hdescent : baseEnd_633988 < baseStart_633988 := by decide
  rcases family_descends (prefixWord ++ tailWord_633988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634002 : List Nat := [3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_634002 : Nat := 118140960795 + 634002 * 2 ^ 59
def prefixEnd_634002 : Nat := 4983230072969 + 3 ^ 40 * 634002 * 2
def baseEnd_634002 : Nat := 96458596122054429024973

theorem tailTrace_634002 : CollatzResearch.WordTrace tailWord_634002 prefixEnd_634002 96458596122054429024973 := by
  unfold tailWord_634002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780988162281626941546065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15415968432751005177456173 5780988162281626941546065)
  ·
    refine ⟨4335741121711220206159549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5780988162281626941546065 4335741121711220206159549)
    ·
      refine ⟨1625902920641707577309831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4335741121711220206159549 1625902920641707577309831)
      ·
        refine ⟨2438854380962561365964747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625902920641707577309831 2438854380962561365964747)
        ·
          refine ⟨3658281571443842048947121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438854380962561365964747 3658281571443842048947121)
          ·
            refine ⟨2743711178582881536710341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658281571443842048947121 2743711178582881536710341)
            ·
              refine ⟨514445845984290288133189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2743711178582881536710341 514445845984290288133189)
              ·
                refine ⟨96458596122054429024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514445845984290288133189 96458596122054429024973)
                ·
                  rfl

theorem cell20_634002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_634002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634002 prefixEnd_634002 := by exact prefixLift 634002
  have htrace : WordTrace (prefixWord ++ tailWord_634002) baseStart_634002 baseEnd_634002 := by
    simpa [prefixWord, tailWord_634002, baseEnd_634002] using wordTrace_append hprefix tailTrace_634002
  have hstable : (prefixWord ++ tailWord_634002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634002).length < 2 ^ (prefixWord ++ tailWord_634002).sum := by decide
  have hdescent : baseEnd_634002 < baseStart_634002 := by decide
  rcases family_descends (prefixWord ++ tailWord_634002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634012 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_634012 : Nat := 118140960795 + 634012 * 2 ^ 59
def prefixEnd_634012 : Nat := 4983230072969 + 3 ^ 40 * 634012 * 2
def baseEnd_634012 : Nat := 289380352638647696741545

theorem tailTrace_634012 : CollatzResearch.WordTrace tailWord_634012 prefixEnd_634012 289380352638647696741545 := by
  unfold tailWord_634012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562158689545139737024145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15416211586060186316032193 11562158689545139737024145)
  ·
    refine ⟨8671619017158854802768109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11562158689545139737024145 8671619017158854802768109)
    ·
      refine ⟨3251857131434570551038041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8671619017158854802768109 3251857131434570551038041)
      ·
        refine ⟨2438892848575927913278531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3251857131434570551038041 2438892848575927913278531)
        ·
          refine ⟨3658339272863891869917797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438892848575927913278531 3658339272863891869917797)
          ·
            refine ⟨685938613661979725609587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3658339272863891869917797 685938613661979725609587)
            ·
              refine ⟨1028907920492969588414381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685938613661979725609587 1028907920492969588414381)
              ·
                refine ⟨385840470184863595655393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028907920492969588414381 385840470184863595655393)
                ·
                  refine ⟨289380352638647696741545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385840470184863595655393 289380352638647696741545)
                  ·
                    rfl

theorem cell20_634012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_634012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634012 prefixEnd_634012 := by exact prefixLift 634012
  have htrace : WordTrace (prefixWord ++ tailWord_634012) baseStart_634012 baseEnd_634012 := by
    simpa [prefixWord, tailWord_634012, baseEnd_634012] using wordTrace_append hprefix tailTrace_634012
  have hstable : (prefixWord ++ tailWord_634012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634012).length < 2 ^ (prefixWord ++ tailWord_634012).sum := by decide
  have hdescent : baseEnd_634012 < baseStart_634012 := by decide
  rcases family_descends (prefixWord ++ tailWord_634012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634023 : List Nat := [1, 1, 6, 2, 1, 1, 8]
def baseStart_634023 : Nat := 118140960795 + 634023 * 2 ^ 59
def prefixEnd_634023 : Nat := 4983230072969 + 3 ^ 40 * 634023 * 2
def baseEnd_634023 : Nat := 32153930370931171930537

theorem tailTrace_634023 : CollatzResearch.WordTrace tailWord_634023 prefixEnd_634023 32153930370931171930537 := by
  unfold tailWord_634023
  simp only [CollatzResearch.WordTrace]
  refine ⟨23124718582050428352698723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15416479054700285568465815 23124718582050428352698723)
  ·
    refine ⟨34687077873075642529048085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23124718582050428352698723 34687077873075642529048085)
    ·
      refine ⟨1625956775300420743549129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34687077873075642529048085 1625956775300420743549129)
      ·
        refine ⟨1219467581475315557661847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625956775300420743549129 1219467581475315557661847)
        ·
          refine ⟨1829201372212973336492771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219467581475315557661847 1829201372212973336492771)
          ·
            refine ⟨2743802058319460004739157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829201372212973336492771 2743802058319460004739157)
            ·
              refine ⟨32153930370931171930537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2743802058319460004739157 32153930370931171930537)
              ·
                rfl

theorem cell20_634023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_634023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634023 prefixEnd_634023 := by exact prefixLift 634023
  have htrace : WordTrace (prefixWord ++ tailWord_634023) baseStart_634023 baseEnd_634023 := by
    simpa [prefixWord, tailWord_634023, baseEnd_634023] using wordTrace_append hprefix tailTrace_634023
  have hstable : (prefixWord ++ tailWord_634023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634023).length < 2 ^ (prefixWord ++ tailWord_634023).sum := by decide
  have hdescent : baseEnd_634023 < baseStart_634023 := by decide
  rcases family_descends (prefixWord ++ tailWord_634023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634029 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 2]
def baseStart_634029 : Nat := 118140960795 + 634029 * 2 ^ 59
def prefixEnd_634029 : Nat := 4983230072969 + 3 ^ 40 * 634029 * 2
def baseEnd_634029 : Nat := 289388111901871193174809

theorem tailTrace_634029 : CollatzResearch.WordTrace tailWord_634029 prefixEnd_634029 289388111901871193174809 := by
  unfold tailWord_634029
  simp only [CollatzResearch.WordTrace]
  refine ⟨23124937420028691377417141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15416624946685794251611427 23124937420028691377417141)
  ·
    refine ⟨2167962883127689816632857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23124937420028691377417141 2167962883127689816632857)
    ·
      refine ⟨1625972162345767362474643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2167962883127689816632857 1625972162345767362474643)
      ·
        refine ⟨2438958243518651043711965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625972162345767362474643 2438958243518651043711965)
        ·
          refine ⟨914609341319494141391987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2438958243518651043711965 914609341319494141391987)
          ·
            refine ⟨1371914011979241212087981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914609341319494141391987 1371914011979241212087981)
            ·
              refine ⟨514467754492215454532993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371914011979241212087981 514467754492215454532993)
              ·
                refine ⟨385850815869161590899745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514467754492215454532993 385850815869161590899745)
                ·
                  refine ⟨289388111901871193174809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385850815869161590899745 289388111901871193174809)
                  ·
                    rfl

theorem cell20_634029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_634029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634029 prefixEnd_634029 := by exact prefixLift 634029
  have htrace : WordTrace (prefixWord ++ tailWord_634029) baseStart_634029 baseEnd_634029 := by
    simpa [prefixWord, tailWord_634029, baseEnd_634029] using wordTrace_append hprefix tailTrace_634029
  have hstable : (prefixWord ++ tailWord_634029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634029).length < 2 ^ (prefixWord ++ tailWord_634029).sum := by decide
  have hdescent : baseEnd_634029 < baseStart_634029 := by decide
  rcases family_descends (prefixWord ++ tailWord_634029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634033 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_634033 : Nat := 118140960795 + 634033 * 2 ^ 59
def prefixEnd_634033 : Nat := 4983230072969 + 3 ^ 40 * 634033 * 2
def baseEnd_634033 : Nat := 289389937610864957041459

theorem tailTrace_634033 : CollatzResearch.WordTrace tailWord_634033 prefixEnd_634033 289389937610864957041459 := by
  unfold tailWord_634033
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125083312014200060562753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15416722208009466707041835 23125083312014200060562753)
  ·
    refine ⟨17343812484010650045422065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23125083312014200060562753 17343812484010650045422065)
    ·
      refine ⟨13007859363007987534066549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17343812484010650045422065 13007859363007987534066549)
      ·
        refine ⟨1219486815281998831318739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13007859363007987534066549 1219486815281998831318739)
        ·
          refine ⟨1829230222922998246978109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219486815281998831318739 1829230222922998246978109)
          ·
            refine ⟨685961333596124342616791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1829230222922998246978109 685961333596124342616791)
            ·
              refine ⟨1028942000394186513925187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685961333596124342616791 1028942000394186513925187)
              ·
                refine ⟨1543413000591279770887781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028942000394186513925187 1543413000591279770887781)
                ·
                  refine ⟨289389937610864957041459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543413000591279770887781 289389937610864957041459)
                  ·
                    rfl

theorem cell20_634033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_634033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634033 prefixEnd_634033 := by exact prefixLift 634033
  have htrace : WordTrace (prefixWord ++ tailWord_634033) baseStart_634033 baseEnd_634033 := by
    simpa [prefixWord, tailWord_634033, baseEnd_634033] using wordTrace_append hprefix tailTrace_634033
  have hstable : (prefixWord ++ tailWord_634033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634033).length < 2 ^ (prefixWord ++ tailWord_634033).sum := by decide
  have hdescent : baseEnd_634033 < baseStart_634033 := by decide
  rcases family_descends (prefixWord ++ tailWord_634033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634047 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_634047 : Nat := 118140960795 + 634047 * 2 ^ 59
def prefixEnd_634047 : Nat := 4983230072969 + 3 ^ 40 * 634047 * 2
def baseEnd_634047 : Nat := 289396327592343130574735

theorem tailTrace_634047 : CollatzResearch.WordTrace tailWord_634047 prefixEnd_634047 289396327592343130574735 := by
  unfold tailWord_634047
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125593933963480451572395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15417062622642320301048263 23125593933963480451572395)
  ·
    refine ⟨34688390900945220677358593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23125593933963480451572395 34688390900945220677358593)
    ·
      refine ⟨26016293175708915508018945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34688390900945220677358593 26016293175708915508018945)
      ·
        refine ⟨19512219881781686631014209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26016293175708915508018945 19512219881781686631014209)
        ·
          refine ⟨14634164911336264973260657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19512219881781686631014209 14634164911336264973260657)
          ·
            refine ⟨10975623683502198729945493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14634164911336264973260657 10975623683502198729945493)
            ·
              refine ⟨514482360164165565466195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10975623683502198729945493 514482360164165565466195)
              ·
                refine ⟨771723540246248348199293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514482360164165565466195 771723540246248348199293)
                ·
                  refine ⟨289396327592343130574735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771723540246248348199293 289396327592343130574735)
                  ·
                    rfl

theorem cell20_634047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_634047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634047 prefixEnd_634047 := by exact prefixLift 634047
  have htrace : WordTrace (prefixWord ++ tailWord_634047) baseStart_634047 baseEnd_634047 := by
    simpa [prefixWord, tailWord_634047, baseEnd_634047] using wordTrace_append hprefix tailTrace_634047
  have hstable : (prefixWord ++ tailWord_634047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634047).length < 2 ^ (prefixWord ++ tailWord_634047).sum := by decide
  have hdescent : baseEnd_634047 < baseStart_634047 := by decide
  rcases family_descends (prefixWord ++ tailWord_634047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634051 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_634051 : Nat := 118140960795 + 634051 * 2 ^ 59
def prefixEnd_634051 : Nat := 4983230072969 + 3 ^ 40 * 634051 * 2
def baseEnd_634051 : Nat := 289398153301336894441385

theorem tailTrace_634051 : CollatzResearch.WordTrace tailWord_634051 prefixEnd_634051 289398153301336894441385 := by
  unfold tailWord_634051
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125739825948989134718007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15417159883965992756478671 23125739825948989134718007)
  ·
    refine ⟨34688609738923483702077011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23125739825948989134718007 34688609738923483702077011)
    ·
      refine ⟨52032914608385225553115517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34688609738923483702077011 52032914608385225553115517)
      ·
        refine ⟨19512342978144459582418319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52032914608385225553115517 19512342978144459582418319)
        ·
          refine ⟨29268514467216689373627479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19512342978144459582418319 29268514467216689373627479)
          ·
            refine ⟨43902771700825034060441219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29268514467216689373627479 43902771700825034060441219)
            ·
              refine ⟨65854157551237551090661829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43902771700825034060441219 65854157551237551090661829)
              ·
                refine ⟨12347654540857040829499093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65854157551237551090661829 12347654540857040829499093)
                ·
                  refine ⟨289398153301336894441385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12347654540857040829499093 289398153301336894441385)
                  ·
                    rfl

theorem cell20_634051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_634051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634051 prefixEnd_634051 := by exact prefixLift 634051
  have htrace : WordTrace (prefixWord ++ tailWord_634051) baseStart_634051 baseEnd_634051 := by
    simpa [prefixWord, tailWord_634051, baseEnd_634051] using wordTrace_append hprefix tailTrace_634051
  have hstable : (prefixWord ++ tailWord_634051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634051).length < 2 ^ (prefixWord ++ tailWord_634051).sum := by decide
  have hdescent : baseEnd_634051 < baseStart_634051 := by decide
  rcases family_descends (prefixWord ++ tailWord_634051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634099 : List Nat := [1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_634099 : Nat := 118140960795 + 634099 * 2 ^ 59
def prefixEnd_634099 : Nat := 4983230072969 + 3 ^ 40 * 634099 * 2
def baseEnd_634099 : Nat := 96473353936420686947063

theorem tailTrace_634099 : CollatzResearch.WordTrace tailWord_634099 prefixEnd_634099 96473353936420686947063 := by
  unfold tailWord_634099
  simp only [CollatzResearch.WordTrace]
  refine ⟨23127490529775093332465351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15418327019850062221643567 23127490529775093332465351)
  ·
    refine ⟨34691235794662639998698027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23127490529775093332465351 34691235794662639998698027)
    ·
      refine ⟨52036853691993959998047041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34691235794662639998698027 52036853691993959998047041)
      ·
        refine ⟨39027640268995469998535281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52036853691993959998047041 39027640268995469998535281)
        ·
          refine ⟨29270730201746602498901461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39027640268995469998535281 29270730201746602498901461)
          ·
            refine ⟨686032739103435996068003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29270730201746602498901461 686032739103435996068003)
            ·
              refine ⟨1029049108655153994102005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686032739103435996068003 1029049108655153994102005)
              ·
                refine ⟨96473353936420686947063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029049108655153994102005 96473353936420686947063)
                ·
                  rfl

theorem cell20_634099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_634099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634099 prefixEnd_634099 := by exact prefixLift 634099
  have htrace : WordTrace (prefixWord ++ tailWord_634099) baseStart_634099 baseEnd_634099 := by
    simpa [prefixWord, tailWord_634099, baseEnd_634099] using wordTrace_append hprefix tailTrace_634099
  have hstable : (prefixWord ++ tailWord_634099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634099).length < 2 ^ (prefixWord ++ tailWord_634099).sum := by decide
  have hdescent : baseEnd_634099 < baseStart_634099 := by decide
  rcases family_descends (prefixWord ++ tailWord_634099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634106 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_634106 : Nat := 118140960795 + 634106 * 2 ^ 59
def prefixEnd_634106 : Nat := 4983230072969 + 3 ^ 40 * 634106 * 2
def baseEnd_634106 : Nat := 289423256800001147607827

theorem tailTrace_634106 : CollatzResearch.WordTrace tailWord_634106 prefixEnd_634106 289423256800001147607827 := by
  unfold tailWord_634106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781936460187433381992543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15418497227166489018646781 5781936460187433381992543)
  ·
    refine ⟨8672904690281150072988815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5781936460187433381992543 8672904690281150072988815)
    ·
      refine ⟨13009357035421725109483223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672904690281150072988815 13009357035421725109483223)
      ·
        refine ⟨19514035553132587664224835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009357035421725109483223 19514035553132587664224835)
        ·
          refine ⟨29271053329698881496337253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19514035553132587664224835 29271053329698881496337253)
          ·
            refine ⟨5488322499318540280563235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29271053329698881496337253 5488322499318540280563235)
            ·
              refine ⟨8232483748977810420844853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5488322499318540280563235 8232483748977810420844853)
              ·
                refine ⟨771795351466669726954205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8232483748977810420844853 771795351466669726954205)
                ·
                  refine ⟨289423256800001147607827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771795351466669726954205 289423256800001147607827)
                  ·
                    rfl

theorem cell20_634106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_634106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634106 prefixEnd_634106 := by exact prefixLift 634106
  have htrace : WordTrace (prefixWord ++ tailWord_634106) baseStart_634106 baseEnd_634106 := by
    simpa [prefixWord, tailWord_634106, baseEnd_634106] using wordTrace_append hprefix tailTrace_634106
  have hstable : (prefixWord ++ tailWord_634106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634106).length < 2 ^ (prefixWord ++ tailWord_634106).sum := by decide
  have hdescent : baseEnd_634106 < baseStart_634106 := by decide
  rcases family_descends (prefixWord ++ tailWord_634106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634113 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_634113 : Nat := 118140960795 + 634113 * 2 ^ 59
def prefixEnd_634113 : Nat := 4983230072969 + 3 ^ 40 * 634113 * 2
def baseEnd_634113 : Nat := 289426451790740234374465

theorem tailTrace_634113 : CollatzResearch.WordTrace tailWord_634113 prefixEnd_634113 289426451790740234374465 := by
  unfold tailWord_634113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23128001151724373723474993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15418667434482915815649995 23128001151724373723474993)
  ·
    refine ⟨17346000863793280292606245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23128001151724373723474993 17346000863793280292606245)
    ·
      refine ⟨3252375161961240054863671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17346000863793280292606245 3252375161961240054863671)
      ·
        refine ⟨4878562742941860082295507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252375161961240054863671 4878562742941860082295507)
        ·
          refine ⟨7317844114412790123443261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878562742941860082295507 7317844114412790123443261)
          ·
            refine ⟨2744191542904796296291223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7317844114412790123443261 2744191542904796296291223)
            ·
              refine ⟨4116287314357194444436835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744191542904796296291223 4116287314357194444436835)
              ·
                refine ⟨6174430971535791666655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116287314357194444436835 6174430971535791666655253)
                ·
                  refine ⟨289426451790740234374465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6174430971535791666655253 289426451790740234374465)
                  ·
                    rfl

theorem cell20_634113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_634113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634113 prefixEnd_634113 := by exact prefixLift 634113
  have htrace : WordTrace (prefixWord ++ tailWord_634113) baseStart_634113 baseEnd_634113 := by
    simpa [prefixWord, tailWord_634113, baseEnd_634113] using wordTrace_append hprefix tailTrace_634113
  have hstable : (prefixWord ++ tailWord_634113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634113).length < 2 ^ (prefixWord ++ tailWord_634113).sum := by decide
  have hdescent : baseEnd_634113 < baseStart_634113 := by decide
  rcases family_descends (prefixWord ++ tailWord_634113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634116 : List Nat := [2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_634116 : Nat := 118140960795 + 634116 * 2 ^ 59
def prefixEnd_634116 : Nat := 4983230072969 + 3 ^ 40 * 634116 * 2
def baseEnd_634116 : Nat := 96475940357495185758151

theorem tailTrace_634116 : CollatzResearch.WordTrace tailWord_634116 prefixEnd_634116 96475940357495185758151 := by
  unfold tailWord_634116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564055285356752617917101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15418740380475670157222801 11564055285356752617917101)
  ·
    refine ⟨4336520732008782231718913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11564055285356752617917101 4336520732008782231718913)
    ·
      refine ⟨3252390549006586673789185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4336520732008782231718913 3252390549006586673789185)
      ·
        refine ⟨2439292911754940005341889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3252390549006586673789185 2439292911754940005341889)
        ·
          refine ⟨1829469683816205004006417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439292911754940005341889 1829469683816205004006417)
          ·
            refine ⟨1372102262862153753004813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829469683816205004006417 1372102262862153753004813)
            ·
              refine ⟨514538348573307657376805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372102262862153753004813 514538348573307657376805)
              ·
                refine ⟨96475940357495185758151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514538348573307657376805 96475940357495185758151)
                ·
                  rfl

theorem cell20_634116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_634116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634116 prefixEnd_634116 := by exact prefixLift 634116
  have htrace : WordTrace (prefixWord ++ tailWord_634116) baseStart_634116 baseEnd_634116 := by
    simpa [prefixWord, tailWord_634116, baseEnd_634116] using wordTrace_append hprefix tailTrace_634116
  have hstable : (prefixWord ++ tailWord_634116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634116).length < 2 ^ (prefixWord ++ tailWord_634116).sum := by decide
  have hdescent : baseEnd_634116 < baseStart_634116 := by decide
  rcases family_descends (prefixWord ++ tailWord_634116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634157 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_634157 : Nat := 118140960795 + 634157 * 2 ^ 59
def prefixEnd_634157 : Nat := 4983230072969 + 3 ^ 40 * 634157 * 2
def baseEnd_634157 : Nat := 289446534589671636907619

theorem tailTrace_634157 : CollatzResearch.WordTrace tailWord_634157 prefixEnd_634157 289446534589671636907619 := by
  unfold tailWord_634157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129605963564969238076725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15419737309043312825384483 23129605963564969238076725)
  ·
    refine ⟨2168400559084215866069693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23129605963564969238076725 2168400559084215866069693)
    ·
      refine ⟨813150209656580949776135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2168400559084215866069693 813150209656580949776135)
      ·
        refine ⟨1219725314484871424664203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813150209656580949776135 1219725314484871424664203)
        ·
          refine ⟨1829587971727307136996305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219725314484871424664203 1829587971727307136996305)
          ·
            refine ⟨1372190978795480352747229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829587971727307136996305 1372190978795480352747229)
            ·
              refine ⟨514571617048305132280211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372190978795480352747229 514571617048305132280211)
              ·
                refine ⟨771857425572457698420317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514571617048305132280211 771857425572457698420317)
                ·
                  refine ⟨289446534589671636907619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771857425572457698420317 289446534589671636907619)
                  ·
                    rfl

theorem cell20_634157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_634157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634157 prefixEnd_634157 := by exact prefixLift 634157
  have htrace : WordTrace (prefixWord ++ tailWord_634157) baseStart_634157 baseEnd_634157 := by
    simpa [prefixWord, tailWord_634157, baseEnd_634157] using wordTrace_append hprefix tailTrace_634157
  have hstable : (prefixWord ++ tailWord_634157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634157).length < 2 ^ (prefixWord ++ tailWord_634157).sum := by decide
  have hdescent : baseEnd_634157 < baseStart_634157 := by decide
  rcases family_descends (prefixWord ++ tailWord_634157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634175 : List Nat := [1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_634175 : Nat := 118140960795 + 634175 * 2 ^ 59
def prefixEnd_634175 : Nat := 4983230072969 + 3 ^ 40 * 634175 * 2
def baseEnd_634175 : Nat := 96484916760047858102515

theorem tailTrace_634175 : CollatzResearch.WordTrace tailWord_634175 prefixEnd_634175 96484916760047858102515 := by
  unfold tailWord_634175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23130262477499758312231979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15420174984999838874821319 23130262477499758312231979)
  ·
    refine ⟨34695393716249637468347969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23130262477499758312231979 34695393716249637468347969)
    ·
      refine ⟨26021545287187228101260977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34695393716249637468347969 26021545287187228101260977)
      ·
        refine ⟨19516158965390421075945733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26021545287187228101260977 19516158965390421075945733)
        ·
          refine ⟨3659279806010703951739825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19516158965390421075945733 3659279806010703951739825)
          ·
            refine ⟨2744459854508027963804869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3659279806010703951739825 2744459854508027963804869)
            ·
              refine ⟨514586222720255243213413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2744459854508027963804869 514586222720255243213413)
              ·
                refine ⟨96484916760047858102515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514586222720255243213413 96484916760047858102515)
                ·
                  rfl

theorem cell20_634175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_634175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634175 prefixEnd_634175 := by exact prefixLift 634175
  have htrace : WordTrace (prefixWord ++ tailWord_634175) baseStart_634175 baseEnd_634175 := by
    simpa [prefixWord, tailWord_634175, baseEnd_634175] using wordTrace_append hprefix tailTrace_634175
  have hstable : (prefixWord ++ tailWord_634175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634175).length < 2 ^ (prefixWord ++ tailWord_634175).sum := by decide
  have hdescent : baseEnd_634175 < baseStart_634175 := by decide
  rcases family_descends (prefixWord ++ tailWord_634175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634198 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_634198 : Nat := 118140960795 + 634198 * 2 ^ 59
def prefixEnd_634198 : Nat := 4983230072969 + 3 ^ 40 * 634198 * 2
def baseEnd_634198 : Nat := 289465248106857716540785

theorem tailTrace_634198 : CollatzResearch.WordTrace tailWord_634198 prefixEnd_634198 289465248106857716540785 := by
  unfold tailWord_634198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445693834776027077519953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15420734237610955493546165 1445693834776027077519953)
  ·
    refine ⟨1084270376082020308139965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1445693834776027077519953 1084270376082020308139965)
    ·
      refine ⟨406601391030757615552487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1084270376082020308139965 406601391030757615552487)
      ·
        refine ⟨609902086546136423328731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406601391030757615552487 609902086546136423328731)
        ·
          refine ⟨914853129819204634993097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609902086546136423328731 914853129819204634993097)
          ·
            refine ⟨686139847364403476244823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914853129819204634993097 686139847364403476244823)
            ·
              refine ⟨1029209771046605214367235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686139847364403476244823 1029209771046605214367235)
              ·
                refine ⟨1543814656569907821550853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029209771046605214367235 1543814656569907821550853)
                ·
                  refine ⟨289465248106857716540785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543814656569907821550853 289465248106857716540785)
                  ·
                    rfl

theorem cell20_634198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_634198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634198 prefixEnd_634198 := by exact prefixLift 634198
  have htrace : WordTrace (prefixWord ++ tailWord_634198) baseStart_634198 baseEnd_634198 := by
    simpa [prefixWord, tailWord_634198, baseEnd_634198] using wordTrace_append hprefix tailTrace_634198
  have hstable : (prefixWord ++ tailWord_634198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634198).length < 2 ^ (prefixWord ++ tailWord_634198).sum := by decide
  have hdescent : baseEnd_634198 < baseStart_634198 := by decide
  rcases family_descends (prefixWord ++ tailWord_634198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634254 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_634254 : Nat := 118140960795 + 634254 * 2 ^ 59
def prefixEnd_634254 : Nat := 4983230072969 + 3 ^ 40 * 634254 * 2
def baseEnd_634254 : Nat := 289490808032770410673889

theorem tailTrace_634254 : CollatzResearch.WordTrace tailWord_634254 prefixEnd_634254 289490808032770410673889 := by
  unfold tailWord_634254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891642980526694350544727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15422095896142369869571877 2891642980526694350544727)
  ·
    refine ⟨4337464470790041525817091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891642980526694350544727 4337464470790041525817091)
    ·
      refine ⟨6506196706185062288725637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337464470790041525817091 6506196706185062288725637)
      ·
        refine ⟨1219911882409699179136057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6506196706185062288725637 1219911882409699179136057)
        ·
          refine ⟨914933911807274384352043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219911882409699179136057 914933911807274384352043)
          ·
            refine ⟨1372400867710911576528065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914933911807274384352043 1372400867710911576528065)
            ·
              refine ⟨1029300650783183682396049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372400867710911576528065 1029300650783183682396049)
              ·
                refine ⟨771975488087387761797037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029300650783183682396049 771975488087387761797037)
                ·
                  refine ⟨289490808032770410673889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771975488087387761797037 289490808032770410673889)
                  ·
                    rfl

theorem cell20_634254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_634254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634254 prefixEnd_634254 := by exact prefixLift 634254
  have htrace : WordTrace (prefixWord ++ tailWord_634254) baseStart_634254 baseEnd_634254 := by
    simpa [prefixWord, tailWord_634254, baseEnd_634254] using wordTrace_append hprefix tailTrace_634254
  have hstable : (prefixWord ++ tailWord_634254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634254).length < 2 ^ (prefixWord ++ tailWord_634254).sum := by decide
  have hdescent : baseEnd_634254 < baseStart_634254 := by decide
  rcases family_descends (prefixWord ++ tailWord_634254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634261 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 2]
def baseStart_634261 : Nat := 118140960795 + 634261 * 2 ^ 59
def prefixEnd_634261 : Nat := 4983230072969 + 3 ^ 40 * 634261 * 2
def baseEnd_634261 : Nat := 289494003023509497440527

theorem tailTrace_634261 : CollatzResearch.WordTrace tailWord_634261 prefixEnd_634261 289494003023509497440527 := by
  unfold tailWord_634261
  simp only [CollatzResearch.WordTrace]
  refine ⟨23133399155188194999862637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15422266103458796666575091 23133399155188194999862637)
  ·
    refine ⟨8675024683195573124948489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23133399155188194999862637 8675024683195573124948489)
    ·
      refine ⟨6506268512396679843711367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8675024683195573124948489 6506268512396679843711367)
      ·
        refine ⟨9759402768595019765567051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506268512396679843711367 9759402768595019765567051)
        ·
          refine ⟨14639104152892529648350577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9759402768595019765567051 14639104152892529648350577)
          ·
            refine ⟨10979328114669397236262933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14639104152892529648350577 10979328114669397236262933)
            ·
              refine ⟨514656005375127995449825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10979328114669397236262933 514656005375127995449825)
              ·
                refine ⟨385992004031345996587369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514656005375127995449825 385992004031345996587369)
                ·
                  refine ⟨289494003023509497440527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385992004031345996587369 289494003023509497440527)
                  ·
                    rfl

theorem cell20_634261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_634261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634261 prefixEnd_634261 := by exact prefixLift 634261
  have htrace : WordTrace (prefixWord ++ tailWord_634261) baseStart_634261 baseEnd_634261 := by
    simpa [prefixWord, tailWord_634261, baseEnd_634261] using wordTrace_append hprefix tailTrace_634261
  have hstable : (prefixWord ++ tailWord_634261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634261).length < 2 ^ (prefixWord ++ tailWord_634261).sum := by decide
  have hdescent : baseEnd_634261 < baseStart_634261 := by decide
  rcases family_descends (prefixWord ++ tailWord_634261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634289 : List Nat := [1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_634289 : Nat := 118140960795 + 634289 * 2 ^ 59
def prefixEnd_634289 : Nat := 4983230072969 + 3 ^ 40 * 634289 * 2
def baseEnd_634289 : Nat := 96502260995488614835693

theorem tailTrace_634289 : CollatzResearch.WordTrace tailWord_634289 prefixEnd_634289 96502260995488614835693 := by
  unfold tailWord_634289
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134420399086755781881921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15422946932724503854587947 23134420399086755781881921)
  ·
    refine ⟨17350815299315066836411441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23134420399086755781881921 17350815299315066836411441)
    ·
      refine ⟨13013111474486300127308581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17350815299315066836411441 13013111474486300127308581)
      ·
        refine ⟨2439958401466181273870359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13013111474486300127308581 2439958401466181273870359)
        ·
          refine ⟨3659937602199271910805539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439958401466181273870359 3659937602199271910805539)
          ·
            refine ⟨5489906403298907866208309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659937602199271910805539 5489906403298907866208309)
            ·
              refine ⟨514678725309272612457029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5489906403298907866208309 514678725309272612457029)
              ·
                refine ⟨96502260995488614835693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514678725309272612457029 96502260995488614835693)
                ·
                  rfl

theorem cell20_634289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_634289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634289 prefixEnd_634289 := by exact prefixLift 634289
  have htrace : WordTrace (prefixWord ++ tailWord_634289) baseStart_634289 baseEnd_634289 := by
    simpa [prefixWord, tailWord_634289, baseEnd_634289] using wordTrace_append hprefix tailTrace_634289
  have hstable : (prefixWord ++ tailWord_634289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634289).length < 2 ^ (prefixWord ++ tailWord_634289).sum := by decide
  have hdescent : baseEnd_634289 < baseStart_634289 := by decide
  rcases family_descends (prefixWord ++ tailWord_634289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634354 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_634354 : Nat := 118140960795 + 634354 * 2 ^ 59
def prefixEnd_634354 : Nat := 4983230072969 + 3 ^ 40 * 634354 * 2
def baseEnd_634354 : Nat := 289536450757614507340147

theorem tailTrace_634354 : CollatzResearch.WordTrace tailWord_634354 prefixEnd_634354 289536450757614507340147 := by
  unfold tailWord_634354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784197785962817970749529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15424527429234181255332077 5784197785962817970749529)
  ·
    refine ⟨4338148339472113478062147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5784197785962817970749529 4338148339472113478062147)
    ·
      refine ⟨6507222509208170217093221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4338148339472113478062147 6507222509208170217093221)
      ·
        refine ⟨1220104220476531915704979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6507222509208170217093221 1220104220476531915704979)
        ·
          refine ⟨1830156330714797873557469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220104220476531915704979 1830156330714797873557469)
          ·
            refine ⟨686308624018049202584051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1830156330714797873557469 686308624018049202584051)
            ·
              refine ⟨1029462936027073803876077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686308624018049202584051 1029462936027073803876077)
              ·
                refine ⟨386048601010152676453529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029462936027073803876077 386048601010152676453529)
                ·
                  refine ⟨289536450757614507340147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386048601010152676453529 289536450757614507340147)
                  ·
                    rfl

theorem cell20_634354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_634354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634354 prefixEnd_634354 := by exact prefixLift 634354
  have htrace : WordTrace (prefixWord ++ tailWord_634354) baseStart_634354 baseEnd_634354 := by
    simpa [prefixWord, tailWord_634354, baseEnd_634354] using wordTrace_append hprefix tailTrace_634354
  have hstable : (prefixWord ++ tailWord_634354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634354).length < 2 ^ (prefixWord ++ tailWord_634354).sum := by decide
  have hdescent : baseEnd_634354 < baseStart_634354 := by decide
  rcases family_descends (prefixWord ++ tailWord_634354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634381 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 3]
def baseStart_634381 : Nat := 118140960795 + 634381 * 2 ^ 59
def prefixEnd_634381 : Nat := 4983230072969 + 3 ^ 40 * 634381 * 2
def baseEnd_634381 : Nat := 289548774293322413440037

theorem tailTrace_634381 : CollatzResearch.WordTrace tailWord_634381 prefixEnd_634381 289548774293322413440037 := by
  unfold tailWord_634381
  simp only [CollatzResearch.WordTrace]
  refine ⟨23137775914753455494230997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15425183943168970329487331 23137775914753455494230997)
  ·
    refine ⟨542291623002034113146039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23137775914753455494230997 542291623002034113146039)
    ·
      refine ⟨813437434503051169719059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542291623002034113146039 813437434503051169719059)
      ·
        refine ⟨1220156151754576754578589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813437434503051169719059 1220156151754576754578589)
        ·
          refine ⟨457558556907966282966971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220156151754576754578589 457558556907966282966971)
          ·
            refine ⟨686337835361949424450457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457558556907966282966971 686337835361949424450457)
            ·
              refine ⟨514753376521462068337843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686337835361949424450457 514753376521462068337843)
              ·
                refine ⟨772130064782193102506765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514753376521462068337843 772130064782193102506765)
                ·
                  refine ⟨289548774293322413440037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772130064782193102506765 289548774293322413440037)
                  ·
                    rfl

theorem cell20_634381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_634381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634381 prefixEnd_634381 := by exact prefixLift 634381
  have htrace : WordTrace (prefixWord ++ tailWord_634381) baseStart_634381 baseEnd_634381 := by
    simpa [prefixWord, tailWord_634381, baseEnd_634381] using wordTrace_append hprefix tailTrace_634381
  have hstable : (prefixWord ++ tailWord_634381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634381).length < 2 ^ (prefixWord ++ tailWord_634381).sum := by decide
  have hdescent : baseEnd_634381 < baseStart_634381 := by decide
  rcases family_descends (prefixWord ++ tailWord_634381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634389 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_634389 : Nat := 118140960795 + 634389 * 2 ^ 59
def prefixEnd_634389 : Nat := 4983230072969 + 3 ^ 40 * 634389 * 2
def baseEnd_634389 : Nat := 289552425711309941173337

theorem tailTrace_634389 : CollatzResearch.WordTrace tailWord_634389 prefixEnd_634389 289552425711309941173337 := by
  unfold tailWord_634389
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138067698724472860522221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15425378465816315240348147 23138067698724472860522221)
  ·
    refine ⟨8676775387021677322695833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23138067698724472860522221 8676775387021677322695833)
    ·
      refine ⟨6507581540266257992021875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8676775387021677322695833 6507581540266257992021875)
      ·
        refine ⟨9761372310399386988032813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507581540266257992021875 9761372310399386988032813)
        ·
          refine ⟨3660514616399770120512305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9761372310399386988032813 3660514616399770120512305)
          ·
            refine ⟨2745385962299827590384229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660514616399770120512305 2745385962299827590384229)
            ·
              refine ⟨514759867931217673197043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2745385962299827590384229 514759867931217673197043)
              ·
                refine ⟨772139801896826509795565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514759867931217673197043 772139801896826509795565)
                ·
                  refine ⟨289552425711309941173337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772139801896826509795565 289552425711309941173337)
                  ·
                    rfl

theorem cell20_634389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_634389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634389 prefixEnd_634389 := by exact prefixLift 634389
  have htrace : WordTrace (prefixWord ++ tailWord_634389) baseStart_634389 baseEnd_634389 := by
    simpa [prefixWord, tailWord_634389, baseEnd_634389] using wordTrace_append hprefix tailTrace_634389
  have hstable : (prefixWord ++ tailWord_634389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634389).length < 2 ^ (prefixWord ++ tailWord_634389).sum := by decide
  have hdescent : baseEnd_634389 < baseStart_634389 := by decide
  rcases family_descends (prefixWord ++ tailWord_634389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634454 : List Nat := [5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_634454 : Nat := 118140960795 + 634454 * 2 ^ 59
def prefixEnd_634454 : Nat := 4983230072969 + 3 ^ 40 * 634454 * 2
def baseEnd_634454 : Nat := 96527364494152868002135

theorem tailTrace_634454 : CollatzResearch.WordTrace tailWord_634454 prefixEnd_634454 96527364494152868002135 := by
  unfold tailWord_634454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446277402718061810102401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15426958962325992641092277 1446277402718061810102401)
  ·
    refine ⟨1084708052038546357576801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1446277402718061810102401 1084708052038546357576801)
    ·
      refine ⟨813531039028909768182601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1084708052038546357576801 813531039028909768182601)
      ·
        refine ⟨610148279271682326136951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 813531039028909768182601 610148279271682326136951)
        ·
          refine ⟨915222418907523489205427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610148279271682326136951 915222418907523489205427)
          ·
            refine ⟨1372833628361285233808141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915222418907523489205427 1372833628361285233808141)
            ·
              refine ⟨514812610635481962678053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372833628361285233808141 514812610635481962678053)
              ·
                refine ⟨96527364494152868002135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514812610635481962678053 96527364494152868002135)
                ·
                  rfl

theorem cell20_634454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_634454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634454 prefixEnd_634454 := by exact prefixLift 634454
  have htrace : WordTrace (prefixWord ++ tailWord_634454) baseStart_634454 baseEnd_634454 := by
    simpa [prefixWord, tailWord_634454, baseEnd_634454] using wordTrace_append hprefix tailTrace_634454
  have hstable : (prefixWord ++ tailWord_634454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634454).length < 2 ^ (prefixWord ++ tailWord_634454).sum := by decide
  have hdescent : baseEnd_634454 < baseStart_634454 := by decide
  rcases family_descends (prefixWord ++ tailWord_634454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634455 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_634455 : Nat := 118140960795 + 634455 * 2 ^ 59
def prefixEnd_634455 : Nat := 4983230072969 + 3 ^ 40 * 634455 * 2
def baseEnd_634455 : Nat := 289582549909707044973067

theorem tailTrace_634455 : CollatzResearch.WordTrace tailWord_634455 prefixEnd_634455 289582549909707044973067 := by
  unfold tailWord_634455
  simp only [CollatzResearch.WordTrace]
  refine ⟨23140474916485366132424819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15426983277656910754949879 23140474916485366132424819)
  ·
    refine ⟨34710712374728049198637229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23140474916485366132424819 34710712374728049198637229)
    ·
      refine ⟨13016517140523018449488961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34710712374728049198637229 13016517140523018449488961)
      ·
        refine ⟨9762387855392263837116721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13016517140523018449488961 9762387855392263837116721)
        ·
          refine ⟨7321790891544197877837541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9762387855392263837116721 7321790891544197877837541)
          ·
            refine ⟨1372835792164537102094539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7321790891544197877837541 1372835792164537102094539)
            ·
              refine ⟨2059253688246805653141809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372835792164537102094539 2059253688246805653141809)
              ·
                refine ⟨1544440266185104239856357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059253688246805653141809 1544440266185104239856357)
                ·
                  refine ⟨289582549909707044973067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544440266185104239856357 289582549909707044973067)
                  ·
                    rfl

theorem cell20_634455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_634455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634455 prefixEnd_634455 := by exact prefixLift 634455
  have htrace : WordTrace (prefixWord ++ tailWord_634455) baseStart_634455 baseEnd_634455 := by
    simpa [prefixWord, tailWord_634455, baseEnd_634455] using wordTrace_append hprefix tailTrace_634455
  have hstable : (prefixWord ++ tailWord_634455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634455).length < 2 ^ (prefixWord ++ tailWord_634455).sum := by decide
  have hdescent : baseEnd_634455 < baseStart_634455 := by decide
  rcases family_descends (prefixWord ++ tailWord_634455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634476 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_634476 : Nat := 118140960795 + 634476 * 2 ^ 59
def prefixEnd_634476 : Nat := 4983230072969 + 3 ^ 40 * 634476 * 2
def baseEnd_634476 : Nat := 289592134881924305272981

theorem tailTrace_634476 : CollatzResearch.WordTrace tailWord_634476 prefixEnd_634476 289592134881924305272981 := by
  unfold tailWord_634476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570620424704643359469641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15427493899606191145959521 11570620424704643359469641)
  ·
    refine ⟨8677965318528482519602231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11570620424704643359469641 8677965318528482519602231)
    ·
      refine ⟨13016947977792723779403347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8677965318528482519602231 13016947977792723779403347)
      ·
        refine ⟨19525421966689085669105021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13016947977792723779403347 19525421966689085669105021)
        ·
          refine ⟨7322033237508407125914383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19525421966689085669105021 7322033237508407125914383)
          ·
            refine ⟨10983049856262610688871575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322033237508407125914383 10983049856262610688871575)
            ·
              refine ⟨16474574784393916033307363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983049856262610688871575 16474574784393916033307363)
              ·
                refine ⟨24711862176590874049961045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16474574784393916033307363 24711862176590874049961045)
                ·
                  refine ⟨289592134881924305272981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24711862176590874049961045 289592134881924305272981)
                  ·
                    rfl

theorem cell20_634476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_634476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634476 prefixEnd_634476 := by exact prefixLift 634476
  have htrace : WordTrace (prefixWord ++ tailWord_634476) baseStart_634476 baseEnd_634476 := by
    simpa [prefixWord, tailWord_634476, baseEnd_634476] using wordTrace_append hprefix tailTrace_634476
  have hstable : (prefixWord ++ tailWord_634476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634476).length < 2 ^ (prefixWord ++ tailWord_634476).sum := by decide
  have hdescent : baseEnd_634476 < baseStart_634476 := by decide
  rcases family_descends (prefixWord ++ tailWord_634476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634493 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_634493 : Nat := 118140960795 + 634493 * 2 ^ 59
def prefixEnd_634493 : Nat := 4983230072969 + 3 ^ 40 * 634493 * 2
def baseEnd_634493 : Nat := 289599894145147801706245

theorem tailTrace_634493 : CollatzResearch.WordTrace tailWord_634493 prefixEnd_634493 289599894145147801706245 := by
  unfold tailWord_634493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23141860890347698622308133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15427907260231799081538755 23141860890347698622308133)
  ·
    refine ⟨4339098916940193491682775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23141860890347698622308133 4339098916940193491682775)
    ·
      refine ⟨6508648375410290237524163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339098916940193491682775 6508648375410290237524163)
      ·
        refine ⟨9762972563115435356286245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508648375410290237524163 9762972563115435356286245)
        ·
          refine ⟨1830557355584144129303671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9762972563115435356286245 1830557355584144129303671)
          ·
            refine ⟨2745836033376216193955507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830557355584144129303671 2745836033376216193955507)
            ·
              refine ⟨4118754050064324290933261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745836033376216193955507 4118754050064324290933261)
              ·
                refine ⟨1544532768774121609099973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4118754050064324290933261 1544532768774121609099973)
                ·
                  refine ⟨289599894145147801706245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544532768774121609099973 289599894145147801706245)
                  ·
                    rfl

theorem cell20_634493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_634493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634493 prefixEnd_634493 := by exact prefixLift 634493
  have htrace : WordTrace (prefixWord ++ tailWord_634493) baseStart_634493 baseEnd_634493 := by
    simpa [prefixWord, tailWord_634493, baseEnd_634493] using wordTrace_append hprefix tailTrace_634493
  have hstable : (prefixWord ++ tailWord_634493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634493).length < 2 ^ (prefixWord ++ tailWord_634493).sum := by decide
  have hdescent : baseEnd_634493 < baseStart_634493 := by decide
  rcases family_descends (prefixWord ++ tailWord_634493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634503 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_634503 : Nat := 118140960795 + 634503 * 2 ^ 59
def prefixEnd_634503 : Nat := 4983230072969 + 3 ^ 40 * 634503 * 2
def baseEnd_634503 : Nat := 289604458417632211372871

theorem tailTrace_634503 : CollatzResearch.WordTrace tailWord_634503 prefixEnd_634503 289604458417632211372871 := by
  unfold tailWord_634503
  simp only [CollatzResearch.WordTrace]
  refine ⟨23142225620311470330172163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15428150413540980220114775 23142225620311470330172163)
  ·
    refine ⟨34713338430467205495258245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23142225620311470330172163 34713338430467205495258245)
    ·
      refine ⟨6508750955712601030360921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34713338430467205495258245 6508750955712601030360921)
      ·
        refine ⟨4881563216784450772770691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6508750955712601030360921 4881563216784450772770691)
        ·
          refine ⟨7322344825176676159156037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881563216784450772770691 7322344825176676159156037)
          ·
            refine ⟨1372939654720626779841757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7322344825176676159156037 1372939654720626779841757)
            ·
              refine ⟨514852370520235042440659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372939654720626779841757 514852370520235042440659)
              ·
                refine ⟨772278555780352563660989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514852370520235042440659 772278555780352563660989)
                ·
                  refine ⟨289604458417632211372871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772278555780352563660989 289604458417632211372871)
                  ·
                    rfl

theorem cell20_634503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_634503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634503 prefixEnd_634503 := by exact prefixLift 634503
  have htrace : WordTrace (prefixWord ++ tailWord_634503) baseStart_634503 baseEnd_634503 := by
    simpa [prefixWord, tailWord_634503, baseEnd_634503] using wordTrace_append hprefix tailTrace_634503
  have hstable : (prefixWord ++ tailWord_634503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634503).length < 2 ^ (prefixWord ++ tailWord_634503).sum := by decide
  have hdescent : baseEnd_634503 < baseStart_634503 := by decide
  rcases family_descends (prefixWord ++ tailWord_634503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634558 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_634558 : Nat := 118140960795 + 634558 * 2 ^ 59
def prefixEnd_634558 : Nat := 4983230072969 + 3 ^ 40 * 634558 * 2
def baseEnd_634558 : Nat := 289629561916296464539313

theorem tailTrace_634558 : CollatzResearch.WordTrace tailWord_634558 prefixEnd_634558 289629561916296464539313 := by
  unfold tailWord_634558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893028954389026840428041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15429487756741476482282885 2893028954389026840428041)
  ·
    refine ⟨2169771715791770130321031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2893028954389026840428041 2169771715791770130321031)
    ·
      refine ⟨3254657573687655195481547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169771715791770130321031 3254657573687655195481547)
      ·
        refine ⟨4881986360531482793222321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254657573687655195481547 4881986360531482793222321)
        ·
          refine ⟨3661489770398612094916741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4881986360531482793222321 3661489770398612094916741)
          ·
            refine ⟨686529331949739767796889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3661489770398612094916741 686529331949739767796889)
            ·
              refine ⟨514896998962304825847667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686529331949739767796889 514896998962304825847667)
              ·
                refine ⟨772345498443457238771501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514896998962304825847667 772345498443457238771501)
                ·
                  refine ⟨289629561916296464539313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772345498443457238771501 289629561916296464539313)
                  ·
                    rfl

theorem cell20_634558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_634558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634558 prefixEnd_634558 := by exact prefixLift 634558
  have htrace : WordTrace (prefixWord ++ tailWord_634558) baseStart_634558 baseEnd_634558 := by
    simpa [prefixWord, tailWord_634558, baseEnd_634558] using wordTrace_append hprefix tailTrace_634558
  have hstable : (prefixWord ++ tailWord_634558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634558).length < 2 ^ (prefixWord ++ tailWord_634558).sum := by decide
  have hdescent : baseEnd_634558 < baseStart_634558 := by decide
  rcases family_descends (prefixWord ++ tailWord_634558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634599 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 2]
def baseStart_634599 : Nat := 118140960795 + 634599 * 2 ^ 59
def prefixEnd_634599 : Nat := 4983230072969 + 3 ^ 40 * 634599 * 2
def baseEnd_634599 : Nat := 289648275433482544172479

theorem tailTrace_634599 : CollatzResearch.WordTrace tailWord_634599 prefixEnd_634599 289648275433482544172479 := by
  unfold tailWord_634599
  simp only [CollatzResearch.WordTrace]
  refine ⟨23145727027963678725666851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15430484685309119150444567 23145727027963678725666851)
  ·
    refine ⟨34718590541945518088500277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23145727027963678725666851 34718590541945518088500277)
    ·
      refine ⟨3254867863307392320796901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34718590541945518088500277 3254867863307392320796901)
      ·
        refine ⟨610287724370136060149419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3254867863307392320796901 610287724370136060149419)
        ·
          refine ⟨915431586555204090224129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610287724370136060149419 915431586555204090224129)
          ·
            refine ⟨686573689916403067668097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915431586555204090224129 686573689916403067668097)
            ·
              refine ⟨514930267437302300751073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686573689916403067668097 514930267437302300751073)
              ·
                refine ⟨386197700577976725563305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514930267437302300751073 386197700577976725563305)
                ·
                  refine ⟨289648275433482544172479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386197700577976725563305 289648275433482544172479)
                  ·
                    rfl

theorem cell20_634599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2].length) (baseStart_634599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634599 prefixEnd_634599 := by exact prefixLift 634599
  have htrace : WordTrace (prefixWord ++ tailWord_634599) baseStart_634599 baseEnd_634599 := by
    simpa [prefixWord, tailWord_634599, baseEnd_634599] using wordTrace_append hprefix tailTrace_634599
  have hstable : (prefixWord ++ tailWord_634599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634599).length < 2 ^ (prefixWord ++ tailWord_634599).sum := by decide
  have hdescent : baseEnd_634599 < baseStart_634599 := by decide
  rcases family_descends (prefixWord ++ tailWord_634599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634600 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_634600 : Nat := 118140960795 + 634600 * 2 ^ 59
def prefixEnd_634600 : Nat := 4983230072969 + 3 ^ 40 * 634600 * 2
def baseEnd_634600 : Nat := 289648731860730985139141

theorem tailTrace_634600 : CollatzResearch.WordTrace tailWord_634600 prefixEnd_634600 289648731860730985139141 := by
  unfold tailWord_634600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572881750480027948226627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15430509000640037264302169 11572881750480027948226627)
  ·
    refine ⟨17359322625720041922339941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11572881750480027948226627 17359322625720041922339941)
    ·
      refine ⟨3254872992322507860438739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17359322625720041922339941 3254872992322507860438739)
      ·
        refine ⟨4882309488483761790658109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254872992322507860438739 4882309488483761790658109)
        ·
          refine ⟨1830866058181410671496791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4882309488483761790658109 1830866058181410671496791)
          ·
            refine ⟨2746299087272116007245187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830866058181410671496791 2746299087272116007245187)
            ·
              refine ⟨4119448630908174010867781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746299087272116007245187 4119448630908174010867781)
              ·
                refine ⟨772396618295282627037709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4119448630908174010867781 772396618295282627037709)
                ·
                  refine ⟨289648731860730985139141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772396618295282627037709 289648731860730985139141)
                  ·
                    rfl

theorem cell20_634600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_634600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634600 prefixEnd_634600 := by exact prefixLift 634600
  have htrace : WordTrace (prefixWord ++ tailWord_634600) baseStart_634600 baseEnd_634600 := by
    simpa [prefixWord, tailWord_634600, baseEnd_634600] using wordTrace_append hprefix tailTrace_634600
  have hstable : (prefixWord ++ tailWord_634600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634600).length < 2 ^ (prefixWord ++ tailWord_634600).sum := by decide
  have hdescent : baseEnd_634600 < baseStart_634600 := by decide
  rcases family_descends (prefixWord ++ tailWord_634600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634635 : List Nat := [1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_634635 : Nat := 118140960795 + 634635 * 2 ^ 59
def prefixEnd_634635 : Nat := 4983230072969 + 3 ^ 40 * 634635 * 2
def baseEnd_634635 : Nat := 96554902271475472990777

theorem tailTrace_634635 : CollatzResearch.WordTrace tailWord_634635 prefixEnd_634635 96554902271475472990777 := by
  unfold tailWord_634635
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147040055833256873977359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431360037222171249318239 23147040055833256873977359)
  ·
    refine ⟨34720560083749885310966039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23147040055833256873977359 34720560083749885310966039)
    ·
      refine ⟨52080840125624827966449059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34720560083749885310966039 52080840125624827966449059)
      ·
        refine ⟨78121260188437241949673589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52080840125624827966449059 78121260188437241949673589)
        ·
          refine ⟨7323868142665991432781899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78121260188437241949673589 7323868142665991432781899)
          ·
            refine ⟨10985802213998987149172849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323868142665991432781899 10985802213998987149172849)
            ·
              refine ⟨8239351660499240361879637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10985802213998987149172849 8239351660499240361879637)
              ·
                refine ⟨96554902271475472990777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8239351660499240361879637 96554902271475472990777)
                ·
                  rfl

theorem cell20_634635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_634635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634635 prefixEnd_634635 := by exact prefixLift 634635
  have htrace : WordTrace (prefixWord ++ tailWord_634635) baseStart_634635 baseEnd_634635 := by
    simpa [prefixWord, tailWord_634635, baseEnd_634635] using wordTrace_append hprefix tailTrace_634635
  have hstable : (prefixWord ++ tailWord_634635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634635).length < 2 ^ (prefixWord ++ tailWord_634635).sum := by decide
  have hdescent : baseEnd_634635 < baseStart_634635 := by decide
  rcases family_descends (prefixWord ++ tailWord_634635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634686 : List Nat := [4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_634686 : Nat := 118140960795 + 634686 * 2 ^ 59
def prefixEnd_634686 : Nat := 4983230072969 + 3 ^ 40 * 634686 * 2
def baseEnd_634686 : Nat := 96562661534698969424041

theorem tailTrace_634686 : CollatzResearch.WordTrace tailWord_634686 prefixEnd_634686 96562661534698969424041 := by
  unfold tailWord_634686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893612522331061573010489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15432600119098995056055941 2893612522331061573010489)
  ·
    refine ⟨2170209391748296179757867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2893612522331061573010489 2170209391748296179757867)
    ·
      refine ⟨3255314087622444269636801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170209391748296179757867 3255314087622444269636801)
      ·
        refine ⟨2441485565716833202227601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3255314087622444269636801 2441485565716833202227601)
        ·
          refine ⟨1831114174287624901670701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2441485565716833202227601 1831114174287624901670701)
          ·
            refine ⟨686667815357859338126513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1831114174287624901670701 686667815357859338126513)
            ·
              refine ⟨515000861518394503594885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686667815357859338126513 515000861518394503594885)
              ·
                refine ⟨96562661534698969424041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515000861518394503594885 96562661534698969424041)
                ·
                  rfl

theorem cell20_634686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_634686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634686 prefixEnd_634686 := by exact prefixLift 634686
  have htrace : WordTrace (prefixWord ++ tailWord_634686) baseStart_634686 baseEnd_634686 := by
    simpa [prefixWord, tailWord_634686, baseEnd_634686] using wordTrace_append hprefix tailTrace_634686
  have hstable : (prefixWord ++ tailWord_634686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634686).length < 2 ^ (prefixWord ++ tailWord_634686).sum := by decide
  have hdescent : baseEnd_634686 < baseStart_634686 := by decide
  rcases family_descends (prefixWord ++ tailWord_634686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634728 : List Nat := [2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_634728 : Nat := 118140960795 + 634728 * 2 ^ 59
def prefixEnd_634728 : Nat := 4983230072969 + 3 ^ 40 * 634728 * 2
def baseEnd_634728 : Nat := 96569051516177142957317

theorem tailTrace_634728 : CollatzResearch.WordTrace tailWord_634728 prefixEnd_634728 96569051516177142957317 := by
  unfold tailWord_634728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575216022248166878556419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15433621362997555838075225 11575216022248166878556419)
  ·
    refine ⟨17362824033372250317834629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11575216022248166878556419 17362824033372250317834629)
    ·
      refine ⟨3255529506257296934593993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17362824033372250317834629 3255529506257296934593993)
      ·
        refine ⟨2441647129692972700945495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3255529506257296934593993 2441647129692972700945495)
        ·
          refine ⟨3662470694539459051418243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441647129692972700945495 3662470694539459051418243)
          ·
            refine ⟨5493706041809188577127365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662470694539459051418243 5493706041809188577127365)
            ·
              refine ⟨1030069882839222858211381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5493706041809188577127365 1030069882839222858211381)
              ·
                refine ⟨96569051516177142957317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030069882839222858211381 96569051516177142957317)
                ·
                  rfl

theorem cell20_634728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_634728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634728 prefixEnd_634728 := by exact prefixLift 634728
  have htrace : WordTrace (prefixWord ++ tailWord_634728) baseStart_634728 baseEnd_634728 := by
    simpa [prefixWord, tailWord_634728, baseEnd_634728] using wordTrace_append hprefix tailTrace_634728
  have hstable : (prefixWord ++ tailWord_634728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634728).length < 2 ^ (prefixWord ++ tailWord_634728).sum := by decide
  have hdescent : baseEnd_634728 < baseStart_634728 := by decide
  rcases family_descends (prefixWord ++ tailWord_634728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634766 : List Nat := [4, 1, 1, 5, 9]
def baseStart_634766 : Nat := 118140960795 + 634766 * 2 ^ 59
def prefixEnd_634766 : Nat := 4983230072969 + 3 ^ 40 * 634766 * 2
def baseEnd_634766 : Nat := 3576845663999656612409

theorem tailTrace_634766 : CollatzResearch.WordTrace tailWord_634766 prefixEnd_634766 3576845663999656612409 := by
  unfold tailWord_634766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893977252294833280874519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15434545345572444164664101 2893977252294833280874519)
  ·
    refine ⟨4340965878442249921311779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893977252294833280874519 4340965878442249921311779)
    ·
      refine ⟨6511448817663374881967669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340965878442249921311779 6511448817663374881967669)
      ·
        refine ⟨610448326655941395184469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6511448817663374881967669 610448326655941395184469)
        ·
          refine ⟨3576845663999656612409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 610448326655941395184469 3576845663999656612409)
          ·
            rfl

theorem cell20_634766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 9].length) (baseStart_634766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634766 prefixEnd_634766 := by exact prefixLift 634766
  have htrace : WordTrace (prefixWord ++ tailWord_634766) baseStart_634766 baseEnd_634766 := by
    simpa [prefixWord, tailWord_634766, baseEnd_634766] using wordTrace_append hprefix tailTrace_634766
  have hstable : (prefixWord ++ tailWord_634766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634766).length < 2 ^ (prefixWord ++ tailWord_634766).sum := by decide
  have hdescent : baseEnd_634766 < baseStart_634766 := by decide
  rcases family_descends (prefixWord ++ tailWord_634766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634772 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_634772 : Nat := 118140960795 + 634772 * 2 ^ 59
def prefixEnd_634772 : Nat := 4983230072969 + 3 ^ 40 * 634772 * 2
def baseEnd_634772 : Nat := 289727237347462831405105

theorem tailTrace_634772 : CollatzResearch.WordTrace tailWord_634772 prefixEnd_634772 289727237347462831405105 := by
  unfold tailWord_634772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576018428168464635857285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15434691237557952847809713 11576018428168464635857285)
  ·
    refine ⟨2170503455281587119223241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11576018428168464635857285 2170503455281587119223241)
    ·
      refine ⟨1627877591461190339417431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2170503455281587119223241 1627877591461190339417431)
      ·
        refine ⟨2441816387191785509126147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627877591461190339417431 2441816387191785509126147)
        ·
          refine ⟨3662724580787678263689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441816387191785509126147 3662724580787678263689221)
          ·
            refine ⟨686760858897689674441729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3662724580787678263689221 686760858897689674441729)
            ·
              refine ⟨515070644173267255831297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686760858897689674441729 515070644173267255831297)
              ·
                refine ⟨386302983129950441873473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515070644173267255831297 386302983129950441873473)
                ·
                  refine ⟨289727237347462831405105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386302983129950441873473 289727237347462831405105)
                  ·
                    rfl

theorem cell20_634772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_634772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634772 prefixEnd_634772 := by exact prefixLift 634772
  have htrace : WordTrace (prefixWord ++ tailWord_634772) baseStart_634772 baseEnd_634772 := by
    simpa [prefixWord, tailWord_634772, baseEnd_634772] using wordTrace_append hprefix tailTrace_634772
  have hstable : (prefixWord ++ tailWord_634772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634772).length < 2 ^ (prefixWord ++ tailWord_634772).sum := by decide
  have hdescent : baseEnd_634772 < baseStart_634772 := by decide
  rcases family_descends (prefixWord ++ tailWord_634772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634783 : List Nat := [1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_634783 : Nat := 118140960795 + 634783 * 2 ^ 59
def prefixEnd_634783 : Nat := 4983230072969 + 3 ^ 40 * 634783 * 2
def baseEnd_634783 : Nat := 96577419349065227346131

theorem tailTrace_634783 : CollatzResearch.WordTrace tailWord_634783 prefixEnd_634783 96577419349065227346131 := by
  unfold tailWord_634783
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152438059297078150365003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15434958706198052100243335 23152438059297078150365003)
  ·
    refine ⟨34728657088945617225547505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23152438059297078150365003 34728657088945617225547505)
    ·
      refine ⟨26046492816709212919160629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34728657088945617225547505 26046492816709212919160629)
      ·
        refine ⟨2441858701566488711171309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26046492816709212919160629 2441858701566488711171309)
        ·
          refine ⟨915697013087433266689241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2441858701566488711171309 915697013087433266689241)
          ·
            refine ⟨686772759815574950016931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915697013087433266689241 686772759815574950016931)
            ·
              refine ⟨1030159139723362425025397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686772759815574950016931 1030159139723362425025397)
              ·
                refine ⟨96577419349065227346131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030159139723362425025397 96577419349065227346131)
                ·
                  rfl

theorem cell20_634783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_634783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634783 prefixEnd_634783 := by exact prefixLift 634783
  have htrace : WordTrace (prefixWord ++ tailWord_634783) baseStart_634783 baseEnd_634783 := by
    simpa [prefixWord, tailWord_634783, baseEnd_634783] using wordTrace_append hprefix tailTrace_634783
  have hstable : (prefixWord ++ tailWord_634783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634783).length < 2 ^ (prefixWord ++ tailWord_634783).sum := by decide
  have hdescent : baseEnd_634783 < baseStart_634783 := by decide
  rcases family_descends (prefixWord ++ tailWord_634783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634814 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_634814 : Nat := 118140960795 + 634814 * 2 ^ 59
def prefixEnd_634814 : Nat := 4983230072969 + 3 ^ 40 * 634814 * 2
def baseEnd_634814 : Nat := 289746407291897352004933

theorem tailTrace_634814 : CollatzResearch.WordTrace tailWord_634814 prefixEnd_634814 289746407291897352004933 := by
  unfold tailWord_634814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894196090273096305592937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15435712481456513629828997 2894196090273096305592937)
  ·
    refine ⟨2170647067704822229194703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2894196090273096305592937 2170647067704822229194703)
    ·
      refine ⟨3255970601557233343792055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170647067704822229194703 3255970601557233343792055)
      ·
        refine ⟨4883955902335850015688083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255970601557233343792055 4883955902335850015688083)
        ·
          refine ⟨7325933853503775023532125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883955902335850015688083 7325933853503775023532125)
          ·
            refine ⟨2747225195063915633824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325933853503775023532125 2747225195063915633824547)
            ·
              refine ⟨4120837792595873450736821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747225195063915633824547 4120837792595873450736821)
              ·
                refine ⟨386328543055863136006577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4120837792595873450736821 386328543055863136006577)
                ·
                  refine ⟨289746407291897352004933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386328543055863136006577 289746407291897352004933)
                  ·
                    rfl

theorem cell20_634814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_634814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634814 prefixEnd_634814 := by exact prefixLift 634814
  have htrace : WordTrace (prefixWord ++ tailWord_634814) baseStart_634814 baseEnd_634814 := by
    simpa [prefixWord, tailWord_634814, baseEnd_634814] using wordTrace_append hprefix tailTrace_634814
  have hstable : (prefixWord ++ tailWord_634814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634814).length < 2 ^ (prefixWord ++ tailWord_634814).sum := by decide
  have hdescent : baseEnd_634814 < baseStart_634814 := by decide
  rcases family_descends (prefixWord ++ tailWord_634814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634828 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_634828 : Nat := 118140960795 + 634828 * 2 ^ 59
def prefixEnd_634828 : Nat := 4983230072969 + 3 ^ 40 * 634828 * 2
def baseEnd_634828 : Nat := 289752797273375525538209

theorem tailTrace_634828 : CollatzResearch.WordTrace tailWord_634828 prefixEnd_634828 289752797273375525538209 := by
  unfold tailWord_634828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577039672067025417876569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15436052896089367223835425 11577039672067025417876569)
  ·
    refine ⟨8682779754050269063407427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11577039672067025417876569 8682779754050269063407427)
    ·
      refine ⟨13024169631075403595111141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682779754050269063407427 13024169631075403595111141)
      ·
        refine ⟨2442031805826638174083339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13024169631075403595111141 2442031805826638174083339)
        ·
          refine ⟨3663047708739957261125009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442031805826638174083339 3663047708739957261125009)
          ·
            refine ⟨2747285781554967945843757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663047708739957261125009 2747285781554967945843757)
            ·
              refine ⟨1030232168083112979691409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2747285781554967945843757 1030232168083112979691409)
              ·
                refine ⟨772674126062334734768557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030232168083112979691409 772674126062334734768557)
                ·
                  refine ⟨289752797273375525538209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772674126062334734768557 289752797273375525538209)
                  ·
                    rfl

theorem cell20_634828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_634828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634828 prefixEnd_634828 := by exact prefixLift 634828
  have htrace : WordTrace (prefixWord ++ tailWord_634828) baseStart_634828 baseEnd_634828 := by
    simpa [prefixWord, tailWord_634828, baseEnd_634828] using wordTrace_append hprefix tailTrace_634828
  have hstable : (prefixWord ++ tailWord_634828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634828).length < 2 ^ (prefixWord ++ tailWord_634828).sum := by decide
  have hdescent : baseEnd_634828 < baseStart_634828 := by decide
  rcases family_descends (prefixWord ++ tailWord_634828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634849 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_634849 : Nat := 118140960795 + 634849 * 2 ^ 59
def prefixEnd_634849 : Nat := 4983230072969 + 3 ^ 40 * 634849 * 2
def baseEnd_634849 : Nat := 289762382245592785838123

theorem tailTrace_634849 : CollatzResearch.WordTrace tailWord_634849 prefixEnd_634849 289762382245592785838123 := by
  unfold tailWord_634849
  simp only [CollatzResearch.WordTrace]
  refine ⟨23154845277057971422267601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15436563518038647614845067 23154845277057971422267601)
  ·
    refine ⟨17366133957793478566700701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23154845277057971422267601 17366133957793478566700701)
    ·
      refine ⟨6512300234172554462512763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17366133957793478566700701 6512300234172554462512763)
      ·
        refine ⟨9768450351258831693769145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512300234172554462512763 9768450351258831693769145)
        ·
          refine ⟨7326337763444123770326859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9768450351258831693769145 7326337763444123770326859)
          ·
            refine ⟨10989506645166185655490289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7326337763444123770326859 10989506645166185655490289)
            ·
              refine ⟨8242129983874639241617717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10989506645166185655490289 8242129983874639241617717)
              ·
                refine ⟨772699685988247428901661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8242129983874639241617717 772699685988247428901661)
                ·
                  refine ⟨289762382245592785838123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772699685988247428901661 289762382245592785838123)
                  ·
                    rfl

theorem cell20_634849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_634849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634849 prefixEnd_634849 := by exact prefixLift 634849
  have htrace : WordTrace (prefixWord ++ tailWord_634849) baseStart_634849 baseEnd_634849 := by
    simpa [prefixWord, tailWord_634849, baseEnd_634849] using wordTrace_append hprefix tailTrace_634849
  have hstable : (prefixWord ++ tailWord_634849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634849).length < 2 ^ (prefixWord ++ tailWord_634849).sum := by decide
  have hdescent : baseEnd_634849 < baseStart_634849 := by decide
  rcases family_descends (prefixWord ++ tailWord_634849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634863 : List Nat := [1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_634863 : Nat := 118140960795 + 634863 * 2 ^ 59
def prefixEnd_634863 : Nat := 4983230072969 + 3 ^ 40 * 634863 * 2
def baseEnd_634863 : Nat := 96589590742356986457133

theorem tailTrace_634863 : CollatzResearch.WordTrace tailWord_634863 prefixEnd_634863 96589590742356986457133 := by
  unfold tailWord_634863
  simp only [CollatzResearch.WordTrace]
  refine ⟨23155355899007251813277243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15436903932671501208851495 23155355899007251813277243)
  ·
    refine ⟨34733033848510877719915865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23155355899007251813277243 34733033848510877719915865)
    ·
      refine ⟨26049775386383158289936899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34733033848510877719915865 26049775386383158289936899)
      ·
        refine ⟨39074663079574737434905349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26049775386383158289936899 39074663079574737434905349)
        ·
          refine ⟨7326499327420263269044753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39074663079574737434905349 7326499327420263269044753)
          ·
            refine ⟨5494874495565197451783565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7326499327420263269044753 5494874495565197451783565)
            ·
              refine ⟨2060577935836949044418837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5494874495565197451783565 2060577935836949044418837)
              ·
                refine ⟨96589590742356986457133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2060577935836949044418837 96589590742356986457133)
                ·
                  rfl

theorem cell20_634863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_634863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634863 prefixEnd_634863 := by exact prefixLift 634863
  have htrace : WordTrace (prefixWord ++ tailWord_634863) baseStart_634863 baseEnd_634863 := by
    simpa [prefixWord, tailWord_634863, baseEnd_634863] using wordTrace_append hprefix tailTrace_634863
  have hstable : (prefixWord ++ tailWord_634863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634863).length < 2 ^ (prefixWord ++ tailWord_634863).sum := by decide
  have hdescent : baseEnd_634863 < baseStart_634863 := by decide
  rcases family_descends (prefixWord ++ tailWord_634863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634887 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_634887 : Nat := 118140960795 + 634887 * 2 ^ 59
def prefixEnd_634887 : Nat := 4983230072969 + 3 ^ 40 * 634887 * 2
def baseEnd_634887 : Nat := 289779726481033542571301

theorem tailTrace_634887 : CollatzResearch.WordTrace tailWord_634887 prefixEnd_634887 289779726481033542571301 := by
  unfold tailWord_634887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23156231250920303912150915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15437487500613535941433943 23156231250920303912150915)
  ·
    refine ⟨34734346876380455868226373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23156231250920303912150915 34734346876380455868226373)
    ·
      refine ⟨6512690039321335475292445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34734346876380455868226373 6512690039321335475292445)
      ·
        refine ⟨2442258764745500803234667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6512690039321335475292445 2442258764745500803234667)
        ·
          refine ⟨3663388147118251204852001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442258764745500803234667 3663388147118251204852001)
          ·
            refine ⟨2747541110338688403639001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663388147118251204852001 2747541110338688403639001)
            ·
              refine ⟨2060655832754016302729251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747541110338688403639001 2060655832754016302729251)
              ·
                refine ⟨3090983749131024454093877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060655832754016302729251 3090983749131024454093877)
                ·
                  refine ⟨289779726481033542571301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3090983749131024454093877 289779726481033542571301)
                  ·
                    rfl

theorem cell20_634887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_634887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634887 prefixEnd_634887 := by exact prefixLift 634887
  have htrace : WordTrace (prefixWord ++ tailWord_634887) baseStart_634887 baseEnd_634887 := by
    simpa [prefixWord, tailWord_634887, baseEnd_634887] using wordTrace_append hprefix tailTrace_634887
  have hstable : (prefixWord ++ tailWord_634887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634887).length < 2 ^ (prefixWord ++ tailWord_634887).sum := by decide
  have hdescent : baseEnd_634887 < baseStart_634887 := by decide
  rcases family_descends (prefixWord ++ tailWord_634887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634890 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_634890 : Nat := 118140960795 + 634890 * 2 ^ 59
def prefixEnd_634890 : Nat := 4983230072969 + 3 ^ 40 * 634890 * 2
def baseEnd_634890 : Nat := 289781095762778865471289

theorem tailTrace_634890 : CollatzResearch.WordTrace tailWord_634890 prefixEnd_634890 289781095762778865471289 := by
  unfold tailWord_634890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789085167477358856127531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15437560446606290283006749 5789085167477358856127531)
  ·
    refine ⟨8683627751216038284191297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5789085167477358856127531 8683627751216038284191297)
    ·
      refine ⟨6512720813412028713143473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8683627751216038284191297 6512720813412028713143473)
      ·
        refine ⟨4884540610059021534857605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6512720813412028713143473 4884540610059021534857605)
        ·
          refine ⟨915851364386066537785801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4884540610059021534857605 915851364386066537785801)
          ·
            refine ⟨686888523289549903339351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915851364386066537785801 686888523289549903339351)
            ·
              refine ⟨1030332784934324855009027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686888523289549903339351 1030332784934324855009027)
              ·
                refine ⟨1545499177401487282513541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030332784934324855009027 1545499177401487282513541)
                ·
                  refine ⟨289781095762778865471289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545499177401487282513541 289781095762778865471289)
                  ·
                    rfl

theorem cell20_634890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_634890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634890 prefixEnd_634890 := by exact prefixLift 634890
  have htrace : WordTrace (prefixWord ++ tailWord_634890) baseStart_634890 baseEnd_634890 := by
    simpa [prefixWord, tailWord_634890, baseEnd_634890] using wordTrace_append hprefix tailTrace_634890
  have hstable : (prefixWord ++ tailWord_634890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634890).length < 2 ^ (prefixWord ++ tailWord_634890).sum := by decide
  have hdescent : baseEnd_634890 < baseStart_634890 := by decide
  rcases family_descends (prefixWord ++ tailWord_634890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634893 : List Nat := [1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_634893 : Nat := 118140960795 + 634893 * 2 ^ 59
def prefixEnd_634893 : Nat := 4983230072969 + 3 ^ 40 * 634893 * 2
def baseEnd_634893 : Nat := 96594155014841396123759

theorem tailTrace_634893 : CollatzResearch.WordTrace tailWord_634893 prefixEnd_634893 96594155014841396123759 := by
  unfold tailWord_634893
  simp only [CollatzResearch.WordTrace]
  refine ⟨23156450088898566936869333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15437633392599044624579555 23156450088898566936869333)
  ·
    refine ⟨542729298958560162582875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23156450088898566936869333 542729298958560162582875)
    ·
      refine ⟨814093948437840243874313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542729298958560162582875 814093948437840243874313)
      ·
        refine ⟨610570461328380182905735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814093948437840243874313 610570461328380182905735)
        ·
          refine ⟨915855691992570274358603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610570461328380182905735 915855691992570274358603)
          ·
            refine ⟨1373783537988855411537905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915855691992570274358603 1373783537988855411537905)
            ·
              refine ⟨1030337653491641558653429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373783537988855411537905 1030337653491641558653429)
              ·
                refine ⟨96594155014841396123759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030337653491641558653429 96594155014841396123759)
                ·
                  rfl

theorem cell20_634893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_634893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634893 prefixEnd_634893 := by exact prefixLift 634893
  have htrace : WordTrace (prefixWord ++ tailWord_634893) baseStart_634893 baseEnd_634893 := by
    simpa [prefixWord, tailWord_634893, baseEnd_634893] using wordTrace_append hprefix tailTrace_634893
  have hstable : (prefixWord ++ tailWord_634893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634893).length < 2 ^ (prefixWord ++ tailWord_634893).sum := by decide
  have hdescent : baseEnd_634893 < baseStart_634893 := by decide
  rcases family_descends (prefixWord ++ tailWord_634893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634900 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_634900 : Nat := 118140960795 + 634900 * 2 ^ 59
def prefixEnd_634900 : Nat := 4983230072969 + 3 ^ 40 * 634900 * 2
def baseEnd_634900 : Nat := 289785660035263275137915

theorem tailTrace_634900 : CollatzResearch.WordTrace tailWord_634900 prefixEnd_634900 289785660035263275137915 := by
  unfold tailWord_634900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578352699936603566187077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15437803599915471421582769 11578352699936603566187077)
  ·
    refine ⟨2170941131238113168660077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11578352699936603566187077 2170941131238113168660077)
    ·
      refine ⟨814102924214292438247529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2170941131238113168660077 814102924214292438247529)
      ·
        refine ⟨610577193160719328685647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814102924214292438247529 610577193160719328685647)
        ·
          refine ⟨915865789741078993028471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610577193160719328685647 915865789741078993028471)
          ·
            refine ⟨1373798684611618489542707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915865789741078993028471 1373798684611618489542707)
            ·
              refine ⟨2060698026917427734314061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373798684611618489542707 2060698026917427734314061)
              ·
                refine ⟨772761760094035400367773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060698026917427734314061 772761760094035400367773)
                ·
                  refine ⟨289785660035263275137915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772761760094035400367773 289785660035263275137915)
                  ·
                    rfl

theorem cell20_634900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_634900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634900 prefixEnd_634900 := by exact prefixLift 634900
  have htrace : WordTrace (prefixWord ++ tailWord_634900) baseStart_634900 baseEnd_634900 := by
    simpa [prefixWord, tailWord_634900, baseEnd_634900] using wordTrace_append hprefix tailTrace_634900
  have hstable : (prefixWord ++ tailWord_634900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634900).length < 2 ^ (prefixWord ++ tailWord_634900).sum := by decide
  have hdescent : baseEnd_634900 < baseStart_634900 := by decide
  rcases family_descends (prefixWord ++ tailWord_634900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634945 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 2]
def baseStart_634945 : Nat := 118140960795 + 634945 * 2 ^ 59
def prefixEnd_634945 : Nat := 4983230072969 + 3 ^ 40 * 634945 * 2
def baseEnd_634945 : Nat := 289806199261443118637731

theorem tailTrace_634945 : CollatzResearch.WordTrace tailWord_634945 prefixEnd_634945 289806199261443118637731 := by
  unfold tailWord_634945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158346684710179817762289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15438897789806786545174859 23158346684710179817762289)
  ·
    refine ⟨17368760013532634863321717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23158346684710179817762289 17368760013532634863321717)
    ·
      refine ⟨1628321251268684518436411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17368760013532634863321717 1628321251268684518436411)
      ·
        refine ⟨2442481876903026777654617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628321251268684518436411 2442481876903026777654617)
        ·
          refine ⟨1831861407677270083240963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442481876903026777654617 1831861407677270083240963)
          ·
            refine ⟨2747792111515905124861445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831861407677270083240963 2747792111515905124861445)
            ·
              refine ⟨515211020909232210911521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2747792111515905124861445 515211020909232210911521)
              ·
                refine ⟨386408265681924158183641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515211020909232210911521 386408265681924158183641)
                ·
                  refine ⟨289806199261443118637731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386408265681924158183641 289806199261443118637731)
                  ·
                    rfl

theorem cell20_634945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_634945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634945 prefixEnd_634945 := by exact prefixLift 634945
  have htrace : WordTrace (prefixWord ++ tailWord_634945) baseStart_634945 baseEnd_634945 := by
    simpa [prefixWord, tailWord_634945, baseEnd_634945] using wordTrace_append hprefix tailTrace_634945
  have hstable : (prefixWord ++ tailWord_634945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634945).length < 2 ^ (prefixWord ++ tailWord_634945).sum := by decide
  have hdescent : baseEnd_634945 < baseStart_634945 := by decide
  rcases family_descends (prefixWord ++ tailWord_634945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634966 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_634966 : Nat := 118140960795 + 634966 * 2 ^ 59
def prefixEnd_634966 : Nat := 4983230072969 + 3 ^ 40 * 634966 * 2
def baseEnd_634966 : Nat := 289815784233660378937645

theorem tailTrace_634966 : CollatzResearch.WordTrace tailWord_634966 prefixEnd_634966 289815784233660378937645 := by
  unfold tailWord_634966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447444538602131275267297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15439408411756066936184501 1447444538602131275267297)
  ·
    refine ⟨1085583403951598456450473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1447444538602131275267297 1085583403951598456450473)
    ·
      refine ⟨814187552963698842337855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085583403951598456450473 814187552963698842337855)
      ·
        refine ⟨1221281329445548263506783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814187552963698842337855 1221281329445548263506783)
        ·
          refine ⟨1831921994168322395260175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221281329445548263506783 1831921994168322395260175)
          ·
            refine ⟨2747882991252483592890263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831921994168322395260175 2747882991252483592890263)
            ·
              refine ⟨4121824486878725389335395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747882991252483592890263 4121824486878725389335395)
              ·
                refine ⟨6182736730318088084003093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121824486878725389335395 6182736730318088084003093)
                ·
                  refine ⟨289815784233660378937645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6182736730318088084003093 289815784233660378937645)
                  ·
                    rfl

theorem cell20_634966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_634966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634966 prefixEnd_634966 := by exact prefixLift 634966
  have htrace : WordTrace (prefixWord ++ tailWord_634966) baseStart_634966 baseEnd_634966 := by
    simpa [prefixWord, tailWord_634966, baseEnd_634966] using wordTrace_append hprefix tailTrace_634966
  have hstable : (prefixWord ++ tailWord_634966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634966).length < 2 ^ (prefixWord ++ tailWord_634966).sum := by decide
  have hdescent : baseEnd_634966 < baseStart_634966 := by decide
  rcases family_descends (prefixWord ++ tailWord_634966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634970 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_634970 : Nat := 118140960795 + 634970 * 2 ^ 59
def prefixEnd_634970 : Nat := 4983230072969 + 3 ^ 40 * 634970 * 2
def baseEnd_634970 : Nat := 289817609942654142804295

theorem tailTrace_634970 : CollatzResearch.WordTrace tailWord_634970 prefixEnd_634970 289817609942654142804295 := by
  unfold tailWord_634970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789814627404902271855591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15439505673079739391614909 5789814627404902271855591)
  ·
    refine ⟨8684721941107353407783387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5789814627404902271855591 8684721941107353407783387)
    ·
      refine ⟨13027082911661030111675081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8684721941107353407783387 13027082911661030111675081)
      ·
        refine ⟨9770312183745772583756311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13027082911661030111675081 9770312183745772583756311)
        ·
          refine ⟨14655468275618658875634467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9770312183745772583756311 14655468275618658875634467)
          ·
            refine ⟨21983202413427988313451701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14655468275618658875634467 21983202413427988313451701)
            ·
              refine ⟨2060925226258873904386097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21983202413427988313451701 2060925226258873904386097)
              ·
                refine ⟨1545693919694155428289573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060925226258873904386097 1545693919694155428289573)
                ·
                  refine ⟨289817609942654142804295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545693919694155428289573 289817609942654142804295)
                  ·
                    rfl

theorem cell20_634970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_634970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_634970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_634970 prefixEnd_634970 := by exact prefixLift 634970
  have htrace : WordTrace (prefixWord ++ tailWord_634970) baseStart_634970 baseEnd_634970 := by
    simpa [prefixWord, tailWord_634970, baseEnd_634970] using wordTrace_append hprefix tailTrace_634970
  have hstable : (prefixWord ++ tailWord_634970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634970).length < 2 ^ (prefixWord ++ tailWord_634970).sum := by decide
  have hdescent : baseEnd_634970 < baseStart_634970 := by decide
  rcases family_descends (prefixWord ++ tailWord_634970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635001 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_635001 : Nat := 118140960795 + 635001 * 2 ^ 59
def prefixEnd_635001 : Nat := 4983230072969 + 3 ^ 40 * 635001 * 2
def baseEnd_635001 : Nat := 289831759187355812770835

theorem tailTrace_635001 : CollatzResearch.WordTrace tailWord_635001 prefixEnd_635001 289831759187355812770835 := by
  unfold tailWord_635001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160389172507301381800857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15440259448338200921200571 23160389172507301381800857)
  ·
    refine ⟨17370291879380476036350643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23160389172507301381800857 17370291879380476036350643)
    ·
      refine ⟨26055437819070714054525965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17370291879380476036350643 26055437819070714054525965)
      ·
        refine ⟨9770789182151517770447237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26055437819070714054525965 9770789182151517770447237)
        ·
          refine ⟨1832022971653409581958857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9770789182151517770447237 1832022971653409581958857)
          ·
            refine ⟨1374017228740057186469143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832022971653409581958857 1374017228740057186469143)
            ·
              refine ⟨2061025843110085779703715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374017228740057186469143 2061025843110085779703715)
              ·
                refine ⟨3091538764665128669555573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061025843110085779703715 3091538764665128669555573)
                ·
                  refine ⟨289831759187355812770835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091538764665128669555573 289831759187355812770835)
                  ·
                    rfl

theorem cell20_635001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_635001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635001 prefixEnd_635001 := by exact prefixLift 635001
  have htrace : WordTrace (prefixWord ++ tailWord_635001) baseStart_635001 baseEnd_635001 := by
    simpa [prefixWord, tailWord_635001, baseEnd_635001] using wordTrace_append hprefix tailTrace_635001
  have hstable : (prefixWord ++ tailWord_635001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635001).length < 2 ^ (prefixWord ++ tailWord_635001).sum := by decide
  have hdescent : baseEnd_635001 < baseStart_635001 := by decide
  rcases family_descends (prefixWord ++ tailWord_635001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635032 : List Nat := [2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_635032 : Nat := 118140960795 + 635032 * 2 ^ 59
def prefixEnd_635032 : Nat := 4983230072969 + 3 ^ 40 * 635032 * 2
def baseEnd_635032 : Nat := 96615302810685827579125

theorem tailTrace_635032 : CollatzResearch.WordTrace tailWord_635032 prefixEnd_635032 96615302810685827579125 := by
  unfold tailWord_635032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580759917697496838089675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15441013223596662450786233 11580759917697496838089675)
  ·
    refine ⟨17371139876546245257134513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11580759917697496838089675 17371139876546245257134513)
    ·
      refine ⟨13028354907409683942850885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17371139876546245257134513 13028354907409683942850885)
      ·
        refine ⟨2442816545139315739284541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13028354907409683942850885 2442816545139315739284541)
        ·
          refine ⟨916056204427243402231703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2442816545139315739284541 916056204427243402231703)
          ·
            refine ⟨1374084306640865103347555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916056204427243402231703 1374084306640865103347555)
            ·
              refine ⟨2061126459961297655021333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374084306640865103347555 2061126459961297655021333)
              ·
                refine ⟨96615302810685827579125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2061126459961297655021333 96615302810685827579125)
                ·
                  rfl

theorem cell20_635032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_635032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635032 prefixEnd_635032 := by exact prefixLift 635032
  have htrace : WordTrace (prefixWord ++ tailWord_635032) baseStart_635032 baseEnd_635032 := by
    simpa [prefixWord, tailWord_635032, baseEnd_635032] using wordTrace_append hprefix tailTrace_635032
  have hstable : (prefixWord ++ tailWord_635032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635032).length < 2 ^ (prefixWord ++ tailWord_635032).sum := by decide
  have hdescent : baseEnd_635032 < baseStart_635032 := by decide
  rcases family_descends (prefixWord ++ tailWord_635032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635038 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_635038 : Nat := 118140960795 + 635038 * 2 ^ 59
def prefixEnd_635038 : Nat := 4983230072969 + 3 ^ 40 * 635038 * 2
def baseEnd_635038 : Nat := 289848646995548128537351

theorem tailTrace_635038 : CollatzResearch.WordTrace tailWord_635038 prefixEnd_635038 289848646995548128537351 := by
  unfold tailWord_635038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895217334171657087612221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15441159115582171133931845 2895217334171657087612221)
  ·
    refine ⟨1085706500314371407854583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2895217334171657087612221 1085706500314371407854583)
    ·
      refine ⟨1628559750471557111781875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085706500314371407854583 1628559750471557111781875)
      ·
        refine ⟨2442839625707335667672813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628559750471557111781875 2442839625707335667672813)
        ·
          refine ⟨916064859640250875377305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2442839625707335667672813 916064859640250875377305)
          ·
            refine ⟨687048644730188156532979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916064859640250875377305 687048644730188156532979)
            ·
              refine ⟨1030572967095282234799469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687048644730188156532979 1030572967095282234799469)
              ·
                refine ⟨386464862660730838049801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1030572967095282234799469 386464862660730838049801)
                ·
                  refine ⟨289848646995548128537351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386464862660730838049801 289848646995548128537351)
                  ·
                    rfl

theorem cell20_635038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_635038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635038 prefixEnd_635038 := by exact prefixLift 635038
  have htrace : WordTrace (prefixWord ++ tailWord_635038) baseStart_635038 baseEnd_635038 := by
    simpa [prefixWord, tailWord_635038, baseEnd_635038] using wordTrace_append hprefix tailTrace_635038
  have hstable : (prefixWord ++ tailWord_635038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635038).length < 2 ^ (prefixWord ++ tailWord_635038).sum := by decide
  have hdescent : baseEnd_635038 < baseStart_635038 := by decide
  rcases family_descends (prefixWord ++ tailWord_635038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635039 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_635039 : Nat := 118140960795 + 635039 * 2 ^ 59
def prefixEnd_635039 : Nat := 4983230072969 + 3 ^ 40 * 635039 * 2
def baseEnd_635039 : Nat := 289849103422796569504013

theorem tailTrace_635039 : CollatzResearch.WordTrace tailWord_635039 prefixEnd_635039 289849103422796569504013 := by
  unfold tailWord_635039
  simp only [CollatzResearch.WordTrace]
  refine ⟨23161775146369633871684171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15441183430913089247789447 23161775146369633871684171)
  ·
    refine ⟨34742662719554450807526257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23161775146369633871684171 34742662719554450807526257)
    ·
      refine ⟨26056997039665838105644693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34742662719554450807526257 26056997039665838105644693)
      ·
        refine ⟨1221421736234336161202095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26056997039665838105644693 1221421736234336161202095)
        ·
          refine ⟨1832132604351504241803143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221421736234336161202095 1832132604351504241803143)
          ·
            refine ⟨2748198906527256362704715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832132604351504241803143 2748198906527256362704715)
            ·
              refine ⟨4122298359790884544057073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748198906527256362704715 4122298359790884544057073)
              ·
                refine ⟨3091723769843163408042805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122298359790884544057073 3091723769843163408042805)
                ·
                  refine ⟨289849103422796569504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091723769843163408042805 289849103422796569504013)
                  ·
                    rfl

theorem cell20_635039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_635039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635039 prefixEnd_635039 := by exact prefixLift 635039
  have htrace : WordTrace (prefixWord ++ tailWord_635039) baseStart_635039 baseEnd_635039 := by
    simpa [prefixWord, tailWord_635039, baseEnd_635039] using wordTrace_append hprefix tailTrace_635039
  have hstable : (prefixWord ++ tailWord_635039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635039).length < 2 ^ (prefixWord ++ tailWord_635039).sum := by decide
  have hdescent : baseEnd_635039 < baseStart_635039 := by decide
  rcases family_descends (prefixWord ++ tailWord_635039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635063 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_635063 : Nat := 118140960795 + 635063 * 2 ^ 59
def prefixEnd_635063 : Nat := 4983230072969 + 3 ^ 40 * 635063 * 2
def baseEnd_635063 : Nat := 289860057676759152703915

theorem tailTrace_635063 : CollatzResearch.WordTrace tailWord_635063 prefixEnd_635063 289860057676759152703915 := by
  unfold tailWord_635063
  simp only [CollatzResearch.WordTrace]
  refine ⟨23162650498282685970557843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15441766998855123980371895 23162650498282685970557843)
  ·
    refine ⟨34743975747424028955836765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23162650498282685970557843 34743975747424028955836765)
    ·
      refine ⟨13028990905284010858438787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34743975747424028955836765 13028990905284010858438787)
      ·
        refine ⟨19543486357926016287658181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13028990905284010858438787 19543486357926016287658181)
        ·
          refine ⟨3664403692111128053935909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19543486357926016287658181 3664403692111128053935909)
          ·
            refine ⟨687075692270836510112983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3664403692111128053935909 687075692270836510112983)
            ·
              refine ⟨1030613538406254765169475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687075692270836510112983 1030613538406254765169475)
              ·
                refine ⟨1545920307609382147754213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030613538406254765169475 1545920307609382147754213)
                ·
                  refine ⟨289860057676759152703915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545920307609382147754213 289860057676759152703915)
                  ·
                    rfl

theorem cell20_635063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_635063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635063 prefixEnd_635063 := by exact prefixLift 635063
  have htrace : WordTrace (prefixWord ++ tailWord_635063) baseStart_635063 baseEnd_635063 := by
    simpa [prefixWord, tailWord_635063, baseEnd_635063] using wordTrace_append hprefix tailTrace_635063
  have hstable : (prefixWord ++ tailWord_635063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635063).length < 2 ^ (prefixWord ++ tailWord_635063).sum := by decide
  have hdescent : baseEnd_635063 < baseStart_635063 := by decide
  rcases family_descends (prefixWord ++ tailWord_635063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635073 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_635073 : Nat := 118140960795 + 635073 * 2 ^ 59
def prefixEnd_635073 : Nat := 4983230072969 + 3 ^ 40 * 635073 * 2
def baseEnd_635073 : Nat := 289864621949243562370541

theorem tailTrace_635073 : CollatzResearch.WordTrace tailWord_635073 prefixEnd_635073 289864621949243562370541 := by
  unfold tailWord_635073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163015228246457678421873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15442010152164305118947915 23163015228246457678421873)
  ·
    refine ⟨17372261421184843258816405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23163015228246457678421873 17372261421184843258816405)
    ·
      refine ⟨814324754118039527757019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17372261421184843258816405 814324754118039527757019)
      ·
        refine ⟨1221487131177059291635529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814324754118039527757019 1221487131177059291635529)
        ·
          refine ⟨916115348382794468726647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221487131177059291635529 916115348382794468726647)
          ·
            refine ⟨1374173022574191703089971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916115348382794468726647 1374173022574191703089971)
            ·
              refine ⟨2061259533861287554634957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374173022574191703089971 2061259533861287554634957)
              ·
                refine ⟨772972325197982832988109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2061259533861287554634957 772972325197982832988109)
                ·
                  refine ⟨289864621949243562370541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772972325197982832988109 289864621949243562370541)
                  ·
                    rfl

theorem cell20_635073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_635073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635073 prefixEnd_635073 := by exact prefixLift 635073
  have htrace : WordTrace (prefixWord ++ tailWord_635073) baseStart_635073 baseEnd_635073 := by
    simpa [prefixWord, tailWord_635073, baseEnd_635073] using wordTrace_append hprefix tailTrace_635073
  have hstable : (prefixWord ++ tailWord_635073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635073).length < 2 ^ (prefixWord ++ tailWord_635073).sum := by decide
  have hdescent : baseEnd_635073 < baseStart_635073 := by decide
  rcases family_descends (prefixWord ++ tailWord_635073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635098 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_635098 : Nat := 118140960795 + 635098 * 2 ^ 59
def prefixEnd_635098 : Nat := 4983230072969 + 3 ^ 40 * 635098 * 2
def baseEnd_635098 : Nat := 289876032630454586537105

theorem tailTrace_635098 : CollatzResearch.WordTrace tailWord_635098 prefixEnd_635098 289876032630454586537105 := by
  unfold tailWord_635098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790981763288971737020487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15442618035437257965387965 5790981763288971737020487)
  ·
    refine ⟨8686472644933457605530731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5790981763288971737020487 8686472644933457605530731)
    ·
      refine ⟨13029708967400186408296097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8686472644933457605530731 13029708967400186408296097)
      ·
        refine ⟨9772281725550139806222073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13029708967400186408296097 9772281725550139806222073)
        ·
          refine ⟨7329211294162604854666555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9772281725550139806222073 7329211294162604854666555)
          ·
            refine ⟨10993816941243907281999833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329211294162604854666555 10993816941243907281999833)
            ·
              refine ⟨8245362705932930461499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10993816941243907281999833 8245362705932930461499875)
              ·
                refine ⟨12368044058899395692249813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245362705932930461499875 12368044058899395692249813)
                ·
                  refine ⟨289876032630454586537105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12368044058899395692249813 289876032630454586537105)
                  ·
                    rfl

theorem cell20_635098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_635098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635098 prefixEnd_635098 := by exact prefixLift 635098
  have htrace : WordTrace (prefixWord ++ tailWord_635098) baseStart_635098 baseEnd_635098 := by
    simpa [prefixWord, tailWord_635098, baseEnd_635098] using wordTrace_append hprefix tailTrace_635098
  have hstable : (prefixWord ++ tailWord_635098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635098).length < 2 ^ (prefixWord ++ tailWord_635098).sum := by decide
  have hdescent : baseEnd_635098 < baseStart_635098 := by decide
  rcases family_descends (prefixWord ++ tailWord_635098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635115 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_635115 : Nat := 118140960795 + 635115 * 2 ^ 59
def prefixEnd_635115 : Nat := 4983230072969 + 3 ^ 40 * 635115 * 2
def baseEnd_635115 : Nat := 289883791893678082970369

theorem tailTrace_635115 : CollatzResearch.WordTrace tailWord_635115 prefixEnd_635115 289883791893678082970369 := by
  unfold tailWord_635115
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164547094094298851450799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15443031396062865900967199 23164547094094298851450799)
  ·
    refine ⟨34746820641141448277176199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23164547094094298851450799 34746820641141448277176199)
    ·
      refine ⟨52120230961712172415764299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34746820641141448277176199 52120230961712172415764299)
      ·
        refine ⟨78180346442568258623646449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52120230961712172415764299 78180346442568258623646449)
        ·
          refine ⟨58635259831926193967734837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78180346442568258623646449 58635259831926193967734837)
          ·
            refine ⟨5497055609243080684475141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58635259831926193967734837 5497055609243080684475141)
            ·
              refine ⟨1030697926733077628339089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5497055609243080684475141 1030697926733077628339089)
              ·
                refine ⟨773023445049808221254317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030697926733077628339089 773023445049808221254317)
                ·
                  refine ⟨289883791893678082970369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773023445049808221254317 289883791893678082970369)
                  ·
                    rfl

theorem cell20_635115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_635115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635115 prefixEnd_635115 := by exact prefixLift 635115
  have htrace : WordTrace (prefixWord ++ tailWord_635115) baseStart_635115 baseEnd_635115 := by
    simpa [prefixWord, tailWord_635115, baseEnd_635115] using wordTrace_append hprefix tailTrace_635115
  have hstable : (prefixWord ++ tailWord_635115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635115).length < 2 ^ (prefixWord ++ tailWord_635115).sum := by decide
  have hdescent : baseEnd_635115 < baseStart_635115 := by decide
  rcases family_descends (prefixWord ++ tailWord_635115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635166 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_635166 : Nat := 118140960795 + 635166 * 2 ^ 59
def prefixEnd_635166 : Nat := 4983230072969 + 3 ^ 40 * 635166 * 2
def baseEnd_635166 : Nat := 289907069683348572270161

theorem tailTrace_635166 : CollatzResearch.WordTrace tailWord_635166 prefixEnd_635166 289907069683348572270161 := by
  unfold tailWord_635166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895800902113691820194669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15444271477939689707704901 2895800902113691820194669)
  ·
    refine ⟨1085925338292634432573001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2895800902113691820194669 1085925338292634432573001)
    ·
      refine ⟨814444003719475824429751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085925338292634432573001 814444003719475824429751)
      ·
        refine ⟨1221666005579213736644627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814444003719475824429751 1221666005579213736644627)
        ·
          refine ⟨1832499008368820604966941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221666005579213736644627 1832499008368820604966941)
          ·
            refine ⟨687187128138307726862603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1832499008368820604966941 687187128138307726862603)
            ·
              refine ⟨1030780692207461590293905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687187128138307726862603 1030780692207461590293905)
              ·
                refine ⟨773085519155596192720429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030780692207461590293905 773085519155596192720429)
                ·
                  refine ⟨289907069683348572270161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773085519155596192720429 289907069683348572270161)
                  ·
                    rfl

theorem cell20_635166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_635166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635166 prefixEnd_635166 := by exact prefixLift 635166
  have htrace : WordTrace (prefixWord ++ tailWord_635166) baseStart_635166 baseEnd_635166 := by
    simpa [prefixWord, tailWord_635166, baseEnd_635166] using wordTrace_append hprefix tailTrace_635166
  have hstable : (prefixWord ++ tailWord_635166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635166).length < 2 ^ (prefixWord ++ tailWord_635166).sum := by decide
  have hdescent : baseEnd_635166 < baseStart_635166 := by decide
  rcases family_descends (prefixWord ++ tailWord_635166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635167 : List Nat := [1, 1, 2, 4, 3, 2, 7]
def baseStart_635167 : Nat := 118140960795 + 635167 * 2 ^ 59
def prefixEnd_635167 : Nat := 4983230072969 + 3 ^ 40 * 635167 * 2
def baseEnd_635167 : Nat := 32211947345621890359647

theorem tailTrace_635167 : CollatzResearch.WordTrace tailWord_635167 prefixEnd_635167 32211947345621890359647 := by
  unfold tailWord_635167
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166443689905911732343755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15444295793270607821562503 23166443689905911732343755)
  ·
    refine ⟨34749665534858867598515633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23166443689905911732343755 34749665534858867598515633)
    ·
      refine ⟨26062249151144150698886725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34749665534858867598515633 26062249151144150698886725)
      ·
        refine ⟨4886671715839528256041261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26062249151144150698886725 4886671715839528256041261)
        ·
          refine ⟨1832501893439823096015473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4886671715839528256041261 1832501893439823096015473)
          ·
            refine ⟨1374376420079867322011605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832501893439823096015473 1374376420079867322011605)
            ·
              refine ⟨32211947345621890359647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1374376420079867322011605 32211947345621890359647)
              ·
                rfl

theorem cell20_635167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_635167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635167 prefixEnd_635167 := by exact prefixLift 635167
  have htrace : WordTrace (prefixWord ++ tailWord_635167) baseStart_635167 baseEnd_635167 := by
    simpa [prefixWord, tailWord_635167, baseEnd_635167] using wordTrace_append hprefix tailTrace_635167
  have hstable : (prefixWord ++ tailWord_635167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635167).length < 2 ^ (prefixWord ++ tailWord_635167).sum := by decide
  have hdescent : baseEnd_635167 < baseStart_635167 := by decide
  rcases family_descends (prefixWord ++ tailWord_635167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635170 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_635170 : Nat := 118140960795 + 635170 * 2 ^ 59
def prefixEnd_635170 : Nat := 4983230072969 + 3 ^ 40 * 635170 * 2
def baseEnd_635170 : Nat := 289908895392342336136811

theorem tailTrace_635170 : CollatzResearch.WordTrace tailWord_635170 prefixEnd_635170 289908895392342336136811 := by
  unfold tailWord_635170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791638277223760811175741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15444368739263362163135309 5791638277223760811175741)
  ·
    refine ⟨2171864353958910304190903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5791638277223760811175741 2171864353958910304190903)
    ·
      refine ⟨3257796530938365456286355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171864353958910304190903 3257796530938365456286355)
      ·
        refine ⟨4886694796407548184429533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257796530938365456286355 4886694796407548184429533)
        ·
          refine ⟨1832510548652830569161075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4886694796407548184429533 1832510548652830569161075)
          ·
            refine ⟨2748765822979245853741613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832510548652830569161075 2748765822979245853741613)
            ·
              refine ⟨1030787183617217195153105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2748765822979245853741613 1030787183617217195153105)
              ·
                refine ⟨773090387712912896364829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030787183617217195153105 773090387712912896364829)
                ·
                  refine ⟨289908895392342336136811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773090387712912896364829 289908895392342336136811)
                  ·
                    rfl

theorem cell20_635170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_635170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635170 prefixEnd_635170 := by exact prefixLift 635170
  have htrace : WordTrace (prefixWord ++ tailWord_635170) baseStart_635170 baseEnd_635170 := by
    simpa [prefixWord, tailWord_635170, baseEnd_635170] using wordTrace_append hprefix tailTrace_635170
  have hstable : (prefixWord ++ tailWord_635170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635170).length < 2 ^ (prefixWord ++ tailWord_635170).sum := by decide
  have hdescent : baseEnd_635170 < baseStart_635170 := by decide
  rcases family_descends (prefixWord ++ tailWord_635170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635212 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_635212 : Nat := 118140960795 + 635212 * 2 ^ 59
def prefixEnd_635212 : Nat := 4983230072969 + 3 ^ 40 * 635212 * 2
def baseEnd_635212 : Nat := 289928065336776856736639

theorem tailTrace_635212 : CollatzResearch.WordTrace tailWord_635212 prefixEnd_635212 289928065336776856736639 := by
  unfold tailWord_635212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584042487371442208865945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15445389983161922945154593 11584042487371442208865945)
  ·
    refine ⟨8688031865528581656649459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11584042487371442208865945 8688031865528581656649459)
    ·
      refine ⟨13032047798292872484974189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688031865528581656649459 13032047798292872484974189)
      ·
        refine ⟨4887017924359827181865321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13032047798292872484974189 4887017924359827181865321)
        ·
          refine ⟨3665263443269870386398991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4887017924359827181865321 3665263443269870386398991)
          ·
            refine ⟨5497895164904805579598487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665263443269870386398991 5497895164904805579598487)
            ·
              refine ⟨8246842747357208369397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497895164904805579598487 8246842747357208369397731)
              ·
                refine ⟨12370264121035812554096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246842747357208369397731 12370264121035812554096597)
                ·
                  refine ⟨289928065336776856736639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12370264121035812554096597 289928065336776856736639)
                  ·
                    rfl

theorem cell20_635212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_635212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635212 prefixEnd_635212 := by exact prefixLift 635212
  have htrace : WordTrace (prefixWord ++ tailWord_635212) baseStart_635212 baseEnd_635212 := by
    simpa [prefixWord, tailWord_635212, baseEnd_635212] using wordTrace_append hprefix tailTrace_635212
  have hstable : (prefixWord ++ tailWord_635212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635212).length < 2 ^ (prefixWord ++ tailWord_635212).sum := by decide
  have hdescent : baseEnd_635212 < baseStart_635212 := by decide
  rcases family_descends (prefixWord ++ tailWord_635212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635228 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_635228 : Nat := 118140960795 + 635228 * 2 ^ 59
def prefixEnd_635228 : Nat := 4983230072969 + 3 ^ 40 * 635228 * 2
def baseEnd_635228 : Nat := 289935368172751912203241

theorem tailTrace_635228 : CollatzResearch.WordTrace tailWord_635228 prefixEnd_635228 289935368172751912203241 := by
  unfold tailWord_635228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584334271342459575157169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15445779028456612766876225 11584334271342459575157169)
  ·
    refine ⟨8688250703506844681367877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11584334271342459575157169 8688250703506844681367877)
    ·
      refine ⟨1629047006907533377756477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8688250703506844681367877 1629047006907533377756477)
      ·
        refine ⟨610892627590325016658679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1629047006907533377756477 610892627590325016658679)
        ·
          refine ⟨916338941385487524988019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610892627590325016658679 916338941385487524988019)
          ·
            refine ⟨1374508412078231287482029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916338941385487524988019 1374508412078231287482029)
            ·
              refine ⟨515440654529336732805761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1374508412078231287482029 515440654529336732805761)
              ·
                refine ⟨386580490897002549604321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515440654529336732805761 386580490897002549604321)
                ·
                  refine ⟨289935368172751912203241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386580490897002549604321 289935368172751912203241)
                  ·
                    rfl

theorem cell20_635228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_635228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635228 prefixEnd_635228 := by exact prefixLift 635228
  have htrace : WordTrace (prefixWord ++ tailWord_635228) baseStart_635228 baseEnd_635228 := by
    simpa [prefixWord, tailWord_635228, baseEnd_635228] using wordTrace_append hprefix tailTrace_635228
  have hstable : (prefixWord ++ tailWord_635228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635228).length < 2 ^ (prefixWord ++ tailWord_635228).sum := by decide
  have hdescent : baseEnd_635228 < baseStart_635228 := by decide
  rcases family_descends (prefixWord ++ tailWord_635228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635232 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_635232 : Nat := 118140960795 + 635232 * 2 ^ 59
def prefixEnd_635232 : Nat := 4983230072969 + 3 ^ 40 * 635232 * 2
def baseEnd_635232 : Nat := 289937193881745676069891

theorem tailTrace_635232 : CollatzResearch.WordTrace tailWord_635232 prefixEnd_635232 289937193881745676069891 := by
  unfold tailWord_635232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584407217335213916729975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15445876289780285222306633 11584407217335213916729975)
  ·
    refine ⟨17376610826002820875094963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11584407217335213916729975 17376610826002820875094963)
    ·
      refine ⟨26064916239004231312642445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17376610826002820875094963 26064916239004231312642445)
      ·
        refine ⟨9774343589626586742240917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26064916239004231312642445 9774343589626586742240917)
        ·
          refine ⟨458172355763746253542543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9774343589626586742240917 458172355763746253542543)
          ·
            refine ⟨687258533645619380313815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458172355763746253542543 687258533645619380313815)
            ·
              refine ⟨1030887800468429070470723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687258533645619380313815 1030887800468429070470723)
              ·
                refine ⟨1546331700702643605706085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030887800468429070470723 1546331700702643605706085)
                ·
                  refine ⟨289937193881745676069891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546331700702643605706085 289937193881745676069891)
                  ·
                    rfl

theorem cell20_635232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_635232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635232 prefixEnd_635232 := by exact prefixLift 635232
  have htrace : WordTrace (prefixWord ++ tailWord_635232) baseStart_635232 baseEnd_635232 := by
    simpa [prefixWord, tailWord_635232, baseEnd_635232] using wordTrace_append hprefix tailTrace_635232
  have hstable : (prefixWord ++ tailWord_635232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635232).length < 2 ^ (prefixWord ++ tailWord_635232).sum := by decide
  have hdescent : baseEnd_635232 < baseStart_635232 := by decide
  rcases family_descends (prefixWord ++ tailWord_635232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635257 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_635257 : Nat := 118140960795 + 635257 * 2 ^ 59
def prefixEnd_635257 : Nat := 4983230072969 + 3 ^ 40 * 635257 * 2
def baseEnd_635257 : Nat := 289948604562956700236455

theorem tailTrace_635257 : CollatzResearch.WordTrace tailWord_635257 prefixEnd_635257 289948604562956700236455 := by
  unfold tailWord_635257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23169726259579857103120025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15446484173053238068746683 23169726259579857103120025)
  ·
    refine ⟨17377294694684892827340019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23169726259579857103120025 17377294694684892827340019)
    ·
      refine ⟨26065942042027339241010029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377294694684892827340019 26065942042027339241010029)
      ·
        refine ⟨9774728265760252215378761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26065942042027339241010029 9774728265760252215378761)
        ·
          refine ⟨7331046199320189161534071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9774728265760252215378761 7331046199320189161534071)
          ·
            refine ⟨10996569298980283742301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331046199320189161534071 10996569298980283742301107)
            ·
              refine ⟨16494853948470425613451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996569298980283742301107 16494853948470425613451661)
              ·
                refine ⟨6185570230676409605044373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16494853948470425613451661 6185570230676409605044373)
                ·
                  refine ⟨289948604562956700236455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6185570230676409605044373 289948604562956700236455)
                  ·
                    rfl

theorem cell20_635257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_635257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635257 prefixEnd_635257 := by exact prefixLift 635257
  have htrace : WordTrace (prefixWord ++ tailWord_635257) baseStart_635257 baseEnd_635257 := by
    simpa [prefixWord, tailWord_635257, baseEnd_635257] using wordTrace_append hprefix tailTrace_635257
  have hstable : (prefixWord ++ tailWord_635257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635257).length < 2 ^ (prefixWord ++ tailWord_635257).sum := by decide
  have hdescent : baseEnd_635257 < baseStart_635257 := by decide
  rcases family_descends (prefixWord ++ tailWord_635257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635346 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_635346 : Nat := 118140960795 + 635346 * 2 ^ 59
def prefixEnd_635346 : Nat := 4983230072969 + 3 ^ 40 * 635346 * 2
def baseEnd_635346 : Nat := 289989226588067946269425

theorem tailTrace_635346 : CollatzResearch.WordTrace tailWord_635346 prefixEnd_635346 289989226588067946269425 := by
  unfold tailWord_635346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793243089064356325777473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15448648237504950202073261 5793243089064356325777473)
  ·
    refine ⟨4344932316798267244333105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5793243089064356325777473 4344932316798267244333105)
    ·
      refine ⟨3258699237598700433249829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4344932316798267244333105 3258699237598700433249829)
      ·
        refine ⟨611006107049756331234343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3258699237598700433249829 611006107049756331234343)
        ·
          refine ⟨916509160574634496851515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611006107049756331234343 916509160574634496851515)
          ·
            refine ⟨1374763740861951745277273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916509160574634496851515 1374763740861951745277273)
            ·
              refine ⟨1031072805646463808957955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374763740861951745277273 1031072805646463808957955)
              ·
                refine ⟨1546609208469695713436933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031072805646463808957955 1546609208469695713436933)
                ·
                  refine ⟨289989226588067946269425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546609208469695713436933 289989226588067946269425)
                  ·
                    rfl

theorem cell20_635346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_635346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635346 prefixEnd_635346 := by exact prefixLift 635346
  have htrace : WordTrace (prefixWord ++ tailWord_635346) baseStart_635346 baseEnd_635346 := by
    simpa [prefixWord, tailWord_635346, baseEnd_635346] using wordTrace_append hprefix tailTrace_635346
  have hstable : (prefixWord ++ tailWord_635346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635346).length < 2 ^ (prefixWord ++ tailWord_635346).sum := by decide
  have hdescent : baseEnd_635346 < baseStart_635346 := by decide
  rcases family_descends (prefixWord ++ tailWord_635346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635357 : List Nat := [1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_635357 : Nat := 118140960795 + 635357 * 2 ^ 59
def prefixEnd_635357 : Nat := 4983230072969 + 3 ^ 40 * 635357 * 2
def baseEnd_635357 : Nat := 96664749095933598967571

theorem tailTrace_635357 : CollatzResearch.WordTrace tailWord_635357 prefixEnd_635357 96664749095933598967571 := by
  unfold tailWord_635357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23173373559217574181760325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15448915706145049454506883 23173373559217574181760325)
  ·
    refine ⟨4345007542353295159080061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23173373559217574181760325 4345007542353295159080061)
    ·
      refine ⟨1629377828382485684655023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4345007542353295159080061 1629377828382485684655023)
      ·
        refine ⟨2444066742573728526982535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629377828382485684655023 2444066742573728526982535)
        ·
          refine ⟨3666100113860592790473803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444066742573728526982535 3666100113860592790473803)
          ·
            refine ⟨5499150170790889185710705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666100113860592790473803 5499150170790889185710705)
            ·
              refine ⟨4124362628093166889283029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499150170790889185710705 4124362628093166889283029)
              ·
                refine ⟨96664749095933598967571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124362628093166889283029 96664749095933598967571)
                ·
                  rfl

theorem cell20_635357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_635357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635357 prefixEnd_635357 := by exact prefixLift 635357
  have htrace : WordTrace (prefixWord ++ tailWord_635357) baseStart_635357 baseEnd_635357 := by
    simpa [prefixWord, tailWord_635357, baseEnd_635357] using wordTrace_append hprefix tailTrace_635357
  have hstable : (prefixWord ++ tailWord_635357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635357).length < 2 ^ (prefixWord ++ tailWord_635357).sum := by decide
  have hdescent : baseEnd_635357 < baseStart_635357 := by decide
  rcases family_descends (prefixWord ++ tailWord_635357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635371 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_635371 : Nat := 118140960795 + 635371 * 2 ^ 59
def prefixEnd_635371 : Nat := 4983230072969 + 3 ^ 40 * 635371 * 2
def baseEnd_635371 : Nat := 290000637269278970435989

theorem tailTrace_635371 : CollatzResearch.WordTrace tailWord_635371 prefixEnd_635371 290000637269278970435989 := by
  unfold tailWord_635371
  simp only [CollatzResearch.WordTrace]
  refine ⟨23173884181166854572769967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15449256120777903048513311 23173884181166854572769967)
  ·
    refine ⟨34760826271750281859154951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23173884181166854572769967 34760826271750281859154951)
    ·
      refine ⟨52141239407625422788732427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34760826271750281859154951 52141239407625422788732427)
      ·
        refine ⟨78211859111438134183098641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52141239407625422788732427 78211859111438134183098641)
        ·
          refine ⟨58658894333578600637323981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78211859111438134183098641 58658894333578600637323981)
          ·
            refine ⟨21997085375091975238996493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58658894333578600637323981 21997085375091975238996493)
            ·
              refine ⟨8248907015659490714623685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21997085375091975238996493 8248907015659490714623685)
              ·
                refine ⟨1546670065436154508991941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8248907015659490714623685 1546670065436154508991941)
                ·
                  refine ⟨290000637269278970435989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546670065436154508991941 290000637269278970435989)
                  ·
                    rfl

theorem cell20_635371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_635371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635371 prefixEnd_635371 := by exact prefixLift 635371
  have htrace : WordTrace (prefixWord ++ tailWord_635371) baseStart_635371 baseEnd_635371 := by
    simpa [prefixWord, tailWord_635371, baseEnd_635371] using wordTrace_append hprefix tailTrace_635371
  have hstable : (prefixWord ++ tailWord_635371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635371).length < 2 ^ (prefixWord ++ tailWord_635371).sum := by decide
  have hdescent : baseEnd_635371 < baseStart_635371 := by decide
  rcases family_descends (prefixWord ++ tailWord_635371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635374 : List Nat := [4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_635374 : Nat := 118140960795 + 635374 * 2 ^ 59
def prefixEnd_635374 : Nat := 4983230072969 + 3 ^ 40 * 635374 * 2
def baseEnd_635374 : Nat := 96667335517008097778659

theorem tailTrace_635374 : CollatzResearch.WordTrace tailWord_635374 prefixEnd_635374 96667335517008097778659 := by
  unfold tailWord_635374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896749200019498260641147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15449329066770657390086117 2896749200019498260641147)
  ·
    refine ⟨4345123800029247390961721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896749200019498260641147 4345123800029247390961721)
    ·
      refine ⟨3258842850021935543221291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345123800029247390961721 3258842850021935543221291)
      ·
        refine ⟨4888264275032903314831937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258842850021935543221291 4888264275032903314831937)
        ·
          refine ⟨3666198206274677486123953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4888264275032903314831937 3666198206274677486123953)
          ·
            refine ⟨2749648654706008114592965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666198206274677486123953 2749648654706008114592965)
            ·
              refine ⟨515559122757376521486181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2749648654706008114592965 515559122757376521486181)
              ·
                refine ⟨96667335517008097778659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515559122757376521486181 96667335517008097778659)
                ·
                  rfl

theorem cell20_635374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_635374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635374 prefixEnd_635374 := by exact prefixLift 635374
  have htrace : WordTrace (prefixWord ++ tailWord_635374) baseStart_635374 baseEnd_635374 := by
    simpa [prefixWord, tailWord_635374, baseEnd_635374] using wordTrace_append hprefix tailTrace_635374
  have hstable : (prefixWord ++ tailWord_635374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635374).length < 2 ^ (prefixWord ++ tailWord_635374).sum := by decide
  have hdescent : baseEnd_635374 < baseStart_635374 := by decide
  rcases family_descends (prefixWord ++ tailWord_635374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635402 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_635402 : Nat := 118140960795 + 635402 * 2 ^ 59
def prefixEnd_635402 : Nat := 4983230072969 + 3 ^ 40 * 635402 * 2
def baseEnd_635402 : Nat := 290014786513980640402529

theorem tailTrace_635402 : CollatzResearch.WordTrace tailWord_635402 prefixEnd_635402 290014786513980640402529 := by
  unfold tailWord_635402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793753711013636716787115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15450009896036364578098973 5793753711013636716787115)
  ·
    refine ⟨8690630566520455075180673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5793753711013636716787115 8690630566520455075180673)
    ·
      refine ⟨6517972924890341306385505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8690630566520455075180673 6517972924890341306385505)
      ·
        refine ⟨4888479693667755979789129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6517972924890341306385505 4888479693667755979789129)
        ·
          refine ⟨3666359770250816984841847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4888479693667755979789129 3666359770250816984841847)
          ·
            refine ⟨5499539655376225477262771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666359770250816984841847 5499539655376225477262771)
            ·
              refine ⟨8249309483064338215894157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499539655376225477262771 8249309483064338215894157)
              ·
                refine ⟨3093491056149126830960309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8249309483064338215894157 3093491056149126830960309)
                ·
                  refine ⟨290014786513980640402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093491056149126830960309 290014786513980640402529)
                  ·
                    rfl

theorem cell20_635402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_635402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635402 prefixEnd_635402 := by exact prefixLift 635402
  have htrace : WordTrace (prefixWord ++ tailWord_635402) baseStart_635402 baseEnd_635402 := by
    simpa [prefixWord, tailWord_635402, baseEnd_635402] using wordTrace_append hprefix tailTrace_635402
  have hstable : (prefixWord ++ tailWord_635402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635402).length < 2 ^ (prefixWord ++ tailWord_635402).sum := by decide
  have hdescent : baseEnd_635402 < baseStart_635402 := by decide
  rcases family_descends (prefixWord ++ tailWord_635402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635409 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_635409 : Nat := 118140960795 + 635409 * 2 ^ 59
def prefixEnd_635409 : Nat := 4983230072969 + 3 ^ 40 * 635409 * 2
def baseEnd_635409 : Nat := 290017981504719727169167

theorem tailTrace_635409 : CollatzResearch.WordTrace tailWord_635409 prefixEnd_635409 290017981504719727169167 := by
  unfold tailWord_635409
  simp only [CollatzResearch.WordTrace]
  refine ⟨23175270155029187062653281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15450180103352791375102187 23175270155029187062653281)
  ·
    refine ⟨17381452616271890296989961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23175270155029187062653281 17381452616271890296989961)
    ·
      refine ⟨13036089462203917722742471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17381452616271890296989961 13036089462203917722742471)
      ·
        refine ⟨19554134193305876584113707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036089462203917722742471 19554134193305876584113707)
        ·
          refine ⟨29331201289958814876170561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19554134193305876584113707 29331201289958814876170561)
          ·
            refine ⟨21998400967469111157127921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29331201289958814876170561 21998400967469111157127921)
            ·
              refine ⟨16498800725601833367845941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21998400967469111157127921 16498800725601833367845941)
              ·
                refine ⟨1546762568025171878235557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16498800725601833367845941 1546762568025171878235557)
                ·
                  refine ⟨290017981504719727169167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546762568025171878235557 290017981504719727169167)
                  ·
                    rfl

theorem cell20_635409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_635409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635409 prefixEnd_635409 := by exact prefixLift 635409
  have htrace : WordTrace (prefixWord ++ tailWord_635409) baseStart_635409 baseEnd_635409 := by
    simpa [prefixWord, tailWord_635409, baseEnd_635409] using wordTrace_append hprefix tailTrace_635409
  have hstable : (prefixWord ++ tailWord_635409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635409).length < 2 ^ (prefixWord ++ tailWord_635409).sum := by decide
  have hdescent : baseEnd_635409 < baseStart_635409 := by decide
  rcases family_descends (prefixWord ++ tailWord_635409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635412 : List Nat := [2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_635412 : Nat := 118140960795 + 635412 * 2 ^ 59
def prefixEnd_635412 : Nat := 4983230072969 + 3 ^ 40 * 635412 * 2
def baseEnd_635412 : Nat := 96673116928821683356385

theorem tailTrace_635412 : CollatzResearch.WordTrace tailWord_635412 prefixEnd_635412 96673116928821683356385 := by
  unfold tailWord_635412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11587689787009159287506245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15450253049345545716674993 11587689787009159287506245)
  ·
    refine ⟨2172691835064217366407421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11587689787009159287506245 2172691835064217366407421)
    ·
      refine ⟨814759438149081512402783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2172691835064217366407421 814759438149081512402783)
      ·
        refine ⟨1222139157223622268604175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814759438149081512402783 1222139157223622268604175)
        ·
          refine ⟨1833208735835433402906263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222139157223622268604175 1833208735835433402906263)
          ·
            refine ⟨2749813103753150104359395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833208735835433402906263 2749813103753150104359395)
            ·
              refine ⟨4124719655629725156539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749813103753150104359395 4124719655629725156539093)
              ·
                refine ⟨96673116928821683356385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124719655629725156539093 96673116928821683356385)
                ·
                  rfl

theorem cell20_635412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_635412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635412 prefixEnd_635412 := by exact prefixLift 635412
  have htrace : WordTrace (prefixWord ++ tailWord_635412) baseStart_635412 baseEnd_635412 := by
    simpa [prefixWord, tailWord_635412, baseEnd_635412] using wordTrace_append hprefix tailTrace_635412
  have hstable : (prefixWord ++ tailWord_635412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635412).length < 2 ^ (prefixWord ++ tailWord_635412).sum := by decide
  have hdescent : baseEnd_635412 < baseStart_635412 := by decide
  rcases family_descends (prefixWord ++ tailWord_635412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635457 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_635457 : Nat := 118140960795 + 635457 * 2 ^ 59
def prefixEnd_635457 : Nat := 4983230072969 + 3 ^ 40 * 635457 * 2
def baseEnd_635457 : Nat := 290039890012644893568971

theorem tailTrace_635457 : CollatzResearch.WordTrace tailWord_635457 prefixEnd_635457 290039890012644893568971 := by
  unfold tailWord_635457
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177020858855291260400625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15451347239236860840267083 23177020858855291260400625)
  ·
    refine ⟨17382765644141468445300469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23177020858855291260400625 17382765644141468445300469)
    ·
      refine ⟨1629634279138262666746919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17382765644141468445300469 1629634279138262666746919)
      ·
        refine ⟨2444451418707394000120379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629634279138262666746919 2444451418707394000120379)
        ·
          refine ⟨3666677128061091000180569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444451418707394000120379 3666677128061091000180569)
          ·
            refine ⟨2750007846045818250135427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666677128061091000180569 2750007846045818250135427)
            ·
              refine ⟨4125011769068727375203141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750007846045818250135427 4125011769068727375203141)
              ·
                refine ⟨773439706700386382850589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4125011769068727375203141 773439706700386382850589)
                ·
                  refine ⟨290039890012644893568971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773439706700386382850589 290039890012644893568971)
                  ·
                    rfl

theorem cell20_635457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_635457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635457 prefixEnd_635457 := by exact prefixLift 635457
  have htrace : WordTrace (prefixWord ++ tailWord_635457) baseStart_635457 baseEnd_635457 := by
    simpa [prefixWord, tailWord_635457, baseEnd_635457] using wordTrace_append hprefix tailTrace_635457
  have hstable : (prefixWord ++ tailWord_635457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635457).length < 2 ^ (prefixWord ++ tailWord_635457).sum := by decide
  have hdescent : baseEnd_635457 < baseStart_635457 := by decide
  rcases family_descends (prefixWord ++ tailWord_635457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635523 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_635523 : Nat := 118140960795 + 635523 * 2 ^ 59
def prefixEnd_635523 : Nat := 4983230072969 + 3 ^ 40 * 635523 * 2
def baseEnd_635523 : Nat := 290070014211041997368701

theorem tailTrace_635523 : CollatzResearch.WordTrace tailWord_635523 prefixEnd_635523 290070014211041997368701 := by
  unfold tailWord_635523
  simp only [CollatzResearch.WordTrace]
  refine ⟨23179428076616184532303223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15452952051077456354868815 23179428076616184532303223)
  ·
    refine ⟨34769142114924276798454835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23179428076616184532303223 34769142114924276798454835)
    ·
      refine ⟨52153713172386415197682253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34769142114924276798454835 52153713172386415197682253)
      ·
        refine ⟨19557642439644905699130845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52153713172386415197682253 19557642439644905699130845)
        ·
          refine ⟨7334115914866839637174067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19557642439644905699130845 7334115914866839637174067)
          ·
            refine ⟨11001173872300259455761101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334115914866839637174067 11001173872300259455761101)
            ·
              refine ⟨4125440202112597295910413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11001173872300259455761101 4125440202112597295910413)
              ·
                refine ⟨1547040075792223985966405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125440202112597295910413 1547040075792223985966405)
                ·
                  refine ⟨290070014211041997368701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547040075792223985966405 290070014211041997368701)
                  ·
                    rfl

theorem cell20_635523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_635523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635523 prefixEnd_635523 := by exact prefixLift 635523
  have htrace : WordTrace (prefixWord ++ tailWord_635523) baseStart_635523 baseEnd_635523 := by
    simpa [prefixWord, tailWord_635523, baseEnd_635523] using wordTrace_append hprefix tailTrace_635523
  have hstable : (prefixWord ++ tailWord_635523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635523).length < 2 ^ (prefixWord ++ tailWord_635523).sum := by decide
  have hdescent : baseEnd_635523 < baseStart_635523 := by decide
  rcases family_descends (prefixWord ++ tailWord_635523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635553 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 2]
def baseStart_635553 : Nat := 118140960795 + 635553 * 2 ^ 59
def prefixEnd_635553 : Nat := 4983230072969 + 3 ^ 40 * 635553 * 2
def baseEnd_635553 : Nat := 290083707028495226368579

theorem tailTrace_635553 : CollatzResearch.WordTrace tailWord_635553 prefixEnd_635553 290083707028495226368579 := by
  unfold tailWord_635553
  simp only [CollatzResearch.WordTrace]
  refine ⟨23180522266507499655895313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15453681511004999770596875 23180522266507499655895313)
  ·
    refine ⟨17385391699880624741921485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23180522266507499655895313 17385391699880624741921485)
    ·
      refine ⟨6519521887455234278220557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17385391699880624741921485 6519521887455234278220557)
      ·
        refine ⟨2444820707795712854332709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6519521887455234278220557 2444820707795712854332709)
        ·
          refine ⟨458403882711696160187383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2444820707795712854332709 458403882711696160187383)
          ·
            refine ⟨687605824067544240281075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458403882711696160187383 687605824067544240281075)
            ·
              refine ⟨1031408736101316360421613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687605824067544240281075 1031408736101316360421613)
              ·
                refine ⟨386778276037993635158105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1031408736101316360421613 386778276037993635158105)
                ·
                  refine ⟨290083707028495226368579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386778276037993635158105 290083707028495226368579)
                  ·
                    rfl

theorem cell20_635553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_635553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635553 prefixEnd_635553 := by exact prefixLift 635553
  have htrace : WordTrace (prefixWord ++ tailWord_635553) baseStart_635553 baseEnd_635553 := by
    simpa [prefixWord, tailWord_635553, baseEnd_635553] using wordTrace_append hprefix tailTrace_635553
  have hstable : (prefixWord ++ tailWord_635553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635553).length < 2 ^ (prefixWord ++ tailWord_635553).sum := by decide
  have hdescent : baseEnd_635553 < baseStart_635553 := by decide
  rcases family_descends (prefixWord ++ tailWord_635553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635588 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_635588 : Nat := 118140960795 + 635588 * 2 ^ 59
def prefixEnd_635588 : Nat := 4983230072969 + 3 ^ 40 * 635588 * 2
def baseEnd_635588 : Nat := 290099681982190660201769

theorem tailTrace_635588 : CollatzResearch.WordTrace tailWord_635588 prefixEnd_635588 290099681982190660201769 := by
  unfold tailWord_635588
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590899410690350316709709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15454532547587133755612945 11590899410690350316709709)
  ·
    refine ⟨4346587279008881368766141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11590899410690350316709709 4346587279008881368766141)
    ·
      refine ⟨1629970229628330513287303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4346587279008881368766141 1629970229628330513287303)
      ·
        refine ⟨2444955344442495769930955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629970229628330513287303 2444955344442495769930955)
        ·
          refine ⟨3667433016663743654896433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444955344442495769930955 3667433016663743654896433)
          ·
            refine ⟨2750574762497807741172325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667433016663743654896433 2750574762497807741172325)
            ·
              refine ⟨515732767968338951469811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2750574762497807741172325 515732767968338951469811)
              ·
                refine ⟨773599151952508427204717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515732767968338951469811 773599151952508427204717)
                ·
                  refine ⟨290099681982190660201769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773599151952508427204717 290099681982190660201769)
                  ·
                    rfl

theorem cell20_635588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_635588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635588 prefixEnd_635588 := by exact prefixLift 635588
  have htrace : WordTrace (prefixWord ++ tailWord_635588) baseStart_635588 baseEnd_635588 := by
    simpa [prefixWord, tailWord_635588, baseEnd_635588] using wordTrace_append hprefix tailTrace_635588
  have hstable : (prefixWord ++ tailWord_635588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635588).length < 2 ^ (prefixWord ++ tailWord_635588).sum := by decide
  have hdescent : baseEnd_635588 < baseStart_635588 := by decide
  rcases family_descends (prefixWord ++ tailWord_635588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635616 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_635616 : Nat := 118140960795 + 635616 * 2 ^ 59
def prefixEnd_635616 : Nat := 4983230072969 + 3 ^ 40 * 635616 * 2
def baseEnd_635616 : Nat := 290112461945147007268321

theorem tailTrace_635616 : CollatzResearch.WordTrace tailWord_635616 prefixEnd_635616 290112461945147007268321 := by
  unfold tailWord_635616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591410032639630707719351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15455213376852840943625801 11591410032639630707719351)
  ·
    refine ⟨17387115048959446061579027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11591410032639630707719351 17387115048959446061579027)
    ·
      refine ⟨26080672573439169092368541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17387115048959446061579027 26080672573439169092368541)
      ·
        refine ⟨9780252215039688409638203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26080672573439169092368541 9780252215039688409638203)
        ·
          refine ⟨14670378322559532614457305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9780252215039688409638203 14670378322559532614457305)
          ·
            refine ⟨11002783741919649460842979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14670378322559532614457305 11002783741919649460842979)
            ·
              refine ⟨16504175612879474191264469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002783741919649460842979 16504175612879474191264469)
              ·
                refine ⟨386816615926862676357761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16504175612879474191264469 386816615926862676357761)
                ·
                  refine ⟨290112461945147007268321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386816615926862676357761 290112461945147007268321)
                  ·
                    rfl

theorem cell20_635616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_635616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635616 prefixEnd_635616 := by exact prefixLift 635616
  have htrace : WordTrace (prefixWord ++ tailWord_635616) baseStart_635616 baseEnd_635616 := by
    simpa [prefixWord, tailWord_635616, baseEnd_635616] using wordTrace_append hprefix tailTrace_635616
  have hstable : (prefixWord ++ tailWord_635616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635616).length < 2 ^ (prefixWord ++ tailWord_635616).sum := by decide
  have hdescent : baseEnd_635616 < baseStart_635616 := by decide
  rcases family_descends (prefixWord ++ tailWord_635616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635636 : List Nat := [2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_635636 : Nat := 118140960795 + 635636 * 2 ^ 59
def prefixEnd_635636 : Nat := 4983230072969 + 3 ^ 40 * 635636 * 2
def baseEnd_635636 : Nat := 96707196830038608867191

theorem tailTrace_635636 : CollatzResearch.WordTrace tailWord_635636 prefixEnd_635636 96707196830038608867191 := by
  unfold tailWord_635636
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591774762603402415583381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15455699683471203220777841 11591774762603402415583381)
  ·
    refine ⟨543364441997034488230471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11591774762603402415583381 543364441997034488230471)
    ·
      refine ⟨815046662995551732345707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543364441997034488230471 815046662995551732345707)
      ·
        refine ⟨1222569994493327598518561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815046662995551732345707 1222569994493327598518561)
        ·
          refine ⟨916927495869995698888921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222569994493327598518561 916927495869995698888921)
          ·
            refine ⟨687695621902496774166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916927495869995698888921 687695621902496774166691)
            ·
              refine ⟨1031543432853745161250037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687695621902496774166691 1031543432853745161250037)
              ·
                refine ⟨96707196830038608867191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031543432853745161250037 96707196830038608867191)
                ·
                  rfl

theorem cell20_635636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_635636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635636 prefixEnd_635636 := by exact prefixLift 635636
  have htrace : WordTrace (prefixWord ++ tailWord_635636) baseStart_635636 baseEnd_635636 := by
    simpa [prefixWord, tailWord_635636, baseEnd_635636] using wordTrace_append hprefix tailTrace_635636
  have hstable : (prefixWord ++ tailWord_635636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635636).length < 2 ^ (prefixWord ++ tailWord_635636).sum := by decide
  have hdescent : baseEnd_635636 < baseStart_635636 := by decide
  rcases family_descends (prefixWord ++ tailWord_635636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635651 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_635651 : Nat := 118140960795 + 635651 * 2 ^ 59
def prefixEnd_635651 : Nat := 4983230072969 + 3 ^ 40 * 635651 * 2
def baseEnd_635651 : Nat := 290128436898842441101511

theorem tailTrace_635651 : CollatzResearch.WordTrace tailWord_635651 prefixEnd_635651 290128436898842441101511 := by
  unfold tailWord_635651
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184096620152462392962807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15456064413434974928641871 23184096620152462392962807)
  ·
    refine ⟨34776144930228693589444211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23184096620152462392962807 34776144930228693589444211)
    ·
      refine ⟨52164217395343040384166317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34776144930228693589444211 52164217395343040384166317)
      ·
        refine ⟨19561581523253640144062369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52164217395343040384166317 19561581523253640144062369)
        ·
          refine ⟨14671186142440230108046777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19561581523253640144062369 14671186142440230108046777)
          ·
            refine ⟨11003389606830172581035083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14671186142440230108046777 11003389606830172581035083)
            ·
              refine ⟨16505084410245258871552625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11003389606830172581035083 16505084410245258871552625)
              ·
                refine ⟨12378813307683944153664469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16505084410245258871552625 12378813307683944153664469)
                ·
                  refine ⟨290128436898842441101511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12378813307683944153664469 290128436898842441101511)
                  ·
                    rfl

theorem cell20_635651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_635651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635651 prefixEnd_635651 := by exact prefixLift 635651
  have htrace : WordTrace (prefixWord ++ tailWord_635651) baseStart_635651 baseEnd_635651 := by
    simpa [prefixWord, tailWord_635651, baseEnd_635651] using wordTrace_append hprefix tailTrace_635651
  have hstable : (prefixWord ++ tailWord_635651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635651).length < 2 ^ (prefixWord ++ tailWord_635651).sum := by decide
  have hdescent : baseEnd_635651 < baseStart_635651 := by decide
  rcases family_descends (prefixWord ++ tailWord_635651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635689 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_635689 : Nat := 118140960795 + 635689 * 2 ^ 59
def prefixEnd_635689 : Nat := 4983230072969 + 3 ^ 40 * 635689 * 2
def baseEnd_635689 : Nat := 290145781134283197834689

theorem tailTrace_635689 : CollatzResearch.WordTrace tailWord_635689 prefixEnd_635689 290145781134283197834689 := by
  unfold tailWord_635689
  simp only [CollatzResearch.WordTrace]
  refine ⟨23185482594014794882846121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15456988396009863255230747 23185482594014794882846121)
  ·
    refine ⟨17389111945511096162134591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23185482594014794882846121 17389111945511096162134591)
    ·
      refine ⟨26083667918266644243201887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17389111945511096162134591 26083667918266644243201887)
      ·
        refine ⟨39125501877399966364802831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26083667918266644243201887 39125501877399966364802831)
        ·
          refine ⟨58688252816099949547204247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39125501877399966364802831 58688252816099949547204247)
          ·
            refine ⟨88032379224149924320806371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58688252816099949547204247 88032379224149924320806371)
            ·
              refine ⟨132048568836224886481209557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88032379224149924320806371 132048568836224886481209557)
              ·
                refine ⟨3094888332099020776903349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132048568836224886481209557 3094888332099020776903349)
                ·
                  refine ⟨290145781134283197834689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3094888332099020776903349 290145781134283197834689)
                  ·
                    rfl

theorem cell20_635689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_635689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635689 prefixEnd_635689 := by exact prefixLift 635689
  have htrace : WordTrace (prefixWord ++ tailWord_635689) baseStart_635689 baseEnd_635689 := by
    simpa [prefixWord, tailWord_635689, baseEnd_635689] using wordTrace_append hprefix tailTrace_635689
  have hstable : (prefixWord ++ tailWord_635689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635689).length < 2 ^ (prefixWord ++ tailWord_635689).sum := by decide
  have hdescent : baseEnd_635689 < baseStart_635689 := by decide
  rcases family_descends (prefixWord ++ tailWord_635689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635692 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_635692 : Nat := 118140960795 + 635692 * 2 ^ 59
def prefixEnd_635692 : Nat := 4983230072969 + 3 ^ 40 * 635692 * 2
def baseEnd_635692 : Nat := 290147150416028520734677

theorem tailTrace_635692 : CollatzResearch.WordTrace tailWord_635692 prefixEnd_635692 290147150416028520734677 := by
  unfold tailWord_635692
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592796006501963197602665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15457061342002617596803553 11592796006501963197602665)
  ·
    refine ⟨8694597004876472398201999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11592796006501963197602665 8694597004876472398201999)
    ·
      refine ⟨13041895507314708597302999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8694597004876472398201999 13041895507314708597302999)
      ·
        refine ⟨19562843260972062895954499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13041895507314708597302999 19562843260972062895954499)
        ·
          refine ⟨29344264891458094343931749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19562843260972062895954499 29344264891458094343931749)
          ·
            refine ⟨5502049667148392689487203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29344264891458094343931749 5502049667148392689487203)
            ·
              refine ⟨8253074500722589034230805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502049667148392689487203 8253074500722589034230805)
              ·
                refine ⟨386862867221371360979569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8253074500722589034230805 386862867221371360979569)
                ·
                  refine ⟨290147150416028520734677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386862867221371360979569 290147150416028520734677)
                  ·
                    rfl

theorem cell20_635692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_635692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635692 prefixEnd_635692 := by exact prefixLift 635692
  have htrace : WordTrace (prefixWord ++ tailWord_635692) baseStart_635692 baseEnd_635692 := by
    simpa [prefixWord, tailWord_635692, baseEnd_635692] using wordTrace_append hprefix tailTrace_635692
  have hstable : (prefixWord ++ tailWord_635692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635692).length < 2 ^ (prefixWord ++ tailWord_635692).sum := by decide
  have hdescent : baseEnd_635692 < baseStart_635692 := by decide
  rcases family_descends (prefixWord ++ tailWord_635692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635720 : List Nat := [2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_635720 : Nat := 118140960795 + 635720 * 2 ^ 59
def prefixEnd_635720 : Nat := 4983230072969 + 3 ^ 40 * 635720 * 2
def baseEnd_635720 : Nat := 96719976792994955933743

theorem tailTrace_635720 : CollatzResearch.WordTrace tailWord_635720 prefixEnd_635720 96719976792994955933743 := by
  unfold tailWord_635720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593306628451243588612307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15457742171268324784816409 11593306628451243588612307)
  ·
    refine ⟨17389959942676865382918461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593306628451243588612307 17389959942676865382918461)
    ·
      refine ⟨6521234978503824518594423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17389959942676865382918461 6521234978503824518594423)
      ·
        refine ⟨9781852467755736777891635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6521234978503824518594423 9781852467755736777891635)
        ·
          refine ⟨14672778701633605166837453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781852467755736777891635 14672778701633605166837453)
          ·
            refine ⟨5502292013112601937564045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14672778701633605166837453 5502292013112601937564045)
            ·
              refine ⟨2063359504917225726586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5502292013112601937564045 2063359504917225726586517)
              ·
                refine ⟨96719976792994955933743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2063359504917225726586517 96719976792994955933743)
                ·
                  rfl

theorem cell20_635720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_635720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635720 prefixEnd_635720 := by exact prefixLift 635720
  have htrace : WordTrace (prefixWord ++ tailWord_635720) baseStart_635720 baseEnd_635720 := by
    simpa [prefixWord, tailWord_635720, baseEnd_635720] using wordTrace_append hprefix tailTrace_635720
  have hstable : (prefixWord ++ tailWord_635720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635720).length < 2 ^ (prefixWord ++ tailWord_635720).sum := by decide
  have hdescent : baseEnd_635720 < baseStart_635720 := by decide
  rcases family_descends (prefixWord ++ tailWord_635720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635744 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_635744 : Nat := 118140960795 + 635744 * 2 ^ 59
def prefixEnd_635744 : Nat := 4983230072969 + 3 ^ 40 * 635744 * 2
def baseEnd_635744 : Nat := 290170884632947451001131

theorem tailTrace_635744 : CollatzResearch.WordTrace tailWord_635744 prefixEnd_635744 290170884632947451001131 := by
  unfold tailWord_635744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593744304407769638049143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15458325739210359517398857 11593744304407769638049143)
  ·
    refine ⟨17390616456611654457073715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593744304407769638049143 17390616456611654457073715)
    ·
      refine ⟨26085924684917481685610573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17390616456611654457073715 26085924684917481685610573)
      ·
        refine ⟨9782221756844055632103965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26085924684917481685610573 9782221756844055632103965)
        ·
          refine ⟨3668333158816520862038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9782221756844055632103965 3668333158816520862038987)
          ·
            refine ⟨5502499738224781293058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668333158816520862038987 5502499738224781293058481)
            ·
              refine ⟨4126874803668585969793861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502499738224781293058481 4126874803668585969793861)
              ·
                refine ⟨773789025687859869336349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4126874803668585969793861 773789025687859869336349)
                ·
                  refine ⟨290170884632947451001131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773789025687859869336349 290170884632947451001131)
                  ·
                    rfl

theorem cell20_635744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_635744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635744 prefixEnd_635744 := by exact prefixLift 635744
  have htrace : WordTrace (prefixWord ++ tailWord_635744) baseStart_635744 baseEnd_635744 := by
    simpa [prefixWord, tailWord_635744, baseEnd_635744] using wordTrace_append hprefix tailTrace_635744
  have hstable : (prefixWord ++ tailWord_635744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635744).length < 2 ^ (prefixWord ++ tailWord_635744).sum := by decide
  have hdescent : baseEnd_635744 < baseStart_635744 := by decide
  rcases family_descends (prefixWord ++ tailWord_635744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635761 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_635761 : Nat := 118140960795 + 635761 * 2 ^ 59
def prefixEnd_635761 : Nat := 4983230072969 + 3 ^ 40 * 635761 * 2
def baseEnd_635761 : Nat := 290178643896170947434395

theorem tailTrace_635761 : CollatzResearch.WordTrace tailWord_635761 prefixEnd_635761 290178643896170947434395 := by
  unfold tailWord_635761
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188108649753951179467137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15458739099835967452978091 23188108649753951179467137)
  ·
    refine ⟨17391081487315463384600353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23188108649753951179467137 17391081487315463384600353)
    ·
      refine ⟨13043311115486597538450265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17391081487315463384600353 13043311115486597538450265)
      ·
        refine ⟨9782483336614948153837699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13043311115486597538450265 9782483336614948153837699)
        ·
          refine ⟨14673725004922422230756549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9782483336614948153837699 14673725004922422230756549)
          ·
            refine ⟨2751323438422954168266853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14673725004922422230756549 2751323438422954168266853)
            ·
              refine ⟨515873144704303906550035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2751323438422954168266853 515873144704303906550035)
              ·
                refine ⟨773809717056455859825053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515873144704303906550035 773809717056455859825053)
                ·
                  refine ⟨290178643896170947434395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773809717056455859825053 290178643896170947434395)
                  ·
                    rfl

theorem cell20_635761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_635761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635761 prefixEnd_635761 := by exact prefixLift 635761
  have htrace : WordTrace (prefixWord ++ tailWord_635761) baseStart_635761 baseEnd_635761 := by
    simpa [prefixWord, tailWord_635761, baseEnd_635761] using wordTrace_append hprefix tailTrace_635761
  have hstable : (prefixWord ++ tailWord_635761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635761).length < 2 ^ (prefixWord ++ tailWord_635761).sum := by decide
  have hdescent : baseEnd_635761 < baseStart_635761 := by decide
  rcases family_descends (prefixWord ++ tailWord_635761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635798 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_635798 : Nat := 118140960795 + 635798 * 2 ^ 59
def prefixEnd_635798 : Nat := 4983230072969 + 3 ^ 40 * 635798 * 2
def baseEnd_635798 : Nat := 290195531704363263200911

theorem tailTrace_635798 : CollatzResearch.WordTrace tailWord_635798 prefixEnd_635798 290195531704363263200911 := by
  unfold tailWord_635798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449341134413744156160253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15459638767079937665709365 1449341134413744156160253)
  ·
    refine ⟨543502925405154058560095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1449341134413744156160253 543502925405154058560095)
    ·
      refine ⟨815254388107731087840143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543502925405154058560095 815254388107731087840143)
      ·
        refine ⟨1222881582161596631760215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815254388107731087840143 1222881582161596631760215)
        ·
          refine ⟨1834322373242394947640323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222881582161596631760215 1834322373242394947640323)
          ·
            refine ⟨2751483559863592421460485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834322373242394947640323 2751483559863592421460485)
            ·
              refine ⟨515903167474423579023841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2751483559863592421460485 515903167474423579023841)
              ·
                refine ⟨386927375605817684267881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515903167474423579023841 386927375605817684267881)
                ·
                  refine ⟨290195531704363263200911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386927375605817684267881 290195531704363263200911)
                  ·
                    rfl

theorem cell20_635798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_635798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635798 prefixEnd_635798 := by exact prefixLift 635798
  have htrace : WordTrace (prefixWord ++ tailWord_635798) baseStart_635798 baseEnd_635798 := by
    simpa [prefixWord, tailWord_635798, baseEnd_635798] using wordTrace_append hprefix tailTrace_635798
  have hstable : (prefixWord ++ tailWord_635798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635798).length < 2 ^ (prefixWord ++ tailWord_635798).sum := by decide
  have hdescent : baseEnd_635798 < baseStart_635798 := by decide
  rcases family_descends (prefixWord ++ tailWord_635798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635846 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_635846 : Nat := 118140960795 + 635846 * 2 ^ 59
def prefixEnd_635846 : Nat := 4983230072969 + 3 ^ 40 * 635846 * 2
def baseEnd_635846 : Nat := 290217440212288429600715

theorem tailTrace_635846 : CollatzResearch.WordTrace tailWord_635846 prefixEnd_635846 290217440212288429600715 := by
  unfold tailWord_635846
  simp only [CollatzResearch.WordTrace]
  refine ⟨724725276701437834259731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15460805902964007130874261 724725276701437834259731)
  ·
    refine ⟨1087087915052156751389597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724725276701437834259731 1087087915052156751389597)
    ·
      refine ⟨407657968144558781771099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1087087915052156751389597 407657968144558781771099)
      ·
        refine ⟨611486952216838172656649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407657968144558781771099 611486952216838172656649)
        ·
          refine ⟨458615214162628629492487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611486952216838172656649 458615214162628629492487)
          ·
            refine ⟨687922821243942944238731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458615214162628629492487 687922821243942944238731)
            ·
              refine ⟨1031884231865914416358097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687922821243942944238731 1031884231865914416358097)
              ·
                refine ⟨773913173899435812268573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031884231865914416358097 773913173899435812268573)
                ·
                  refine ⟨290217440212288429600715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773913173899435812268573 290217440212288429600715)
                  ·
                    rfl

theorem cell20_635846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_635846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635846 prefixEnd_635846 := by exact prefixLift 635846
  have htrace : WordTrace (prefixWord ++ tailWord_635846) baseStart_635846 baseEnd_635846 := by
    simpa [prefixWord, tailWord_635846, baseEnd_635846] using wordTrace_append hprefix tailTrace_635846
  have hstable : (prefixWord ++ tailWord_635846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635846).length < 2 ^ (prefixWord ++ tailWord_635846).sum := by decide
  have hdescent : baseEnd_635846 < baseStart_635846 := by decide
  rcases family_descends (prefixWord ++ tailWord_635846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635865 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_635865 : Nat := 118140960795 + 635865 * 2 ^ 59
def prefixEnd_635865 : Nat := 4983230072969 + 3 ^ 40 * 635865 * 2
def baseEnd_635865 : Nat := 290226112330008807967303

theorem tailTrace_635865 : CollatzResearch.WordTrace tailWord_635865 prefixEnd_635865 290226112330008807967303 := by
  unfold tailWord_635865
  simp only [CollatzResearch.WordTrace]
  refine ⟨23191901841377176941253049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15461267894251451294168699 23191901841377176941253049)
  ·
    refine ⟨17393926381032882705939787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23191901841377176941253049 17393926381032882705939787)
    ·
      refine ⟨26090889571549324058909681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17393926381032882705939787 26090889571549324058909681)
      ·
        refine ⟨19568167178661993044182261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26090889571549324058909681 19568167178661993044182261)
        ·
          refine ⟨1834515672999561847892087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19568167178661993044182261 1834515672999561847892087)
          ·
            refine ⟨2751773509499342771838131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834515672999561847892087 2751773509499342771838131)
            ·
              refine ⟨4127660264249014157757197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751773509499342771838131 4127660264249014157757197)
              ·
                refine ⟨1547872599093380309158949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4127660264249014157757197 1547872599093380309158949)
                ·
                  refine ⟨290226112330008807967303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547872599093380309158949 290226112330008807967303)
                  ·
                    rfl

theorem cell20_635865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_635865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635865 prefixEnd_635865 := by exact prefixLift 635865
  have htrace : WordTrace (prefixWord ++ tailWord_635865) baseStart_635865 baseEnd_635865 := by
    simpa [prefixWord, tailWord_635865, baseEnd_635865] using wordTrace_append hprefix tailTrace_635865
  have hstable : (prefixWord ++ tailWord_635865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635865).length < 2 ^ (prefixWord ++ tailWord_635865).sum := by decide
  have hdescent : baseEnd_635865 < baseStart_635865 := by decide
  rcases family_descends (prefixWord ++ tailWord_635865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635875 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_635875 : Nat := 118140960795 + 635875 * 2 ^ 59
def prefixEnd_635875 : Nat := 4983230072969 + 3 ^ 40 * 635875 * 2
def baseEnd_635875 : Nat := 290230676602493217633929

theorem tailTrace_635875 : CollatzResearch.WordTrace tailWord_635875 prefixEnd_635875 290230676602493217633929 := by
  unfold tailWord_635875
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192266571340948649117079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15461511047560632432744719 23192266571340948649117079)
  ·
    refine ⟨34788399857011422973675619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23192266571340948649117079 34788399857011422973675619)
    ·
      refine ⟨52182599785517134460513429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34788399857011422973675619 52182599785517134460513429)
      ·
        refine ⟨2446059364946115677836567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52182599785517134460513429 2446059364946115677836567)
        ·
          refine ⟨3669089047419173516754851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446059364946115677836567 3669089047419173516754851)
          ·
            refine ⟨5503633571128760275132277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669089047419173516754851 5503633571128760275132277)
            ·
              refine ⟨515965647293321275793651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5503633571128760275132277 515965647293321275793651)
              ·
                refine ⟨773948470939981913690477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515965647293321275793651 773948470939981913690477)
                ·
                  refine ⟨290230676602493217633929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773948470939981913690477 290230676602493217633929)
                  ·
                    rfl

theorem cell20_635875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_635875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635875 prefixEnd_635875 := by exact prefixLift 635875
  have htrace : WordTrace (prefixWord ++ tailWord_635875) baseStart_635875 baseEnd_635875 := by
    simpa [prefixWord, tailWord_635875, baseEnd_635875] using wordTrace_append hprefix tailTrace_635875
  have hstable : (prefixWord ++ tailWord_635875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635875).length < 2 ^ (prefixWord ++ tailWord_635875).sum := by decide
  have hdescent : baseEnd_635875 < baseStart_635875 := by decide
  rcases family_descends (prefixWord ++ tailWord_635875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635889 : List Nat := [1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_635889 : Nat := 118140960795 + 635889 * 2 ^ 59
def prefixEnd_635889 : Nat := 4983230072969 + 3 ^ 40 * 635889 * 2
def baseEnd_635889 : Nat := 96745688861323797055735

theorem tailTrace_635889 : CollatzResearch.WordTrace tailWord_635889 prefixEnd_635889 96745688861323797055735 := by
  unfold tailWord_635889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192777193290229040126721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15461851462193486026751147 23192777193290229040126721)
  ·
    refine ⟨17394582894967671780095041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23192777193290229040126721 17394582894967671780095041)
    ·
      refine ⟨13045937171225753835071281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17394582894967671780095041 13045937171225753835071281)
      ·
        refine ⟨9784452878419315376303461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13045937171225753835071281 9784452878419315376303461)
        ·
          refine ⟨1834584914703621633056899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9784452878419315376303461 1834584914703621633056899)
          ·
            refine ⟨2751877372055432449585349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834584914703621633056899 2751877372055432449585349)
            ·
              refine ⟨515977007260393584297253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2751877372055432449585349 515977007260393584297253)
              ·
                refine ⟨96745688861323797055735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515977007260393584297253 96745688861323797055735)
                ·
                  rfl

theorem cell20_635889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_635889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635889 prefixEnd_635889 := by exact prefixLift 635889
  have htrace : WordTrace (prefixWord ++ tailWord_635889) baseStart_635889 baseEnd_635889 := by
    simpa [prefixWord, tailWord_635889, baseEnd_635889] using wordTrace_append hprefix tailTrace_635889
  have hstable : (prefixWord ++ tailWord_635889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635889).length < 2 ^ (prefixWord ++ tailWord_635889).sum := by decide
  have hdescent : baseEnd_635889 < baseStart_635889 := by decide
  rcases family_descends (prefixWord ++ tailWord_635889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635927 : List Nat := [1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_635927 : Nat := 118140960795 + 635927 * 2 ^ 59
def prefixEnd_635927 : Nat := 4983230072969 + 3 ^ 40 * 635927 * 2
def baseEnd_635927 : Nat := 96751470273137382633461

theorem tailTrace_635927 : CollatzResearch.WordTrace tailWord_635927 prefixEnd_635927 96751470273137382633461 := by
  unfold tailWord_635927
  simp only [CollatzResearch.WordTrace]
  refine ⟨23194163167152561530010035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15462775444768374353340023 23194163167152561530010035)
  ·
    refine ⟨34791244750728842295015053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23194163167152561530010035 34791244750728842295015053)
    ·
      refine ⟨13046716781523315860630645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34791244750728842295015053 13046716781523315860630645)
      ·
        refine ⟨1223129698267810861934123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13046716781523315860630645 1223129698267810861934123)
        ·
          refine ⟨1834694547401716292901185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223129698267810861934123 1834694547401716292901185)
          ·
            refine ⟨1376020910551287219675889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834694547401716292901185 1376020910551287219675889)
            ·
              refine ⟨1032015682913465414756917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376020910551287219675889 1032015682913465414756917)
              ·
                refine ⟨96751470273137382633461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032015682913465414756917 96751470273137382633461)
                ·
                  rfl

theorem cell20_635927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_635927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635927 prefixEnd_635927 := by exact prefixLift 635927
  have htrace : WordTrace (prefixWord ++ tailWord_635927) baseStart_635927 baseEnd_635927 := by
    simpa [prefixWord, tailWord_635927, baseEnd_635927] using wordTrace_append hprefix tailTrace_635927
  have hstable : (prefixWord ++ tailWord_635927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635927).length < 2 ^ (prefixWord ++ tailWord_635927).sum := by decide
  have hdescent : baseEnd_635927 < baseStart_635927 := by decide
  rcases family_descends (prefixWord ++ tailWord_635927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635975 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 2]
def baseStart_635975 : Nat := 118140960795 + 635975 * 2 ^ 59
def prefixEnd_635975 : Nat := 4983230072969 + 3 ^ 40 * 635975 * 2
def baseEnd_635975 : Nat := 290276319327337314300187

theorem tailTrace_635975 : CollatzResearch.WordTrace tailWord_635975 prefixEnd_635975 290276319327337314300187 := by
  unfold tailWord_635975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195913870978665727757379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15463942580652443818504919 23195913870978665727757379)
  ·
    refine ⟨34793870806467998591636069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23195913870978665727757379 34793870806467998591636069)
    ·
      refine ⟨6523850776212749735931763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34793870806467998591636069 6523850776212749735931763)
      ·
        refine ⟨9785776164319124603897645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6523850776212749735931763 9785776164319124603897645)
        ·
          refine ⟨3669666061619671726461617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9785776164319124603897645 3669666061619671726461617)
          ·
            refine ⟨2752249546214753794846213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3669666061619671726461617 2752249546214753794846213)
            ·
              refine ⟨516046789915266336533665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2752249546214753794846213 516046789915266336533665)
              ·
                refine ⟨387035092436449752400249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516046789915266336533665 387035092436449752400249)
                ·
                  refine ⟨290276319327337314300187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387035092436449752400249 290276319327337314300187)
                  ·
                    rfl

theorem cell20_635975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2].length) (baseStart_635975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_635975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_635975 prefixEnd_635975 := by exact prefixLift 635975
  have htrace : WordTrace (prefixWord ++ tailWord_635975) baseStart_635975 baseEnd_635975 := by
    simpa [prefixWord, tailWord_635975, baseEnd_635975] using wordTrace_append hprefix tailTrace_635975
  have hstable : (prefixWord ++ tailWord_635975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635975).length < 2 ^ (prefixWord ++ tailWord_635975).sum := by decide
  have hdescent : baseEnd_635975 < baseStart_635975 := by decide
  rcases family_descends (prefixWord ++ tailWord_635975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636013 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 2]
def baseStart_636013 : Nat := 118140960795 + 636013 * 2 ^ 59
def prefixEnd_636013 : Nat := 4983230072969 + 3 ^ 40 * 636013 * 2
def baseEnd_636013 : Nat := 290293663562778071033365

theorem tailTrace_636013 : CollatzResearch.WordTrace tailWord_636013 prefixEnd_636013 290293663562778071033365 := by
  unfold tailWord_636013
  simp only [CollatzResearch.WordTrace]
  refine ⟨23197299844840998217640693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15464866563227332145093795 23197299844840998217640693)
  ·
    refine ⟨2174746860453843582903815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23197299844840998217640693 2174746860453843582903815)
    ·
      refine ⟨3262120290680765374355723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174746860453843582903815 3262120290680765374355723)
      ·
        refine ⟨4893180436021148061533585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262120290680765374355723 4893180436021148061533585)
        ·
          refine ⟨3669885327015861046150189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893180436021148061533585 3669885327015861046150189)
          ·
            refine ⟨1376206997630947892306321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3669885327015861046150189 1376206997630947892306321)
            ·
              refine ⟨1032155248223210919229741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376206997630947892306321 1032155248223210919229741)
              ·
                refine ⟨387058218083704094711153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032155248223210919229741 387058218083704094711153)
                ·
                  refine ⟨290293663562778071033365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387058218083704094711153 290293663562778071033365)
                  ·
                    rfl

theorem cell20_636013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_636013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636013 prefixEnd_636013 := by exact prefixLift 636013
  have htrace : WordTrace (prefixWord ++ tailWord_636013) baseStart_636013 baseEnd_636013 := by
    simpa [prefixWord, tailWord_636013, baseEnd_636013] using wordTrace_append hprefix tailTrace_636013
  have hstable : (prefixWord ++ tailWord_636013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636013).length < 2 ^ (prefixWord ++ tailWord_636013).sum := by decide
  have hdescent : baseEnd_636013 < baseStart_636013 := by decide
  rcases family_descends (prefixWord ++ tailWord_636013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636055 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_636055 : Nat := 118140960795 + 636055 * 2 ^ 59
def prefixEnd_636055 : Nat := 4983230072969 + 3 ^ 40 * 636055 * 2
def baseEnd_636055 : Nat := 290312833507212591633193

theorem tailTrace_636055 : CollatzResearch.WordTrace tailWord_636055 prefixEnd_636055 290312833507212591633193 := by
  unfold tailWord_636055
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198831710688839390669619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15465887807125892927113079 23198831710688839390669619)
  ·
    refine ⟨34798247566033259086004429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198831710688839390669619 34798247566033259086004429)
    ·
      refine ⟨13049342837262472157251661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34798247566033259086004429 13049342837262472157251661)
      ·
        refine ⟨4893503563973427058969373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13049342837262472157251661 4893503563973427058969373)
        ·
          refine ⟨1835063836490035147113515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4893503563973427058969373 1835063836490035147113515)
          ·
            refine ⟨2752595754735052720670273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835063836490035147113515 2752595754735052720670273)
            ·
              refine ⟨2064446816051289540502705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752595754735052720670273 2064446816051289540502705)
              ·
                refine ⟨1548335112038467155377029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064446816051289540502705 1548335112038467155377029)
                ·
                  refine ⟨290312833507212591633193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548335112038467155377029 290312833507212591633193)
                  ·
                    rfl

theorem cell20_636055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_636055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636055 prefixEnd_636055 := by exact prefixLift 636055
  have htrace : WordTrace (prefixWord ++ tailWord_636055) baseStart_636055 baseEnd_636055 := by
    simpa [prefixWord, tailWord_636055, baseEnd_636055] using wordTrace_append hprefix tailTrace_636055
  have hstable : (prefixWord ++ tailWord_636055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636055).length < 2 ^ (prefixWord ++ tailWord_636055).sum := by decide
  have hdescent : baseEnd_636055 < baseStart_636055 := by decide
  rcases family_descends (prefixWord ++ tailWord_636055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636058 : List Nat := [3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_636058 : Nat := 118140960795 + 636058 * 2 ^ 59
def prefixEnd_636058 : Nat := 4983230072969 + 3 ^ 40 * 636058 * 2
def baseEnd_636058 : Nat := 96771400929652638177727

theorem tailTrace_636058 : CollatzResearch.WordTrace tailWord_636058 prefixEnd_636058 96771400929652638177727 := by
  unfold tailWord_636058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799735282419492725757207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15465960753118647268685885 5799735282419492725757207)
  ·
    refine ⟨8699602923629239088635811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799735282419492725757207 8699602923629239088635811)
    ·
      refine ⟨13049404385443858632953717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8699602923629239088635811 13049404385443858632953717)
      ·
        refine ⟨1223381661135361746839411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13049404385443858632953717 1223381661135361746839411)
        ·
          refine ⟨1835072491703042620259117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223381661135361746839411 1835072491703042620259117)
          ·
            refine ⟨688152184388640982597169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1835072491703042620259117 688152184388640982597169)
            ·
              refine ⟨516114138291480736947877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688152184388640982597169 516114138291480736947877)
              ·
                refine ⟨96771400929652638177727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516114138291480736947877 96771400929652638177727)
                ·
                  rfl

theorem cell20_636058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_636058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636058 prefixEnd_636058 := by exact prefixLift 636058
  have htrace : WordTrace (prefixWord ++ tailWord_636058) baseStart_636058 baseEnd_636058 := by
    simpa [prefixWord, tailWord_636058, baseEnd_636058] using wordTrace_append hprefix tailTrace_636058
  have hstable : (prefixWord ++ tailWord_636058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636058).length < 2 ^ (prefixWord ++ tailWord_636058).sum := by decide
  have hdescent : baseEnd_636058 < baseStart_636058 := by decide
  rcases family_descends (prefixWord ++ tailWord_636058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636069 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_636069 : Nat := 118140960795 + 636069 * 2 ^ 59
def prefixEnd_636069 : Nat := 4983230072969 + 3 ^ 40 * 636069 * 2
def baseEnd_636069 : Nat := 290319223488690765166469

theorem tailTrace_636069 : CollatzResearch.WordTrace tailWord_636069 prefixEnd_636069 290319223488690765166469 := by
  unfold tailWord_636069
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199342332638119781679261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466228221758746521119507 23199342332638119781679261)
  ·
    refine ⟨8699753374739294918129723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23199342332638119781679261 8699753374739294918129723)
    ·
      refine ⟨13049630062108942377194585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8699753374739294918129723 13049630062108942377194585)
      ·
        refine ⟨9787222546581706782895939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13049630062108942377194585 9787222546581706782895939)
        ·
          refine ⟨14680833819872560174343909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9787222546581706782895939 14680833819872560174343909)
          ·
            refine ⟨2752656341226105032689483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14680833819872560174343909 2752656341226105032689483)
            ·
              refine ⟨4128984511839157549034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752656341226105032689483 4128984511839157549034225)
              ·
                refine ⟨3096738383879368161775669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128984511839157549034225 3096738383879368161775669)
                ·
                  refine ⟨290319223488690765166469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096738383879368161775669 290319223488690765166469)
                  ·
                    rfl

theorem cell20_636069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_636069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636069 prefixEnd_636069 := by exact prefixLift 636069
  have htrace : WordTrace (prefixWord ++ tailWord_636069) baseStart_636069 baseEnd_636069 := by
    simpa [prefixWord, tailWord_636069, baseEnd_636069] using wordTrace_append hprefix tailTrace_636069
  have hstable : (prefixWord ++ tailWord_636069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636069).length < 2 ^ (prefixWord ++ tailWord_636069).sum := by decide
  have hdescent : baseEnd_636069 < baseStart_636069 := by decide
  rcases family_descends (prefixWord ++ tailWord_636069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636083 : List Nat := [1, 1, 1, 2, 3, 2, 10]
def baseStart_636083 : Nat := 118140960795 + 636083 * 2 ^ 59
def prefixEnd_636083 : Nat := 4983230072969 + 3 ^ 40 * 636083 * 2
def baseEnd_636083 : Nat := 32258401496685437633305

theorem tailTrace_636083 : CollatzResearch.WordTrace tailWord_636083 prefixEnd_636083 32258401496685437633305 := by
  unfold tailWord_636083
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199852954587400172688903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466568636391600115125935 23199852954587400172688903)
  ·
    refine ⟨34799779431881100259033355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23199852954587400172688903 34799779431881100259033355)
    ·
      refine ⟨52199669147821650388550033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34799779431881100259033355 52199669147821650388550033)
      ·
        refine ⟨39149751860866237791412525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52199669147821650388550033 39149751860866237791412525)
        ·
          refine ⟨14681156947824839171779697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39149751860866237791412525 14681156947824839171779697)
          ·
            refine ⟨11010867710868629378834773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14681156947824839171779697 11010867710868629378834773)
            ·
              refine ⟨32258401496685437633305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11010867710868629378834773 32258401496685437633305)
              ·
                rfl

theorem cell20_636083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_636083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636083 prefixEnd_636083 := by exact prefixLift 636083
  have htrace : WordTrace (prefixWord ++ tailWord_636083) baseStart_636083 baseEnd_636083 := by
    simpa [prefixWord, tailWord_636083, baseEnd_636083] using wordTrace_append hprefix tailTrace_636083
  have hstable : (prefixWord ++ tailWord_636083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636083).length < 2 ^ (prefixWord ++ tailWord_636083).sum := by decide
  have hdescent : baseEnd_636083 < baseStart_636083 := by decide
  rcases family_descends (prefixWord ++ tailWord_636083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636089 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 2]
def baseStart_636089 : Nat := 118140960795 + 636089 * 2 ^ 59
def prefixEnd_636089 : Nat := 4983230072969 + 3 ^ 40 * 636089 * 2
def baseEnd_636089 : Nat := 290328352033659584499721

theorem tailTrace_636089 : CollatzResearch.WordTrace tailWord_636089 prefixEnd_636089 290328352033659584499721 := by
  unfold tailWord_636089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23200071792565663197407321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466714528377108798271547 23200071792565663197407321)
  ·
    refine ⟨17400053844424247398055491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23200071792565663197407321 17400053844424247398055491)
    ·
      refine ⟨26100080766636371097083237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17400053844424247398055491 26100080766636371097083237)
      ·
        refine ⟨4893765143744319580703107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26100080766636371097083237 4893765143744319580703107)
        ·
          refine ⟨7340647715616479371054661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893765143744319580703107 7340647715616479371054661)
          ·
            refine ⟨1376371446678089882072749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7340647715616479371054661 1376371446678089882072749)
            ·
              refine ⟨516139292504283705777281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376371446678089882072749 516139292504283705777281)
              ·
                refine ⟨387104469378212779332961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516139292504283705777281 387104469378212779332961)
                ·
                  refine ⟨290328352033659584499721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387104469378212779332961 290328352033659584499721)
                  ·
                    rfl

theorem cell20_636089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_636089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636089 prefixEnd_636089 := by exact prefixLift 636089
  have htrace : WordTrace (prefixWord ++ tailWord_636089) baseStart_636089 baseEnd_636089 := by
    simpa [prefixWord, tailWord_636089, baseEnd_636089] using wordTrace_append hprefix tailTrace_636089
  have hstable : (prefixWord ++ tailWord_636089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636089).length < 2 ^ (prefixWord ++ tailWord_636089).sum := by decide
  have hdescent : baseEnd_636089 < baseStart_636089 := by decide
  rcases family_descends (prefixWord ++ tailWord_636089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636093 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_636093 : Nat := 118140960795 + 636093 * 2 ^ 59
def prefixEnd_636093 : Nat := 4983230072969 + 3 ^ 40 * 636093 * 2
def baseEnd_636093 : Nat := 290330177742653348366371

theorem tailTrace_636093 : CollatzResearch.WordTrace tailWord_636093 prefixEnd_636093 290330177742653348366371 := by
  unfold tailWord_636093
  simp only [CollatzResearch.WordTrace]
  refine ⟨23200217684551171880552933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466811789700781253701955 23200217684551171880552933)
  ·
    refine ⟨4350040815853344727603675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23200217684551171880552933 4350040815853344727603675)
    ·
      refine ⟨6525061223780017091405513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350040815853344727603675 6525061223780017091405513)
      ·
        refine ⟨4893795917835012818554135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525061223780017091405513 4893795917835012818554135)
        ·
          refine ⟨7340693876752519227831203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893795917835012818554135 7340693876752519227831203)
          ·
            refine ⟨11011040815128778841746805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340693876752519227831203 11011040815128778841746805)
            ·
              refine ⟨1032285076418323016413763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11011040815128778841746805 1032285076418323016413763)
              ·
                refine ⟨1548427614627484524620645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032285076418323016413763 1548427614627484524620645)
                ·
                  refine ⟨290330177742653348366371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548427614627484524620645 290330177742653348366371)
                  ·
                    rfl

theorem cell20_636093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_636093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636093 prefixEnd_636093 := by exact prefixLift 636093
  have htrace : WordTrace (prefixWord ++ tailWord_636093) baseStart_636093 baseEnd_636093 := by
    simpa [prefixWord, tailWord_636093, baseEnd_636093] using wordTrace_append hprefix tailTrace_636093
  have hstable : (prefixWord ++ tailWord_636093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636093).length < 2 ^ (prefixWord ++ tailWord_636093).sum := by decide
  have hdescent : baseEnd_636093 < baseStart_636093 := by decide
  rcases family_descends (prefixWord ++ tailWord_636093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636141 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_636141 : Nat := 118140960795 + 636141 * 2 ^ 59
def prefixEnd_636141 : Nat := 4983230072969 + 3 ^ 40 * 636141 * 2
def baseEnd_636141 : Nat := 290352086250578514766175

theorem tailTrace_636141 : CollatzResearch.WordTrace tailWord_636141 prefixEnd_636141 290352086250578514766175 := by
  unfold tailWord_636141
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201968388377276078300277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15467978925584850718866851 23201968388377276078300277)
  ·
    refine ⟨2175184536410369632340651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23201968388377276078300277 2175184536410369632340651)
    ·
      refine ⟨3262776804615554448510977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175184536410369632340651 3262776804615554448510977)
      ·
        refine ⟨2447082603461665836383233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262776804615554448510977 2447082603461665836383233)
        ·
          refine ⟨1835311952596249377287425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447082603461665836383233 1835311952596249377287425)
          ·
            refine ⟨1376483964447187032965569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835311952596249377287425 1376483964447187032965569)
            ·
              refine ⟨1032362973335390274724177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376483964447187032965569 1032362973335390274724177)
              ·
                refine ⟨774272230001542706043133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032362973335390274724177 774272230001542706043133)
                ·
                  refine ⟨290352086250578514766175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774272230001542706043133 290352086250578514766175)
                  ·
                    rfl

theorem cell20_636141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_636141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636141 prefixEnd_636141 := by exact prefixLift 636141
  have htrace : WordTrace (prefixWord ++ tailWord_636141) baseStart_636141 baseEnd_636141 := by
    simpa [prefixWord, tailWord_636141, baseEnd_636141] using wordTrace_append hprefix tailTrace_636141
  have hstable : (prefixWord ++ tailWord_636141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636141).length < 2 ^ (prefixWord ++ tailWord_636141).sum := by decide
  have hdescent : baseEnd_636141 < baseStart_636141 := by decide
  rcases family_descends (prefixWord ++ tailWord_636141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636183 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_636183 : Nat := 118140960795 + 636183 * 2 ^ 59
def prefixEnd_636183 : Nat := 4983230072969 + 3 ^ 40 * 636183 * 2
def baseEnd_636183 : Nat := 290371256195013035366003

theorem tailTrace_636183 : CollatzResearch.WordTrace tailWord_636183 prefixEnd_636183 290371256195013035366003 := by
  unfold tailWord_636183
  simp only [CollatzResearch.WordTrace]
  refine ⟨23203500254225117251329203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15469000169483411500886135 23203500254225117251329203)
  ·
    refine ⟨34805250381337675876993805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23203500254225117251329203 34805250381337675876993805)
    ·
      refine ⟨13051968893001628453872677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34805250381337675876993805 13051968893001628453872677)
      ·
        refine ⟨2447244167437805335101127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13051968893001628453872677 2447244167437805335101127)
        ·
          refine ⟨3670866251156708002651691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447244167437805335101127 3670866251156708002651691)
          ·
            refine ⟨5506299376735062003977537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670866251156708002651691 5506299376735062003977537)
            ·
              refine ⟨4129724532551296502983153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506299376735062003977537 4129724532551296502983153)
              ·
                refine ⟨3097293399413472377237365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4129724532551296502983153 3097293399413472377237365)
                ·
                  refine ⟨290371256195013035366003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097293399413472377237365 290371256195013035366003)
                  ·
                    rfl

theorem cell20_636183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_636183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636183 prefixEnd_636183 := by exact prefixLift 636183
  have htrace : WordTrace (prefixWord ++ tailWord_636183) baseStart_636183 baseEnd_636183 := by
    simpa [prefixWord, tailWord_636183, baseEnd_636183] using wordTrace_append hprefix tailTrace_636183
  have hstable : (prefixWord ++ tailWord_636183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636183).length < 2 ^ (prefixWord ++ tailWord_636183).sum := by decide
  have hdescent : baseEnd_636183 < baseStart_636183 := by decide
  rcases family_descends (prefixWord ++ tailWord_636183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636186 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_636186 : Nat := 118140960795 + 636186 * 2 ^ 59
def prefixEnd_636186 : Nat := 4983230072969 + 3 ^ 40 * 636186 * 2
def baseEnd_636186 : Nat := 290372625476758358265991

theorem tailTrace_636186 : CollatzResearch.WordTrace tailWord_636186 prefixEnd_636186 290372625476758358265991 := by
  unfold tailWord_636186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800902418303562190922103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15469073115476165842458941 5800902418303562190922103)
  ·
    refine ⟨8701353627455343286383155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800902418303562190922103 8701353627455343286383155)
    ·
      refine ⟨13052030441183014929574733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701353627455343286383155 13052030441183014929574733)
      ·
        refine ⟨4894511415443630598590525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13052030441183014929574733 4894511415443630598590525)
        ·
          refine ⟨1835441780791361474471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4894511415443630598590525 1835441780791361474471447)
          ·
            refine ⟨2753162671187042211707171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835441780791361474471447 2753162671187042211707171)
            ·
              refine ⟨4129744006780563317560757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753162671187042211707171 4129744006780563317560757)
              ·
                refine ⟨387163500635677811021321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4129744006780563317560757 387163500635677811021321)
                ·
                  refine ⟨290372625476758358265991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387163500635677811021321 290372625476758358265991)
                  ·
                    rfl

theorem cell20_636186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_636186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636186 prefixEnd_636186 := by exact prefixLift 636186
  have htrace : WordTrace (prefixWord ++ tailWord_636186) baseStart_636186 baseEnd_636186 := by
    simpa [prefixWord, tailWord_636186, baseEnd_636186] using wordTrace_append hprefix tailTrace_636186
  have hstable : (prefixWord ++ tailWord_636186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636186).length < 2 ^ (prefixWord ++ tailWord_636186).sum := by decide
  have hdescent : baseEnd_636186 < baseStart_636186 := by decide
  rcases family_descends (prefixWord ++ tailWord_636186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636200 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_636200 : Nat := 118140960795 + 636200 * 2 ^ 59
def prefixEnd_636200 : Nat := 4983230072969 + 3 ^ 40 * 636200 * 2
def baseEnd_636200 : Nat := 290379015458236531799267

theorem tailTrace_636200 : CollatzResearch.WordTrace tailWord_636200 prefixEnd_636200 290379015458236531799267 := by
  unfold tailWord_636200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602060147581764577349027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15469413530109019436465369 11602060147581764577349027)
  ·
    refine ⟨17403090221372646866023541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11602060147581764577349027 17403090221372646866023541)
    ·
      refine ⟨1631539708253685643689707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17403090221372646866023541 1631539708253685643689707)
      ·
        refine ⟨2447309562380528465534561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631539708253685643689707 2447309562380528465534561)
        ·
          refine ⟨1835482171785396349150921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447309562380528465534561 1835482171785396349150921)
          ·
            refine ⟨1376611628839047261863191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835482171785396349150921 1376611628839047261863191)
            ·
              refine ⟨2064917443258570892794787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376611628839047261863191 2064917443258570892794787)
              ·
                refine ⟨3097376164887856339192181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064917443258570892794787 3097376164887856339192181)
                ·
                  refine ⟨290379015458236531799267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097376164887856339192181 290379015458236531799267)
                  ·
                    rfl

theorem cell20_636200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_636200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636200 prefixEnd_636200 := by exact prefixLift 636200
  have htrace : WordTrace (prefixWord ++ tailWord_636200) baseStart_636200 baseEnd_636200 := by
    simpa [prefixWord, tailWord_636200, baseEnd_636200] using wordTrace_append hprefix tailTrace_636200
  have hstable : (prefixWord ++ tailWord_636200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636200).length < 2 ^ (prefixWord ++ tailWord_636200).sum := by decide
  have hdescent : baseEnd_636200 < baseStart_636200 := by decide
  rcases family_descends (prefixWord ++ tailWord_636200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636231 : List Nat := [1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_636231 : Nat := 118140960795 + 636231 * 2 ^ 59
def prefixEnd_636231 : Nat := 4983230072969 + 3 ^ 40 * 636231 * 2
def baseEnd_636231 : Nat := 96797721567646067255269

theorem tailTrace_636231 : CollatzResearch.WordTrace tailWord_636231 prefixEnd_636231 96797721567646067255269 := by
  unfold tailWord_636231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205250958051221449076547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470167305367480966051031 23205250958051221449076547)
  ·
    refine ⟨34807876437076832173614821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23205250958051221449076547 34807876437076832173614821)
    ·
      refine ⟨6526476831951906032552779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34807876437076832173614821 6526476831951906032552779)
      ·
        refine ⟨9789715247927859048829169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6526476831951906032552779 9789715247927859048829169)
        ·
          refine ⟨7342286435945894286621877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9789715247927859048829169 7342286435945894286621877)
          ·
            refine ⟨688339353369927589370801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7342286435945894286621877 688339353369927589370801)
            ·
              refine ⟨516254515027445692028101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688339353369927589370801 516254515027445692028101)
              ·
                refine ⟨96797721567646067255269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516254515027445692028101 96797721567646067255269)
                ·
                  rfl

theorem cell20_636231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_636231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636231 prefixEnd_636231 := by exact prefixLift 636231
  have htrace : WordTrace (prefixWord ++ tailWord_636231) baseStart_636231 baseEnd_636231 := by
    simpa [prefixWord, tailWord_636231, baseEnd_636231] using wordTrace_append hprefix tailTrace_636231
  have hstable : (prefixWord ++ tailWord_636231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636231).length < 2 ^ (prefixWord ++ tailWord_636231).sum := by decide
  have hdescent : baseEnd_636231 < baseStart_636231 := by decide
  rcases family_descends (prefixWord ++ tailWord_636231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636237 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 2]
def baseStart_636237 : Nat := 118140960795 + 636237 * 2 ^ 59
def prefixEnd_636237 : Nat := 4983230072969 + 3 ^ 40 * 636237 * 2
def baseEnd_636237 : Nat := 290395903266428847565783

theorem tailTrace_636237 : CollatzResearch.WordTrace tailWord_636237 prefixEnd_636237 290395903266428847565783 := by
  unfold tailWord_636237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205469796029484473794965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470313197352989649196643 23205469796029484473794965)
  ·
    refine ⟨1087756396688882084709139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23205469796029484473794965 1087756396688882084709139)
    ·
      refine ⟨1631634595033323127063709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087756396688882084709139 1631634595033323127063709)
      ·
        refine ⟨611862973137496172648891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1631634595033323127063709 611862973137496172648891)
        ·
          refine ⟨917794459706244258973337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611862973137496172648891 917794459706244258973337)
          ·
            refine ⟨688345844779683194230003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917794459706244258973337 688345844779683194230003)
            ·
              refine ⟨1032518767169524791345005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688345844779683194230003 1032518767169524791345005)
              ·
                refine ⟨387194537688571796754377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032518767169524791345005 387194537688571796754377)
                ·
                  refine ⟨290395903266428847565783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387194537688571796754377 290395903266428847565783)
                  ·
                    rfl

theorem cell20_636237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_636237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636237 prefixEnd_636237 := by exact prefixLift 636237
  have htrace : WordTrace (prefixWord ++ tailWord_636237) baseStart_636237 baseEnd_636237 := by
    simpa [prefixWord, tailWord_636237, baseEnd_636237] using wordTrace_append hprefix tailTrace_636237
  have hstable : (prefixWord ++ tailWord_636237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636237).length < 2 ^ (prefixWord ++ tailWord_636237).sum := by decide
  have hdescent : baseEnd_636237 < baseStart_636237 := by decide
  rcases family_descends (prefixWord ++ tailWord_636237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636259 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_636259 : Nat := 118140960795 + 636259 * 2 ^ 59
def prefixEnd_636259 : Nat := 4983230072969 + 3 ^ 40 * 636259 * 2
def baseEnd_636259 : Nat := 290405944665894548832359

theorem tailTrace_636259 : CollatzResearch.WordTrace tailWord_636259 prefixEnd_636259 290405944665894548832359 := by
  unfold tailWord_636259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23206272201949782231095831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470848134633188154063887 23206272201949782231095831)
  ·
    refine ⟨34809408302924673346643747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23206272201949782231095831 34809408302924673346643747)
    ·
      refine ⟨52214112454387010019965621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34809408302924673346643747 52214112454387010019965621)
      ·
        refine ⟨4895073042598782189371777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52214112454387010019965621 4895073042598782189371777)
        ·
          refine ⟨3671304781949086642028833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895073042598782189371777 3671304781949086642028833)
          ·
            refine ⟨2753478586461814981521625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671304781949086642028833 2753478586461814981521625)
            ·
              refine ⟨2065108939846361236141219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753478586461814981521625 2065108939846361236141219)
              ·
                refine ⟨3097663409769541854211829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065108939846361236141219 3097663409769541854211829)
                ·
                  refine ⟨290405944665894548832359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097663409769541854211829 290405944665894548832359)
                  ·
                    rfl

theorem cell20_636259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_636259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636259 prefixEnd_636259 := by exact prefixLift 636259
  have htrace : WordTrace (prefixWord ++ tailWord_636259) baseStart_636259 baseEnd_636259 := by
    simpa [prefixWord, tailWord_636259, baseEnd_636259] using wordTrace_append hprefix tailTrace_636259
  have hstable : (prefixWord ++ tailWord_636259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636259).length < 2 ^ (prefixWord ++ tailWord_636259).sum := by decide
  have hdescent : baseEnd_636259 < baseStart_636259 := by decide
  rcases family_descends (prefixWord ++ tailWord_636259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636273 : List Nat := [1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_636273 : Nat := 118140960795 + 636273 * 2 ^ 59
def prefixEnd_636273 : Nat := 4983230072969 + 3 ^ 40 * 636273 * 2
def baseEnd_636273 : Nat := 96804111549124240788545

theorem tailTrace_636273 : CollatzResearch.WordTrace tailWord_636273 prefixEnd_636273 96804111549124240788545 := by
  unfold tailWord_636273
  simp only [CollatzResearch.WordTrace]
  refine ⟨23206782823899062622105473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15471188549266041748070315 23206782823899062622105473)
  ·
    refine ⟨17405087117924296966579105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23206782823899062622105473 17405087117924296966579105)
    ·
      refine ⟨13053815338443222724934329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17405087117924296966579105 13053815338443222724934329)
      ·
        refine ⟨9790361503832417043700747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13053815338443222724934329 9790361503832417043700747)
        ·
          refine ⟨14685542255748625565551121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790361503832417043700747 14685542255748625565551121)
          ·
            refine ⟨11014156691811469174163341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14685542255748625565551121 11014156691811469174163341)
            ·
              refine ⟨4130308759429300940311253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11014156691811469174163341 4130308759429300940311253)
              ·
                refine ⟨96804111549124240788545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4130308759429300940311253 96804111549124240788545)
                ·
                  rfl

theorem cell20_636273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_636273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636273 prefixEnd_636273 := by exact prefixLift 636273
  have htrace : WordTrace (prefixWord ++ tailWord_636273) baseStart_636273 baseEnd_636273 := by
    simpa [prefixWord, tailWord_636273, baseEnd_636273] using wordTrace_append hprefix tailTrace_636273
  have hstable : (prefixWord ++ tailWord_636273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636273).length < 2 ^ (prefixWord ++ tailWord_636273).sum := by decide
  have hdescent : baseEnd_636273 < baseStart_636273 := by decide
  rcases family_descends (prefixWord ++ tailWord_636273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636314 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_636314 : Nat := 118140960795 + 636314 * 2 ^ 59
def prefixEnd_636314 : Nat := 4983230072969 + 3 ^ 40 * 636314 * 2
def baseEnd_636314 : Nat := 290431048164558801998801

theorem tailTrace_636314 : CollatzResearch.WordTrace tailWord_636314 prefixEnd_636314 290431048164558801998801 := by
  unfold tailWord_636314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802069554187631656086999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15472185477833684416231997 5802069554187631656086999)
  ·
    refine ⟨8703104331281447484130499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802069554187631656086999 8703104331281447484130499)
    ·
      refine ⟨13054656496922171226195749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703104331281447484130499 13054656496922171226195749)
      ·
        refine ⟨2447748093172907104911703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13054656496922171226195749 2447748093172907104911703)
        ·
          refine ⟨3671622139759360657367555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447748093172907104911703 3671622139759360657367555)
          ·
            refine ⟨5507433209639040986051333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671622139759360657367555 5507433209639040986051333)
            ·
              refine ⟨1032643726807320184884625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5507433209639040986051333 1032643726807320184884625)
              ·
                refine ⟨774482795105490138663469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032643726807320184884625 774482795105490138663469)
                ·
                  refine ⟨290431048164558801998801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774482795105490138663469 290431048164558801998801)
                  ·
                    rfl

theorem cell20_636314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_636314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636314 prefixEnd_636314 := by exact prefixLift 636314
  have htrace : WordTrace (prefixWord ++ tailWord_636314) baseStart_636314 baseEnd_636314 := by
    simpa [prefixWord, tailWord_636314, baseEnd_636314] using wordTrace_append hprefix tailTrace_636314
  have hstable : (prefixWord ++ tailWord_636314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636314).length < 2 ^ (prefixWord ++ tailWord_636314).sum := by decide
  have hdescent : baseEnd_636314 < baseStart_636314 := by decide
  rcases family_descends (prefixWord ++ tailWord_636314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636317 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 2]
def baseStart_636317 : Nat := 118140960795 + 636317 * 2 ^ 59
def prefixEnd_636317 : Nat := 4983230072969 + 3 ^ 40 * 636317 * 2
def baseEnd_636317 : Nat := 290432417446304124898789

theorem tailTrace_636317 : CollatzResearch.WordTrace tailWord_636317 prefixEnd_636317 290432417446304124898789 := by
  unfold tailWord_636317
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208387635739658136707205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472258423826438757804803 23208387635739658136707205)
  ·
    refine ⟨4351572681701185900632601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23208387635739658136707205 4351572681701185900632601)
    ·
      refine ⟨3263679511275889425474451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4351572681701185900632601 3263679511275889425474451)
      ·
        refine ⟨4895519266913834138211677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263679511275889425474451 4895519266913834138211677)
        ·
          refine ⟨1835819725092687801829379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4895519266913834138211677 1835819725092687801829379)
          ·
            refine ⟨2753729587639031702744069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835819725092687801829379 2753729587639031702744069)
            ·
              refine ⟨516324297682318444264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2753729587639031702744069 516324297682318444264513)
              ·
                refine ⟨387243223261738833198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516324297682318444264513 387243223261738833198385)
                ·
                  refine ⟨290432417446304124898789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387243223261738833198385 290432417446304124898789)
                  ·
                    rfl

theorem cell20_636317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_636317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636317 prefixEnd_636317 := by exact prefixLift 636317
  have htrace : WordTrace (prefixWord ++ tailWord_636317) baseStart_636317 baseEnd_636317 := by
    simpa [prefixWord, tailWord_636317, baseEnd_636317] using wordTrace_append hprefix tailTrace_636317
  have hstable : (prefixWord ++ tailWord_636317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636317).length < 2 ^ (prefixWord ++ tailWord_636317).sum := by decide
  have hdescent : baseEnd_636317 < baseStart_636317 := by decide
  rcases family_descends (prefixWord ++ tailWord_636317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636345 : List Nat := [1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_636345 : Nat := 118140960795 + 636345 * 2 ^ 59
def prefixEnd_636345 : Nat := 4983230072969 + 3 ^ 40 * 636345 * 2
def baseEnd_636345 : Nat := 96815065803086823988447

theorem tailTrace_636345 : CollatzResearch.WordTrace tailWord_636345 prefixEnd_636345 96815065803086823988447 := by
  unfold tailWord_636345
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209408879638218918726489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472939253092145945817659 23209408879638218918726489)
  ·
    refine ⟨17407056659728664189044867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23209408879638218918726489 17407056659728664189044867)
    ·
      refine ⟨26110584989592996283567301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17407056659728664189044867 26110584989592996283567301)
      ·
        refine ⟨4895734685548686803168869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26110584989592996283567301 4895734685548686803168869)
        ·
          refine ⟨917950253540378775594163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4895734685548686803168869 917950253540378775594163)
          ·
            refine ⟨1376925380310568163391245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917950253540378775594163 1376925380310568163391245)
            ·
              refine ⟨516347017616463061271717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376925380310568163391245 516347017616463061271717)
              ·
                refine ⟨96815065803086823988447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516347017616463061271717 96815065803086823988447)
                ·
                  rfl

theorem cell20_636345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_636345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636345 prefixEnd_636345 := by exact prefixLift 636345
  have htrace : WordTrace (prefixWord ++ tailWord_636345) baseStart_636345 baseEnd_636345 := by
    simpa [prefixWord, tailWord_636345, baseEnd_636345] using wordTrace_append hprefix tailTrace_636345
  have hstable : (prefixWord ++ tailWord_636345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636345).length < 2 ^ (prefixWord ++ tailWord_636345).sum := by decide
  have hdescent : baseEnd_636345 < baseStart_636345 := by decide
  rcases family_descends (prefixWord ++ tailWord_636345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636373 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_636373 : Nat := 118140960795 + 636373 * 2 ^ 59
def prefixEnd_636373 : Nat := 4983230072969 + 3 ^ 40 * 636373 * 2
def baseEnd_636373 : Nat := 290457977372216819031893

theorem tailTrace_636373 : CollatzResearch.WordTrace tailWord_636373 prefixEnd_636373 290457977372216819031893 := by
  unfold tailWord_636373
  simp only [CollatzResearch.WordTrace]
  refine ⟨23210430123536779700745773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15473620082357853133830515 23210430123536779700745773)
  ·
    refine ⟨8703911296326292387779665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23210430123536779700745773 8703911296326292387779665)
    ·
      refine ⟨6527933472244719290834749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8703911296326292387779665 6527933472244719290834749)
      ·
        refine ⟨2447975052091769734063031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6527933472244719290834749 2447975052091769734063031)
        ·
          refine ⟨3671962578137654601094547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447975052091769734063031 3671962578137654601094547)
          ·
            refine ⟨5507943867206481901641821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671962578137654601094547 5507943867206481901641821)
            ·
              refine ⟨2065478950202430713115683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5507943867206481901641821 2065478950202430713115683)
              ·
                refine ⟨3098218425303646069673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065478950202430713115683 3098218425303646069673525)
                ·
                  refine ⟨290457977372216819031893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098218425303646069673525 290457977372216819031893)
                  ·
                    rfl

theorem cell20_636373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_636373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636373 prefixEnd_636373 := by exact prefixLift 636373
  have htrace : WordTrace (prefixWord ++ tailWord_636373) baseStart_636373 baseEnd_636373 := by
    simpa [prefixWord, tailWord_636373, baseEnd_636373] using wordTrace_append hprefix tailTrace_636373
  have hstable : (prefixWord ++ tailWord_636373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636373).length < 2 ^ (prefixWord ++ tailWord_636373).sum := by decide
  have hdescent : baseEnd_636373 < baseStart_636373 := by decide
  rcases family_descends (prefixWord ++ tailWord_636373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636435 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_636435 : Nat := 118140960795 + 636435 * 2 ^ 59
def prefixEnd_636435 : Nat := 4983230072969 + 3 ^ 40 * 636435 * 2
def baseEnd_636435 : Nat := 290486275861620158964973

theorem tailTrace_636435 : CollatzResearch.WordTrace tailWord_636435 prefixEnd_636435 290486275861620158964973 := by
  unfold tailWord_636435
  simp only [CollatzResearch.WordTrace]
  refine ⟨23212691449312164289502759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15475127632874776193001839 23212691449312164289502759)
  ·
    refine ⟨34819037173968246434254139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23212691449312164289502759 34819037173968246434254139)
    ·
      refine ⟨52228555760952369651381209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34819037173968246434254139 52228555760952369651381209)
      ·
        refine ⟨39171416820714277238535907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52228555760952369651381209 39171416820714277238535907)
        ·
          refine ⟨58757125231071415857803861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39171416820714277238535907 58757125231071415857803861)
          ·
            refine ⟨688560061301618154583639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 58757125231071415857803861 688560061301618154583639)
            ·
              refine ⟨1032840091952427231875459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688560061301618154583639 1032840091952427231875459)
              ·
                refine ⟨1549260137928640847813189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032840091952427231875459 1549260137928640847813189)
                ·
                  refine ⟨290486275861620158964973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549260137928640847813189 290486275861620158964973)
                  ·
                    rfl

theorem cell20_636435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_636435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636435 prefixEnd_636435 := by exact prefixLift 636435
  have htrace : WordTrace (prefixWord ++ tailWord_636435) baseStart_636435 baseEnd_636435 := by
    simpa [prefixWord, tailWord_636435, baseEnd_636435] using wordTrace_append hprefix tailTrace_636435
  have hstable : (prefixWord ++ tailWord_636435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636435).length < 2 ^ (prefixWord ++ tailWord_636435).sum := by decide
  have hdescent : baseEnd_636435 < baseStart_636435 := by decide
  rcases family_descends (prefixWord ++ tailWord_636435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636486 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_636486 : Nat := 118140960795 + 636486 * 2 ^ 59
def prefixEnd_636486 : Nat := 4983230072969 + 3 ^ 40 * 636486 * 2
def baseEnd_636486 : Nat := 290509553651290648264765

theorem tailTrace_636486 : CollatzResearch.WordTrace tailWord_636486 prefixEnd_636486 290509553651290648264765 := by
  unfold tailWord_636486
  simp only [CollatzResearch.WordTrace]
  refine ⟨725454736628981249987791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15476367714751599999739541 725454736628981249987791)
  ·
    refine ⟨1088182104943471874981687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725454736628981249987791 1088182104943471874981687)
    ·
      refine ⟨1632273157415207812472531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088182104943471874981687 1632273157415207812472531)
      ·
        refine ⟨2448409736122811718708797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632273157415207812472531 2448409736122811718708797)
        ·
          refine ⟨918153651046054394515799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2448409736122811718708797 918153651046054394515799)
          ·
            refine ⟨1377230476569081591773699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918153651046054394515799 1377230476569081591773699)
            ·
              refine ⟨2065845714853622387660549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377230476569081591773699 2065845714853622387660549)
              ·
                refine ⟨387346071535054197686353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065845714853622387660549 387346071535054197686353)
                ·
                  refine ⟨290509553651290648264765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387346071535054197686353 290509553651290648264765)
                  ·
                    rfl

theorem cell20_636486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_636486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636486 prefixEnd_636486 := by exact prefixLift 636486
  have htrace : WordTrace (prefixWord ++ tailWord_636486) baseStart_636486 baseEnd_636486 := by
    simpa [prefixWord, tailWord_636486, baseEnd_636486] using wordTrace_append hprefix tailTrace_636486
  have hstable : (prefixWord ++ tailWord_636486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636486).length < 2 ^ (prefixWord ++ tailWord_636486).sum := by decide
  have hdescent : baseEnd_636486 < baseStart_636486 := by decide
  rcases family_descends (prefixWord ++ tailWord_636486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636494 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_636494 : Nat := 118140960795 + 636494 * 2 ^ 59
def prefixEnd_636494 : Nat := 4983230072969 + 3 ^ 40 * 636494 * 2
def baseEnd_636494 : Nat := 290513205069278175998065

theorem tailTrace_636494 : CollatzResearch.WordTrace tailWord_636494 prefixEnd_636494 290513205069278175998065 := by
  unfold tailWord_636494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901855419512302170737567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15476562237398944910600357 2901855419512302170737567)
  ·
    refine ⟨4352783129268453256106351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901855419512302170737567 4352783129268453256106351)
    ·
      refine ⟨6529174693902679884159527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4352783129268453256106351 6529174693902679884159527)
      ·
        refine ⟨9793762040854019826239291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529174693902679884159527 9793762040854019826239291)
        ·
          refine ⟨14690643061281029739358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793762040854019826239291 14690643061281029739358937)
          ·
            refine ⟨11017982295960772304519203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14690643061281029739358937 11017982295960772304519203)
            ·
              refine ⟨16526973443941158456778805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11017982295960772304519203 16526973443941158456778805)
              ·
                refine ⟨1549403760369483605323013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16526973443941158456778805 1549403760369483605323013)
                ·
                  refine ⟨290513205069278175998065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549403760369483605323013 290513205069278175998065)
                  ·
                    rfl

theorem cell20_636494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_636494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636494 prefixEnd_636494 := by exact prefixLift 636494
  have htrace : WordTrace (prefixWord ++ tailWord_636494) baseStart_636494 baseEnd_636494 := by
    simpa [prefixWord, tailWord_636494, baseEnd_636494] using wordTrace_append hprefix tailTrace_636494
  have hstable : (prefixWord ++ tailWord_636494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636494).length < 2 ^ (prefixWord ++ tailWord_636494).sum := by decide
  have hdescent : baseEnd_636494 < baseStart_636494 := by decide
  rcases family_descends (prefixWord ++ tailWord_636494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636528 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_636528 : Nat := 118140960795 + 636528 * 2 ^ 59
def prefixEnd_636528 : Nat := 4983230072969 + 3 ^ 40 * 636528 * 2
def baseEnd_636528 : Nat := 290528723595725168864593

theorem tailTrace_636528 : CollatzResearch.WordTrace tailWord_636528 prefixEnd_636528 290528723595725168864593 := by
  unfold tailWord_636528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608041718987620586319119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15477388958650160781758825 11608041718987620586319119)
  ·
    refine ⟨17412062578481430879478679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11608041718987620586319119 17412062578481430879478679)
    ·
      refine ⟨26118093867722146319218019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17412062578481430879478679 26118093867722146319218019)
      ·
        refine ⟨39177140801583219478827029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26118093867722146319218019 39177140801583219478827029)
        ·
          refine ⟨1836428475074213413070017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39177140801583219478827029 1836428475074213413070017)
          ·
            refine ⟨1377321356305660059802513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836428475074213413070017 1377321356305660059802513)
            ·
              refine ⟨1032991017229245044851885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377321356305660059802513 1032991017229245044851885)
              ·
                refine ⟨387371631460966891819457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032991017229245044851885 387371631460966891819457)
                ·
                  refine ⟨290528723595725168864593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387371631460966891819457 290528723595725168864593)
                  ·
                    rfl

theorem cell20_636528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_636528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636528 prefixEnd_636528 := by exact prefixLift 636528
  have htrace : WordTrace (prefixWord ++ tailWord_636528) baseStart_636528 baseEnd_636528 := by
    simpa [prefixWord, tailWord_636528, baseEnd_636528] using wordTrace_append hprefix tailTrace_636528
  have hstable : (prefixWord ++ tailWord_636528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636528).length < 2 ^ (prefixWord ++ tailWord_636528).sum := by decide
  have hdescent : baseEnd_636528 < baseStart_636528 := by decide
  rcases family_descends (prefixWord ++ tailWord_636528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636549 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 2]
def baseStart_636549 : Nat := 118140960795 + 636549 * 2 ^ 59
def prefixEnd_636549 : Nat := 4983230072969 + 3 ^ 40 * 636549 * 2
def baseEnd_636549 : Nat := 290538308567942429164507

theorem tailTrace_636549 : CollatzResearch.WordTrace tailWord_636549 prefixEnd_636549 290538308567942429164507 := by
  unfold tailWord_636549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216849370899161759152701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15477899580599441172768467 23216849370899161759152701)
  ·
    refine ⟨8706318514087185659682263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23216849370899161759152701 8706318514087185659682263)
    ·
      refine ⟨13059477771130778489523395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8706318514087185659682263 13059477771130778489523395)
      ·
        refine ⟨19589216656696167734285093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13059477771130778489523395 19589216656696167734285093)
        ·
          refine ⟨3672978123130531450178455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19589216656696167734285093 3672978123130531450178455)
          ·
            refine ⟨5509467184695797175267683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672978123130531450178455 5509467184695797175267683)
            ·
              refine ⟨8264200777043695762901525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509467184695797175267683 8264200777043695762901525)
              ·
                refine ⟨387384411423923238886009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8264200777043695762901525 387384411423923238886009)
                ·
                  refine ⟨290538308567942429164507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387384411423923238886009 290538308567942429164507)
                  ·
                    rfl

theorem cell20_636549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_636549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636549 prefixEnd_636549 := by exact prefixLift 636549
  have htrace : WordTrace (prefixWord ++ tailWord_636549) baseStart_636549 baseEnd_636549 := by
    simpa [prefixWord, tailWord_636549, baseEnd_636549] using wordTrace_append hprefix tailTrace_636549
  have hstable : (prefixWord ++ tailWord_636549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636549).length < 2 ^ (prefixWord ++ tailWord_636549).sum := by decide
  have hdescent : baseEnd_636549 < baseStart_636549 := by decide
  rcases family_descends (prefixWord ++ tailWord_636549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636590 : List Nat := [4, 1, 4, 1, 3, 1, 6]
def baseStart_636590 : Nat := 118140960795 + 636590 * 2 ^ 59
def prefixEnd_636590 : Nat := 4983230072969 + 3 ^ 40 * 636590 * 2
def baseEnd_636590 : Nat := 32284113565014278755297

theorem tailTrace_636590 : CollatzResearch.WordTrace tailWord_636590 prefixEnd_636590 32284113565014278755297 := by
  unfold tailWord_636590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902293095468828220174403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15478896509167083840930149 2902293095468828220174403)
  ·
    refine ⟨4353439643203242330261605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902293095468828220174403 4353439643203242330261605)
    ·
      refine ⟨816269933100607936924051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4353439643203242330261605 816269933100607936924051)
      ·
        refine ⟨1224404899650911905386077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816269933100607936924051 1224404899650911905386077)
        ·
          refine ⟨459151837369091964519779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1224404899650911905386077 459151837369091964519779)
          ·
            refine ⟨688727756053637946779669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459151837369091964519779 688727756053637946779669)
            ·
              refine ⟨32284113565014278755297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 688727756053637946779669 32284113565014278755297)
              ·
                rfl

theorem cell20_636590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_636590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636590 prefixEnd_636590 := by exact prefixLift 636590
  have htrace : WordTrace (prefixWord ++ tailWord_636590) baseStart_636590 baseEnd_636590 := by
    simpa [prefixWord, tailWord_636590, baseEnd_636590] using wordTrace_append hprefix tailTrace_636590
  have hstable : (prefixWord ++ tailWord_636590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636590).length < 2 ^ (prefixWord ++ tailWord_636590).sum := by decide
  have hdescent : baseEnd_636590 < baseStart_636590 := by decide
  rcases family_descends (prefixWord ++ tailWord_636590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636610 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_636610 : Nat := 118140960795 + 636610 * 2 ^ 59
def prefixEnd_636610 : Nat := 4983230072969 + 3 ^ 40 * 636610 * 2
def baseEnd_636610 : Nat := 290566150630097328130925

theorem tailTrace_636610 : CollatzResearch.WordTrace tailWord_636610 prefixEnd_636610 290566150630097328130925 := by
  unfold tailWord_636610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804768555919542294280821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15479382815785446118082189 5804768555919542294280821)
  ·
    refine ⟨544197052117457090088827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5804768555919542294280821 544197052117457090088827)
    ·
      refine ⟨816295578176185635133241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544197052117457090088827 816295578176185635133241)
      ·
        refine ⟨612221683632139226349931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816295578176185635133241 612221683632139226349931)
        ·
          refine ⟨918332525448208839524897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612221683632139226349931 918332525448208839524897)
          ·
            refine ⟨688749394086156629643673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918332525448208839524897 688749394086156629643673)
            ·
              refine ⟨516562045564617472232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688749394086156629643673 516562045564617472232755)
              ·
                refine ⟨774843068346926208349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516562045564617472232755 774843068346926208349133)
                ·
                  refine ⟨290566150630097328130925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774843068346926208349133 290566150630097328130925)
                  ·
                    rfl

theorem cell20_636610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_636610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636610 prefixEnd_636610 := by exact prefixLift 636610
  have htrace : WordTrace (prefixWord ++ tailWord_636610) baseStart_636610 baseEnd_636610 := by
    simpa [prefixWord, tailWord_636610, baseEnd_636610] using wordTrace_append hprefix tailTrace_636610
  have hstable : (prefixWord ++ tailWord_636610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636610).length < 2 ^ (prefixWord ++ tailWord_636610).sum := by decide
  have hdescent : baseEnd_636610 < baseStart_636610 := by decide
  rcases family_descends (prefixWord ++ tailWord_636610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636614 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_636614 : Nat := 118140960795 + 636614 * 2 ^ 59
def prefixEnd_636614 : Nat := 4983230072969 + 3 ^ 40 * 636614 * 2
def baseEnd_636614 : Nat := 290567976339091091997575

theorem tailTrace_636614 : CollatzResearch.WordTrace tailWord_636614 prefixEnd_636614 290567976339091091997575 := by
  unfold tailWord_636614
  simp only [CollatzResearch.WordTrace]
  refine ⟨725600628614489933133403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15479480077109118573512597 725600628614489933133403)
  ·
    refine ⟨1088400942921734899700105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725600628614489933133403 1088400942921734899700105)
    ·
      refine ⟨816300707191301174775079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1088400942921734899700105 816300707191301174775079)
      ·
        refine ⟨1224451060786951762162619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816300707191301174775079 1224451060786951762162619)
        ·
          refine ⟨1836676591180427643243929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224451060786951762162619 1836676591180427643243929)
          ·
            refine ⟨1377507443385320732432947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836676591180427643243929 1377507443385320732432947)
            ·
              refine ⟨2066261165077981098649421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377507443385320732432947 2066261165077981098649421)
              ·
                refine ⟨774847936904242911993533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066261165077981098649421 774847936904242911993533)
                ·
                  refine ⟨290567976339091091997575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774847936904242911993533 290567976339091091997575)
                  ·
                    rfl

theorem cell20_636614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_636614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636614 prefixEnd_636614 := by exact prefixLift 636614
  have htrace : WordTrace (prefixWord ++ tailWord_636614) baseStart_636614 baseEnd_636614 := by
    simpa [prefixWord, tailWord_636614, baseEnd_636614] using wordTrace_append hprefix tailTrace_636614
  have hstable : (prefixWord ++ tailWord_636614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636614).length < 2 ^ (prefixWord ++ tailWord_636614).sum := by decide
  have hdescent : baseEnd_636614 < baseStart_636614 := by decide
  rcases family_descends (prefixWord ++ tailWord_636614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636615 : List Nat := [1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_636615 : Nat := 118140960795 + 636615 * 2 ^ 59
def prefixEnd_636615 : Nat := 4983230072969 + 3 ^ 40 * 636615 * 2
def baseEnd_636615 : Nat := 96856144255446510988079

theorem tailTrace_636615 : CollatzResearch.WordTrace tailWord_636615 prefixEnd_636615 96856144255446510988079 := by
  unfold tailWord_636615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23219256588660055031055299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15479504392440036687370199 23219256588660055031055299)
  ·
    refine ⟨34828884882990082546582949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23219256588660055031055299 34828884882990082546582949)
    ·
      refine ⟨6530415915560640477484303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34828884882990082546582949 6530415915560640477484303)
      ·
        refine ⟨9795623873340960716226455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530415915560640477484303 9795623873340960716226455)
        ·
          refine ⟨14693435810011441074339683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795623873340960716226455 14693435810011441074339683)
          ·
            refine ⟨22040153715017161611509525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14693435810011441074339683 22040153715017161611509525)
            ·
              refine ⟨1033132205391429450539509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22040153715017161611509525 1033132205391429450539509)
              ·
                refine ⟨96856144255446510988079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1033132205391429450539509 96856144255446510988079)
                ·
                  rfl

theorem cell20_636615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_636615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636615 prefixEnd_636615 := by exact prefixLift 636615
  have htrace : WordTrace (prefixWord ++ tailWord_636615) baseStart_636615 baseEnd_636615 := by
    simpa [prefixWord, tailWord_636615, baseEnd_636615] using wordTrace_append hprefix tailTrace_636615
  have hstable : (prefixWord ++ tailWord_636615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636615).length < 2 ^ (prefixWord ++ tailWord_636615).sum := by decide
  have hdescent : baseEnd_636615 < baseStart_636615 := by decide
  rcases family_descends (prefixWord ++ tailWord_636615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636618 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_636618 : Nat := 118140960795 + 636618 * 2 ^ 59
def prefixEnd_636618 : Nat := 4983230072969 + 3 ^ 40 * 636618 * 2
def baseEnd_636618 : Nat := 290569802048084855864225

theorem tailTrace_636618 : CollatzResearch.WordTrace tailWord_636618 prefixEnd_636618 290569802048084855864225 := by
  unfold tailWord_636618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804841501912296635853627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15479577338432791028943005 5804841501912296635853627)
  ·
    refine ⟨8707262252868444953780441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5804841501912296635853627 8707262252868444953780441)
    ·
      refine ⟨6530446689651333715335331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8707262252868444953780441 6530446689651333715335331)
      ·
        refine ⟨9795670034477000573002997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530446689651333715335331 9795670034477000573002997)
        ·
          refine ⟨918344065732218803719031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9795670034477000573002997 918344065732218803719031)
          ·
            refine ⟨1377516098598328205578547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918344065732218803719031 1377516098598328205578547)
            ·
              refine ⟨2066274147897492308367821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377516098598328205578547 2066274147897492308367821)
              ·
                refine ⟨774852805461559615637933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066274147897492308367821 774852805461559615637933)
                ·
                  refine ⟨290569802048084855864225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774852805461559615637933 290569802048084855864225)
                  ·
                    rfl

theorem cell20_636618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_636618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636618 prefixEnd_636618 := by exact prefixLift 636618
  have htrace : WordTrace (prefixWord ++ tailWord_636618) baseStart_636618 baseEnd_636618 := by
    simpa [prefixWord, tailWord_636618, baseEnd_636618] using wordTrace_append hprefix tailTrace_636618
  have hstable : (prefixWord ++ tailWord_636618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636618).length < 2 ^ (prefixWord ++ tailWord_636618).sum := by decide
  have hdescent : baseEnd_636618 < baseStart_636618 := by decide
  rcases family_descends (prefixWord ++ tailWord_636618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636653 : List Nat := [1, 5, 1, 2, 1, 10]
def baseStart_636653 : Nat := 118140960795 + 636653 * 2 ^ 59
def prefixEnd_636653 : Nat := 4983230072969 + 3 ^ 40 * 636653 * 2
def baseEnd_636653 : Nat := 10762436185251121840645

theorem tailTrace_636653 : CollatzResearch.WordTrace tailWord_636653 prefixEnd_636653 10762436185251121840645 := by
  unfold tailWord_636653
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220642562522387520938613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15480428375014925013959075 23220642562522387520938613)
  ·
    refine ⟨2176935240236473830087995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23220642562522387520938613 2176935240236473830087995)
    ·
      refine ⟨3265402860354710745131993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176935240236473830087995 3265402860354710745131993)
      ·
        refine ⟨2449052145266033058848995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265402860354710745131993 2449052145266033058848995)
        ·
          refine ⟨3673578217899049588273493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449052145266033058848995 3673578217899049588273493)
          ·
            refine ⟨10762436185251121840645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3673578217899049588273493 10762436185251121840645)
            ·
              rfl

theorem cell20_636653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_636653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636653 prefixEnd_636653 := by exact prefixLift 636653
  have htrace : WordTrace (prefixWord ++ tailWord_636653) baseStart_636653 baseEnd_636653 := by
    simpa [prefixWord, tailWord_636653, baseEnd_636653] using wordTrace_append hprefix tailTrace_636653
  have hstable : (prefixWord ++ tailWord_636653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636653).length < 2 ^ (prefixWord ++ tailWord_636653).sum := by decide
  have hdescent : baseEnd_636653 < baseStart_636653 := by decide
  rcases family_descends (prefixWord ++ tailWord_636653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636718 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_636718 : Nat := 118140960795 + 636718 * 2 ^ 59
def prefixEnd_636718 : Nat := 4983230072969 + 3 ^ 40 * 636718 * 2
def baseEnd_636718 : Nat := 290615444772928952530483

theorem tailTrace_636718 : CollatzResearch.WordTrace tailWord_636718 prefixEnd_636718 290615444772928952530483 := by
  unfold tailWord_636718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902876663410862952756851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15482008871524602414703205 2902876663410862952756851)
  ·
    refine ⟨4354314995116294429135277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902876663410862952756851 4354314995116294429135277)
    ·
      refine ⟨1632868123168610410925729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4354314995116294429135277 1632868123168610410925729)
      ·
        refine ⟨1224651092376457808194297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1632868123168610410925729 1224651092376457808194297)
        ·
          refine ⟨918488319282343356145723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1224651092376457808194297 918488319282343356145723)
          ·
            refine ⟨1377732478923515034218585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918488319282343356145723 1377732478923515034218585)
            ·
              refine ⟨1033299359192636275663939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377732478923515034218585 1033299359192636275663939)
              ·
                refine ⟨1549949038788954413495909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033299359192636275663939 1549949038788954413495909)
                ·
                  refine ⟨290615444772928952530483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549949038788954413495909 290615444772928952530483)
                  ·
                    rfl

theorem cell20_636718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_636718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636718 prefixEnd_636718 := by exact prefixLift 636718
  have htrace : WordTrace (prefixWord ++ tailWord_636718) baseStart_636718 baseEnd_636718 := by
    simpa [prefixWord, tailWord_636718, baseEnd_636718] using wordTrace_append hprefix tailTrace_636718
  have hstable : (prefixWord ++ tailWord_636718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636718).length < 2 ^ (prefixWord ++ tailWord_636718).sum := by decide
  have hdescent : baseEnd_636718 < baseStart_636718 := by decide
  rcases family_descends (prefixWord ++ tailWord_636718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636722 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_636722 : Nat := 118140960795 + 636722 * 2 ^ 59
def prefixEnd_636722 : Nat := 4983230072969 + 3 ^ 40 * 636722 * 2
def baseEnd_636722 : Nat := 290617270481922716397133

theorem tailTrace_636722 : CollatzResearch.WordTrace tailWord_636722 prefixEnd_636722 290617270481922716397133 := by
  unfold tailWord_636722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805789799818103076300105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15482106132848274870133613 5805789799818103076300105)
  ·
    refine ⟨4354342349863577307225079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5805789799818103076300105 4354342349863577307225079)
    ·
      refine ⟨6531513524795365960837619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4354342349863577307225079 6531513524795365960837619)
      ·
        refine ⟨9797270287193048941256429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6531513524795365960837619 9797270287193048941256429)
        ·
          refine ⟨3673976357697393352971161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9797270287193048941256429 3673976357697393352971161)
          ·
            refine ⟨2755482268273045014728371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673976357697393352971161 2755482268273045014728371)
            ·
              refine ⟨4133223402409567522092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755482268273045014728371 4133223402409567522092557)
              ·
                refine ⟨1549958775903587820784709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4133223402409567522092557 1549958775903587820784709)
                ·
                  refine ⟨290617270481922716397133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549958775903587820784709 290617270481922716397133)
                  ·
                    rfl

theorem cell20_636722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_636722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636722 prefixEnd_636722 := by exact prefixLift 636722
  have htrace : WordTrace (prefixWord ++ tailWord_636722) baseStart_636722 baseEnd_636722 := by
    simpa [prefixWord, tailWord_636722, baseEnd_636722] using wordTrace_append hprefix tailTrace_636722
  have hstable : (prefixWord ++ tailWord_636722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636722).length < 2 ^ (prefixWord ++ tailWord_636722).sum := by decide
  have hdescent : baseEnd_636722 < baseStart_636722 := by decide
  rcases family_descends (prefixWord ++ tailWord_636722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636742 : List Nat := [6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_636742 : Nat := 118140960795 + 636742 * 2 ^ 59
def prefixEnd_636742 : Nat := 4983230072969 + 3 ^ 40 * 636742 * 2
def baseEnd_636742 : Nat := 96875466342297178576795

theorem tailTrace_636742 : CollatzResearch.WordTrace tailWord_636742 prefixEnd_636742 96875466342297178576795 := by
  unfold tailWord_636742
  simp only [CollatzResearch.WordTrace]
  refine ⟨725746520599998616279015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15482592439466637147285653 725746520599998616279015)
  ·
    refine ⟨1088619780899997924418523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725746520599998616279015 1088619780899997924418523)
    ·
      refine ⟨1632929671349996886627785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088619780899997924418523 1632929671349996886627785)
      ·
        refine ⟨1224697253512497664970839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1632929671349996886627785 1224697253512497664970839)
        ·
          refine ⟨1837045880268746497456259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224697253512497664970839 1837045880268746497456259)
          ·
            refine ⟨2755568820403119746184389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837045880268746497456259 2755568820403119746184389)
            ·
              refine ⟨516669153825584952409573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2755568820403119746184389 516669153825584952409573)
              ·
                refine ⟨96875466342297178576795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516669153825584952409573 96875466342297178576795)
                ·
                  rfl

theorem cell20_636742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_636742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636742 prefixEnd_636742 := by exact prefixLift 636742
  have htrace : WordTrace (prefixWord ++ tailWord_636742) baseStart_636742 baseEnd_636742 := by
    simpa [prefixWord, tailWord_636742, baseEnd_636742] using wordTrace_append hprefix tailTrace_636742
  have hstable : (prefixWord ++ tailWord_636742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636742).length < 2 ^ (prefixWord ++ tailWord_636742).sum := by decide
  have hdescent : baseEnd_636742 < baseStart_636742 := by decide
  rcases family_descends (prefixWord ++ tailWord_636742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636756 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_636756 : Nat := 118140960795 + 636756 * 2 ^ 59
def prefixEnd_636756 : Nat := 4983230072969 + 3 ^ 40 * 636756 * 2
def baseEnd_636756 : Nat := 290632789008369709263661

theorem tailTrace_636756 : CollatzResearch.WordTrace tailWord_636756 prefixEnd_636756 290632789008369709263661 := by
  unfold tailWord_636756
  simp only [CollatzResearch.WordTrace]
  refine ⟨11612199640574618055969061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15482932854099490741292081 11612199640574618055969061)
  ·
    refine ⟨2177287432607740885494199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11612199640574618055969061 2177287432607740885494199)
    ·
      refine ⟨3265931148911611328241299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2177287432607740885494199 3265931148911611328241299)
      ·
        refine ⟨4898896723367416992361949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265931148911611328241299 4898896723367416992361949)
        ·
          refine ⟨1837086271262781372135731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4898896723367416992361949 1837086271262781372135731)
          ·
            refine ⟨2755629406894172058203597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837086271262781372135731 2755629406894172058203597)
            ·
              refine ⟨1033361027585314521826349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2755629406894172058203597 1033361027585314521826349)
              ·
                refine ⟨387510385344492945684881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033361027585314521826349 387510385344492945684881)
                ·
                  refine ⟨290632789008369709263661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387510385344492945684881 290632789008369709263661)
                  ·
                    rfl

theorem cell20_636756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_636756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636756 prefixEnd_636756 := by exact prefixLift 636756
  have htrace : WordTrace (prefixWord ++ tailWord_636756) baseStart_636756 baseEnd_636756 := by
    simpa [prefixWord, tailWord_636756, baseEnd_636756] using wordTrace_append hprefix tailTrace_636756
  have hstable : (prefixWord ++ tailWord_636756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636756).length < 2 ^ (prefixWord ++ tailWord_636756).sum := by decide
  have hdescent : baseEnd_636756 < baseStart_636756 := by decide
  rcases family_descends (prefixWord ++ tailWord_636756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636767 : List Nat := [1, 1, 2, 3, 1, 6, 6]
def baseStart_636767 : Nat := 118140960795 + 636767 * 2 ^ 59
def prefixEnd_636767 : Nat := 4983230072969 + 3 ^ 40 * 636767 * 2
def baseEnd_636767 : Nat := 32293089967566951099661

theorem tailTrace_636767 : CollatzResearch.WordTrace tailWord_636767 prefixEnd_636767 32293089967566951099661 := by
  unfold tailWord_636767
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224800484109384990588555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15483200322739589993725703 23224800484109384990588555)
  ·
    refine ⟨34837200726164077485882833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23224800484109384990588555 34837200726164077485882833)
    ·
      refine ⟨26127900544623058114412125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34837200726164077485882833 26127900544623058114412125)
      ·
        refine ⟨9797962704233646792904547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26127900544623058114412125 9797962704233646792904547)
        ·
          refine ⟨14696944056350470189356821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797962704233646792904547 14696944056350470189356821)
          ·
            refine ⟨688919252641428290126101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14696944056350470189356821 688919252641428290126101)
            ·
              refine ⟨32293089967566951099661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 688919252641428290126101 32293089967566951099661)
              ·
                rfl

theorem cell20_636767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_636767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636767 prefixEnd_636767 := by exact prefixLift 636767
  have htrace : WordTrace (prefixWord ++ tailWord_636767) baseStart_636767 baseEnd_636767 := by
    simpa [prefixWord, tailWord_636767, baseEnd_636767] using wordTrace_append hprefix tailTrace_636767
  have hstable : (prefixWord ++ tailWord_636767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636767).length < 2 ^ (prefixWord ++ tailWord_636767).sum := by decide
  have hdescent : baseEnd_636767 < baseStart_636767 := by decide
  rcases family_descends (prefixWord ++ tailWord_636767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636829 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_636829 : Nat := 118140960795 + 636829 * 2 ^ 59
def prefixEnd_636829 : Nat := 4983230072969 + 3 ^ 40 * 636829 * 2
def baseEnd_636829 : Nat := 290666108197505899830029

theorem tailTrace_636829 : CollatzResearch.WordTrace tailWord_636829 prefixEnd_636829 290666108197505899830029 := by
  unfold tailWord_636829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227061809884769579345541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15484707873256513052897027 23227061809884769579345541)
  ·
    refine ⟨4355074089353394296127289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23227061809884769579345541 4355074089353394296127289)
    ·
      refine ⟨3266305567015045722095467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355074089353394296127289 3266305567015045722095467)
      ·
        refine ⟨4899458350522568583143201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266305567015045722095467 4899458350522568583143201)
        ·
          refine ⟨3674593762891926437357401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899458350522568583143201 3674593762891926437357401)
          ·
            refine ⟨2755945322168944828018051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3674593762891926437357401 2755945322168944828018051)
            ·
              refine ⟨4133917983253417242027077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755945322168944828018051 4133917983253417242027077)
              ·
                refine ⟨775109621860015732880077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4133917983253417242027077 775109621860015732880077)
                ·
                  refine ⟨290666108197505899830029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775109621860015732880077 290666108197505899830029)
                  ·
                    rfl

theorem cell20_636829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_636829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636829 prefixEnd_636829 := by exact prefixLift 636829
  have htrace : WordTrace (prefixWord ++ tailWord_636829) baseStart_636829 baseEnd_636829 := by
    simpa [prefixWord, tailWord_636829, baseEnd_636829] using wordTrace_append hprefix tailTrace_636829
  have hstable : (prefixWord ++ tailWord_636829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636829).length < 2 ^ (prefixWord ++ tailWord_636829).sum := by decide
  have hdescent : baseEnd_636829 < baseStart_636829 := by decide
  rcases family_descends (prefixWord ++ tailWord_636829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636888 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_636888 : Nat := 118140960795 + 636888 * 2 ^ 59
def prefixEnd_636888 : Nat := 4983230072969 + 3 ^ 40 * 636888 * 2
def baseEnd_636888 : Nat := 290693037405163916863121

theorem tailTrace_636888 : CollatzResearch.WordTrace tailWord_636888 prefixEnd_636888 290693037405163916863121 := by
  unfold tailWord_636888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614606858335511327871659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15486142477780681770495545 11614606858335511327871659)
  ·
    refine ⟨17421910287503266991807489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11614606858335511327871659 17421910287503266991807489)
    ·
      refine ⟨13066432715627450243855617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17421910287503266991807489 13066432715627450243855617)
      ·
        refine ⟨9799824536720587682891713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13066432715627450243855617 9799824536720587682891713)
        ·
          refine ⟨7349868402540440762168785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9799824536720587682891713 7349868402540440762168785)
          ·
            refine ⟨5512401301905330571626589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7349868402540440762168785 5512401301905330571626589)
            ·
              refine ⟨2067150488214498964359971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512401301905330571626589 2067150488214498964359971)
              ·
                refine ⟨3100725732321748446539957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067150488214498964359971 3100725732321748446539957)
                ·
                  refine ⟨290693037405163916863121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100725732321748446539957 290693037405163916863121)
                  ·
                    rfl

theorem cell20_636888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_636888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636888 prefixEnd_636888 := by exact prefixLift 636888
  have htrace : WordTrace (prefixWord ++ tailWord_636888) baseStart_636888 baseEnd_636888 := by
    simpa [prefixWord, tailWord_636888, baseEnd_636888] using wordTrace_append hprefix tailTrace_636888
  have hstable : (prefixWord ++ tailWord_636888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636888).length < 2 ^ (prefixWord ++ tailWord_636888).sum := by decide
  have hdescent : baseEnd_636888 < baseStart_636888 := by decide
  rcases family_descends (prefixWord ++ tailWord_636888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636957 : List Nat := [1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_636957 : Nat := 118140960795 + 636957 * 2 ^ 59
def prefixEnd_636957 : Nat := 4983230072969 + 3 ^ 40 * 636957 * 2
def baseEnd_636957 : Nat := 96908176961768781187613

theorem tailTrace_636957 : CollatzResearch.WordTrace tailWord_636957 prefixEnd_636957 96908176961768781187613 := by
  unfold tailWord_636957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23231730353421047440005125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15487820235614031626670083 23231730353421047440005125)
  ·
    refine ⟨4355949441266446395000961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23231730353421047440005125 4355949441266446395000961)
    ·
      refine ⟨3266962080949834796250721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355949441266446395000961 3266962080949834796250721)
      ·
        refine ⟨2450221560712376097188041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3266962080949834796250721 2450221560712376097188041)
        ·
          refine ⟨1837666170534282072891031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450221560712376097188041 1837666170534282072891031)
          ·
            refine ⟨2756499255801423109336547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837666170534282072891031 2756499255801423109336547)
            ·
              refine ⟨4134748883702134664004821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756499255801423109336547 4134748883702134664004821)
              ·
                refine ⟨96908176961768781187613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4134748883702134664004821 96908176961768781187613)
                ·
                  rfl

theorem cell20_636957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_636957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_636957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_636957 prefixEnd_636957 := by exact prefixLift 636957
  have htrace : WordTrace (prefixWord ++ tailWord_636957) baseStart_636957 baseEnd_636957 := by
    simpa [prefixWord, tailWord_636957, baseEnd_636957] using wordTrace_append hprefix tailTrace_636957
  have hstable : (prefixWord ++ tailWord_636957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636957).length < 2 ^ (prefixWord ++ tailWord_636957).sum := by decide
  have hdescent : baseEnd_636957 < baseStart_636957 := by decide
  rcases family_descends (prefixWord ++ tailWord_636957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637009 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_637009 : Nat := 118140960795 + 637009 * 2 ^ 59
def prefixEnd_637009 : Nat := 4983230072969 + 3 ^ 40 * 637009 * 2
def baseEnd_637009 : Nat := 290748265102225273829293

theorem tailTrace_637009 : CollatzResearch.WordTrace tailWord_637009 prefixEnd_637009 290748265102225273829293 := by
  unfold tailWord_637009
  simp only [CollatzResearch.WordTrace]
  refine ⟨23233626949232660320898081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15489084632821773547265387 23233626949232660320898081)
  ·
    refine ⟨17425220211924495240673561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23233626949232660320898081 17425220211924495240673561)
    ·
      refine ⟨13068915158943371430505171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17425220211924495240673561 13068915158943371430505171)
      ·
        refine ⟨19603372738415057145757757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13068915158943371430505171 19603372738415057145757757)
        ·
          refine ⟨7351264776905646429659159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19603372738415057145757757 7351264776905646429659159)
          ·
            refine ⟨11026897165358469644488739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351264776905646429659159 11026897165358469644488739)
            ·
              refine ⟨16540345748037704466733109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11026897165358469644488739 16540345748037704466733109)
              ·
                refine ⟨1550657413878534793756229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16540345748037704466733109 1550657413878534793756229)
                ·
                  refine ⟨290748265102225273829293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550657413878534793756229 290748265102225273829293)
                  ·
                    rfl

theorem cell20_637009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_637009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637009 prefixEnd_637009 := by exact prefixLift 637009
  have htrace : WordTrace (prefixWord ++ tailWord_637009) baseStart_637009 baseEnd_637009 := by
    simpa [prefixWord, tailWord_637009, baseEnd_637009] using wordTrace_append hprefix tailTrace_637009
  have hstable : (prefixWord ++ tailWord_637009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637009).length < 2 ^ (prefixWord ++ tailWord_637009).sum := by decide
  have hdescent : baseEnd_637009 < baseStart_637009 := by decide
  rcases family_descends (prefixWord ++ tailWord_637009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637033 : List Nat := [1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_637033 : Nat := 118140960795 + 637033 * 2 ^ 59
def prefixEnd_637033 : Nat := 4983230072969 + 3 ^ 40 * 637033 * 2
def baseEnd_637033 : Nat := 96919739785395952343065

theorem tailTrace_637033 : CollatzResearch.WordTrace tailWord_637033 prefixEnd_637033 96919739785395952343065 := by
  unfold tailWord_637033
  simp only [CollatzResearch.WordTrace]
  refine ⟨23234502301145712419771753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15489668200763808279847835 23234502301145712419771753)
  ·
    refine ⟨17425876725859284314828815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23234502301145712419771753 17425876725859284314828815)
    ·
      refine ⟨26138815088788926472243223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17425876725859284314828815 26138815088788926472243223)
      ·
        refine ⟨39208222633183389708364835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26138815088788926472243223 39208222633183389708364835)
        ·
          refine ⟨58812333949775084562547253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39208222633183389708364835 58812333949775084562547253)
          ·
            refine ⟨5513656307791414177738805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58812333949775084562547253 5513656307791414177738805)
            ·
              refine ⟨516905278855445079163013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5513656307791414177738805 516905278855445079163013)
              ·
                refine ⟨96919739785395952343065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516905278855445079163013 96919739785395952343065)
                ·
                  rfl

theorem cell20_637033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_637033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637033 prefixEnd_637033 := by exact prefixLift 637033
  have htrace : WordTrace (prefixWord ++ tailWord_637033) baseStart_637033 baseEnd_637033 := by
    simpa [prefixWord, tailWord_637033, baseEnd_637033] using wordTrace_append hprefix tailTrace_637033
  have hstable : (prefixWord ++ tailWord_637033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637033).length < 2 ^ (prefixWord ++ tailWord_637033).sum := by decide
  have hdescent : baseEnd_637033 < baseStart_637033 := by decide
  rcases family_descends (prefixWord ++ tailWord_637033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637057 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_637057 : Nat := 118140960795 + 637057 * 2 ^ 59
def prefixEnd_637057 : Nat := 4983230072969 + 3 ^ 40 * 637057 * 2
def baseEnd_637057 : Nat := 290770173610150440229097

theorem tailTrace_637057 : CollatzResearch.WordTrace tailWord_637057 prefixEnd_637057 290770173610150440229097 := by
  unfold tailWord_637057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23235377653058764518645425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15490251768705843012430283 23235377653058764518645425)
  ·
    refine ⟨17426533239794073388984069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23235377653058764518645425 17426533239794073388984069)
    ·
      refine ⟨3267474982461388760434513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17426533239794073388984069 3267474982461388760434513)
      ·
        refine ⟨2450606236846041570325885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267474982461388760434513 2450606236846041570325885)
        ·
          refine ⟨918977338817265588872207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2450606236846041570325885 918977338817265588872207)
          ·
            refine ⟨1378466008225898383308311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918977338817265588872207 1378466008225898383308311)
            ·
              refine ⟨2067699012338847574962467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378466008225898383308311 2067699012338847574962467)
              ·
                refine ⟨3101548518508271362443701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067699012338847574962467 3101548518508271362443701)
                ·
                  refine ⟨290770173610150440229097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3101548518508271362443701 290770173610150440229097)
                  ·
                    rfl

theorem cell20_637057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_637057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637057 prefixEnd_637057 := by exact prefixLift 637057
  have htrace : WordTrace (prefixWord ++ tailWord_637057) baseStart_637057 baseEnd_637057 := by
    simpa [prefixWord, tailWord_637057, baseEnd_637057] using wordTrace_append hprefix tailTrace_637057
  have hstable : (prefixWord ++ tailWord_637057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637057).length < 2 ^ (prefixWord ++ tailWord_637057).sum := by decide
  have hdescent : baseEnd_637057 < baseStart_637057 := by decide
  rcases family_descends (prefixWord ++ tailWord_637057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637064 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_637064 : Nat := 118140960795 + 637064 * 2 ^ 59
def prefixEnd_637064 : Nat := 4983230072969 + 3 ^ 40 * 637064 * 2
def baseEnd_637064 : Nat := 290773368600889526995735

theorem tailTrace_637064 : CollatzResearch.WordTrace tailWord_637064 prefixEnd_637064 290773368600889526995735 := by
  unfold tailWord_637064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617816482016702357075123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15490421976022269809433497 11617816482016702357075123)
  ·
    refine ⟨17426724723025053535612685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11617816482016702357075123 17426724723025053535612685)
    ·
      refine ⟨6535021771134395075854757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17426724723025053535612685 6535021771134395075854757)
      ·
        refine ⟨1225316582087699076722767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6535021771134395075854757 1225316582087699076722767)
        ·
          refine ⟨1837974873131548615084151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225316582087699076722767 1837974873131548615084151)
          ·
            refine ⟨2756962309697322922626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837974873131548615084151 2756962309697322922626227)
            ·
              refine ⟨4135443464545984383939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756962309697322922626227 4135443464545984383939341)
              ·
                refine ⟨1550791299204744143977253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135443464545984383939341 1550791299204744143977253)
                ·
                  refine ⟨290773368600889526995735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550791299204744143977253 290773368600889526995735)
                  ·
                    rfl

theorem cell20_637064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_637064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637064 prefixEnd_637064 := by exact prefixLift 637064
  have htrace : WordTrace (prefixWord ++ tailWord_637064) baseStart_637064 baseEnd_637064 := by
    simpa [prefixWord, tailWord_637064, baseEnd_637064] using wordTrace_append hprefix tailTrace_637064
  have hstable : (prefixWord ++ tailWord_637064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637064).length < 2 ^ (prefixWord ++ tailWord_637064).sum := by decide
  have hdescent : baseEnd_637064 < baseStart_637064 := by decide
  rcases family_descends (prefixWord ++ tailWord_637064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637074 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_637074 : Nat := 118140960795 + 637074 * 2 ^ 59
def prefixEnd_637074 : Nat := 4983230072969 + 3 ^ 40 * 637074 * 2
def baseEnd_637074 : Nat := 290777932873373936662361

theorem tailTrace_637074 : CollatzResearch.WordTrace tailWord_637074 prefixEnd_637074 290777932873373936662361 := by
  unfold tailWord_637074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808999423499294105503569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15490665129331450948009517 5808999423499294105503569)
  ·
    refine ⟨4356749567624470579127677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808999423499294105503569 4356749567624470579127677)
    ·
      refine ⟨1633781087859176467172879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4356749567624470579127677 1633781087859176467172879)
      ·
        refine ⟨2450671631788764700759319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633781087859176467172879 2450671631788764700759319)
        ·
          refine ⟨3676007447683147051138979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450671631788764700759319 3676007447683147051138979)
          ·
            refine ⟨5514011171524720576708469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676007447683147051138979 5514011171524720576708469)
            ·
              refine ⟨516938547330442554066419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5514011171524720576708469 516938547330442554066419)
              ·
                refine ⟨775407820995663831099629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516938547330442554066419 775407820995663831099629)
                ·
                  refine ⟨290777932873373936662361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775407820995663831099629 290777932873373936662361)
                  ·
                    rfl

theorem cell20_637074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_637074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637074 prefixEnd_637074 := by exact prefixLift 637074
  have htrace : WordTrace (prefixWord ++ tailWord_637074) baseStart_637074 baseEnd_637074 := by
    simpa [prefixWord, tailWord_637074, baseEnd_637074] using wordTrace_append hprefix tailTrace_637074
  have hstable : (prefixWord ++ tailWord_637074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637074).length < 2 ^ (prefixWord ++ tailWord_637074).sum := by decide
  have hdescent : baseEnd_637074 < baseStart_637074 := by decide
  rcases family_descends (prefixWord ++ tailWord_637074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637088 : List Nat := [2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_637088 : Nat := 118140960795 + 637088 * 2 ^ 59
def prefixEnd_637088 : Nat := 4983230072969 + 3 ^ 40 * 637088 * 2
def baseEnd_637088 : Nat := 96928107618284036731879

theorem tailTrace_637088 : CollatzResearch.WordTrace tailWord_637088 prefixEnd_637088 96928107618284036731879 := by
  unfold tailWord_637088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618254157973228406511959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15491005543964304542015945 11618254157973228406511959)
  ·
    refine ⟨17427381236959842609767939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11618254157973228406511959 17427381236959842609767939)
    ·
      refine ⟨26141071855439763914651909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17427381236959842609767939 26141071855439763914651909)
      ·
        refine ⟨4901450972894955733997233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26141071855439763914651909 4901450972894955733997233)
        ·
          refine ⟨3676088229671216800497925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4901450972894955733997233 3676088229671216800497925)
          ·
            refine ⟨689266543063353150093361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3676088229671216800497925 689266543063353150093361)
            ·
              refine ⟨516949907297514862570021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689266543063353150093361 516949907297514862570021)
              ·
                refine ⟨96928107618284036731879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516949907297514862570021 96928107618284036731879)
                ·
                  rfl

theorem cell20_637088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_637088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637088 prefixEnd_637088 := by exact prefixLift 637088
  have htrace : WordTrace (prefixWord ++ tailWord_637088) baseStart_637088 baseEnd_637088 := by
    simpa [prefixWord, tailWord_637088, baseEnd_637088] using wordTrace_append hprefix tailTrace_637088
  have hstable : (prefixWord ++ tailWord_637088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637088).length < 2 ^ (prefixWord ++ tailWord_637088).sum := by decide
  have hdescent : baseEnd_637088 < baseStart_637088 := by decide
  rcases family_descends (prefixWord ++ tailWord_637088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637174 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_637174 : Nat := 118140960795 + 637174 * 2 ^ 59
def prefixEnd_637174 : Nat := 4983230072969 + 3 ^ 40 * 637174 * 2
def baseEnd_637174 : Nat := 290823575598218033328619

theorem tailTrace_637174 : CollatzResearch.WordTrace tailWord_637174 prefixEnd_637174 290823575598218033328619 := by
  unfold tailWord_637174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452477812102180843790911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15493096662423262333769717 1452477812102180843790911)
  ·
    refine ⟨2178716718153271265686367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1452477812102180843790911 2178716718153271265686367)
    ·
      refine ⟨3268075077229906898529551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178716718153271265686367 3268075077229906898529551)
      ·
        refine ⟨4902112615844860347794327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268075077229906898529551 4902112615844860347794327)
        ·
          refine ⟨7353168923767290521691491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902112615844860347794327 7353168923767290521691491)
          ·
            refine ⟨11029753385650935782537237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353168923767290521691491 11029753385650935782537237)
            ·
              refine ⟨517019689952387614806433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11029753385650935782537237 517019689952387614806433)
              ·
                refine ⟨387764767464290711104825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517019689952387614806433 387764767464290711104825)
                ·
                  refine ⟨290823575598218033328619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387764767464290711104825 290823575598218033328619)
                  ·
                    rfl

theorem cell20_637174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_637174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637174 prefixEnd_637174 := by exact prefixLift 637174
  have htrace : WordTrace (prefixWord ++ tailWord_637174) baseStart_637174 baseEnd_637174 := by
    simpa [prefixWord, tailWord_637174, baseEnd_637174] using wordTrace_append hprefix tailTrace_637174
  have hstable : (prefixWord ++ tailWord_637174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637174).length < 2 ^ (prefixWord ++ tailWord_637174).sum := by decide
  have hdescent : baseEnd_637174 < baseStart_637174 := by decide
  rcases family_descends (prefixWord ++ tailWord_637174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637244 : List Nat := [2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_637244 : Nat := 118140960795 + 637244 * 2 ^ 59
def prefixEnd_637244 : Nat := 4983230072969 + 3 ^ 40 * 637244 * 2
def baseEnd_637244 : Nat := 96951841835202966998333

theorem tailTrace_637244 : CollatzResearch.WordTrace tailWord_637244 prefixEnd_637244 96951841835202966998333 := by
  unfold tailWord_637244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621099051690647727851393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15494798735587530303801857 11621099051690647727851393)
  ·
    refine ⟨8715824288767985795888545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11621099051690647727851393 8715824288767985795888545)
    ·
      refine ⟨6536868216575989346916409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8715824288767985795888545 6536868216575989346916409)
      ·
        refine ⟨4902651162431992010187307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6536868216575989346916409 4902651162431992010187307)
        ·
          refine ⟨7353976743647988015280961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902651162431992010187307 7353976743647988015280961)
          ·
            refine ⟨5515482557735991011460721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7353976743647988015280961 5515482557735991011460721)
            ·
              refine ⟨4136611918301993258595541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5515482557735991011460721 4136611918301993258595541)
              ·
                refine ⟨96951841835202966998333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4136611918301993258595541 96951841835202966998333)
                ·
                  rfl

theorem cell20_637244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_637244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637244 prefixEnd_637244 := by exact prefixLift 637244
  have htrace : WordTrace (prefixWord ++ tailWord_637244) baseStart_637244 baseEnd_637244 := by
    simpa [prefixWord, tailWord_637244, baseEnd_637244] using wordTrace_append hprefix tailTrace_637244
  have hstable : (prefixWord ++ tailWord_637244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637244).length < 2 ^ (prefixWord ++ tailWord_637244).sum := by decide
  have hdescent : baseEnd_637244 < baseStart_637244 := by decide
  rcases family_descends (prefixWord ++ tailWord_637244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637247 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_637247 : Nat := 118140960795 + 637247 * 2 ^ 59
def prefixEnd_637247 : Nat := 4983230072969 + 3 ^ 40 * 637247 * 2
def baseEnd_637247 : Nat := 290856894787354223894987

theorem tailTrace_637247 : CollatzResearch.WordTrace tailWord_637247 prefixEnd_637247 290856894787354223894987 := by
  unfold tailWord_637247
  simp only [CollatzResearch.WordTrace]
  refine ⟨23242307522370426968061995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15494871681580284645374663 23242307522370426968061995)
  ·
    refine ⟨34863461283555640452092993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23242307522370426968061995 34863461283555640452092993)
    ·
      refine ⟨26147595962666730339069745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34863461283555640452092993 26147595962666730339069745)
      ·
        refine ⟨19610696972000047754302309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26147595962666730339069745 19610696972000047754302309)
        ·
          refine ⟨3677005682250008953931683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19610696972000047754302309 3677005682250008953931683)
          ·
            refine ⟨5515508523375013430897525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677005682250008953931683 5515508523375013430897525)
            ·
              refine ⟨517078924066407509146643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5515508523375013430897525 517078924066407509146643)
              ·
                refine ⟨775618386099611263719965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517078924066407509146643 775618386099611263719965)
                ·
                  refine ⟨290856894787354223894987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775618386099611263719965 290856894787354223894987)
                  ·
                    rfl

theorem cell20_637247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_637247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637247 prefixEnd_637247 := by exact prefixLift 637247
  have htrace : WordTrace (prefixWord ++ tailWord_637247) baseStart_637247 baseEnd_637247 := by
    simpa [prefixWord, tailWord_637247, baseEnd_637247] using wordTrace_append hprefix tailTrace_637247
  have hstable : (prefixWord ++ tailWord_637247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637247).length < 2 ^ (prefixWord ++ tailWord_637247).sum := by decide
  have hdescent : baseEnd_637247 < baseStart_637247 := by decide
  rcases family_descends (prefixWord ++ tailWord_637247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637268 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_637268 : Nat := 118140960795 + 637268 * 2 ^ 59
def prefixEnd_637268 : Nat := 4983230072969 + 3 ^ 40 * 637268 * 2
def baseEnd_637268 : Nat := 290866479759571484194901

theorem tailTrace_637268 : CollatzResearch.WordTrace tailWord_637268 prefixEnd_637268 290866479759571484194901 := by
  unfold tailWord_637268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621536727647173777288229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15495382303529565036384305 11621536727647173777288229)
  ·
    refine ⟨2179038136433845083241543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11621536727647173777288229 2179038136433845083241543)
    ·
      refine ⟨3268557204650767624862315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179038136433845083241543 3268557204650767624862315)
      ·
        refine ⟨4902835806976151437293473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268557204650767624862315 4902835806976151437293473)
        ·
          refine ⟨3677126855232113577970105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4902835806976151437293473 3677126855232113577970105)
          ·
            refine ⟨2757845141424085183477579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677126855232113577970105 2757845141424085183477579)
            ·
              refine ⟨4136767712136127775216369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757845141424085183477579 4136767712136127775216369)
              ·
                refine ⟨3102575784102095831412277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136767712136127775216369 3102575784102095831412277)
                ·
                  refine ⟨290866479759571484194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102575784102095831412277 290866479759571484194901)
                  ·
                    rfl

theorem cell20_637268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_637268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637268 prefixEnd_637268 := by exact prefixLift 637268
  have htrace : WordTrace (prefixWord ++ tailWord_637268) baseStart_637268 baseEnd_637268 := by
    simpa [prefixWord, tailWord_637268, baseEnd_637268] using wordTrace_append hprefix tailTrace_637268
  have hstable : (prefixWord ++ tailWord_637268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637268).length < 2 ^ (prefixWord ++ tailWord_637268).sum := by decide
  have hdescent : baseEnd_637268 < baseStart_637268 := by decide
  rcases family_descends (prefixWord ++ tailWord_637268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637288 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_637288 : Nat := 118140960795 + 637288 * 2 ^ 59
def prefixEnd_637288 : Nat := 4983230072969 + 3 ^ 40 * 637288 * 2
def baseEnd_637288 : Nat := 290875608304540303528153

theorem tailTrace_637288 : CollatzResearch.WordTrace tailWord_637288 prefixEnd_637288 290875608304540303528153 := by
  unfold tailWord_637288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621901457610945485152259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15495868610147927313536345 11621901457610945485152259)
  ·
    refine ⟨17432852186416418227728389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11621901457610945485152259 17432852186416418227728389)
    ·
      refine ⟨3268659784953078417699073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17432852186416418227728389 3268659784953078417699073)
      ·
        refine ⟨2451494838714808813274305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3268659784953078417699073 2451494838714808813274305)
        ·
          refine ⟨1838621129036106609955729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451494838714808813274305 1838621129036106609955729)
          ·
            refine ⟨1378965846777079957466797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838621129036106609955729 1378965846777079957466797)
            ·
              refine ⟨517112192541404984050049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1378965846777079957466797 517112192541404984050049)
              ·
                refine ⟨387834144406053738037537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517112192541404984050049 387834144406053738037537)
                ·
                  refine ⟨290875608304540303528153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387834144406053738037537 290875608304540303528153)
                  ·
                    rfl

theorem cell20_637288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_637288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637288 prefixEnd_637288 := by exact prefixLift 637288
  have htrace : WordTrace (prefixWord ++ tailWord_637288) baseStart_637288 baseEnd_637288 := by
    simpa [prefixWord, tailWord_637288, baseEnd_637288] using wordTrace_append hprefix tailTrace_637288
  have hstable : (prefixWord ++ tailWord_637288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637288).length < 2 ^ (prefixWord ++ tailWord_637288).sum := by decide
  have hdescent : baseEnd_637288 < baseStart_637288 := by decide
  rcases family_descends (prefixWord ++ tailWord_637288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637289 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_637289 : Nat := 118140960795 + 637289 * 2 ^ 59
def prefixEnd_637289 : Nat := 4983230072969 + 3 ^ 40 * 637289 * 2
def baseEnd_637289 : Nat := 290876064731788744494815

theorem tailTrace_637289 : CollatzResearch.WordTrace tailWord_637289 prefixEnd_637289 290876064731788744494815 := by
  unfold tailWord_637289
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243839388218268141090921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15495892925478845427393947 23243839388218268141090921)
  ·
    refine ⟨17432879541163701105818191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23243839388218268141090921 17432879541163701105818191)
    ·
      refine ⟨26149319311745551658727287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17432879541163701105818191 26149319311745551658727287)
      ·
        refine ⟨39223978967618327488090931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26149319311745551658727287 39223978967618327488090931)
        ·
          refine ⟨58835968451427491232136397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39223978967618327488090931 58835968451427491232136397)
          ·
            refine ⟨22063488169285309212051149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58835968451427491232136397 22063488169285309212051149)
            ·
              refine ⟨8273808063481990954519181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22063488169285309212051149 8273808063481990954519181)
              ·
                refine ⟨3102678023805746607944693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8273808063481990954519181 3102678023805746607944693)
                ·
                  refine ⟨290876064731788744494815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102678023805746607944693 290876064731788744494815)
                  ·
                    rfl

theorem cell20_637289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_637289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637289 prefixEnd_637289 := by exact prefixLift 637289
  have htrace : WordTrace (prefixWord ++ tailWord_637289) baseStart_637289 baseEnd_637289 := by
    simpa [prefixWord, tailWord_637289, baseEnd_637289] using wordTrace_append hprefix tailTrace_637289
  have hstable : (prefixWord ++ tailWord_637289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637289).length < 2 ^ (prefixWord ++ tailWord_637289).sum := by decide
  have hdescent : baseEnd_637289 < baseStart_637289 := by decide
  rcases family_descends (prefixWord ++ tailWord_637289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637320 : List Nat := [2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_637320 : Nat := 118140960795 + 637320 * 2 ^ 59
def prefixEnd_637320 : Nat := 4983230072969 + 3 ^ 40 * 637320 * 2
def baseEnd_637320 : Nat := 96963404658830138153785

theorem tailTrace_637320 : CollatzResearch.WordTrace tailWord_637320 prefixEnd_637320 96963404658830138153785 := by
  unfold tailWord_637320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622485025552980217734707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15496646700737306956979609 11622485025552980217734707)
  ·
    refine ⟨17433727538329470326602061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11622485025552980217734707 17433727538329470326602061)
    ·
      refine ⟨6537647826873551372475773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17433727538329470326602061 6537647826873551372475773)
      ·
        refine ⟨2451617935077581764678415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6537647826873551372475773 2451617935077581764678415)
        ·
          refine ⟨3677426902616372647017623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451617935077581764678415 3677426902616372647017623)
          ·
            refine ⟨5516140353924558970526435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677426902616372647017623 5516140353924558970526435)
            ·
              refine ⟨8274210530886838455789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516140353924558970526435 8274210530886838455789653)
              ·
                refine ⟨96963404658830138153785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8274210530886838455789653 96963404658830138153785)
                ·
                  rfl

theorem cell20_637320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_637320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637320 prefixEnd_637320 := by exact prefixLift 637320
  have htrace : WordTrace (prefixWord ++ tailWord_637320) baseStart_637320 baseEnd_637320 := by
    simpa [prefixWord, tailWord_637320, baseEnd_637320] using wordTrace_append hprefix tailTrace_637320
  have hstable : (prefixWord ++ tailWord_637320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637320).length < 2 ^ (prefixWord ++ tailWord_637320).sum := by decide
  have hdescent : baseEnd_637320 < baseStart_637320 := by decide
  rcases family_descends (prefixWord ++ tailWord_637320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637344 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_637344 : Nat := 118140960795 + 637344 * 2 ^ 59
def prefixEnd_637344 : Nat := 4983230072969 + 3 ^ 40 * 637344 * 2
def baseEnd_637344 : Nat := 290901168230452997661257

theorem tailTrace_637344 : CollatzResearch.WordTrace tailWord_637344 prefixEnd_637344 290901168230452997661257 := by
  unfold tailWord_637344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622922701509506267171543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15497230268679341689562057 11622922701509506267171543)
  ·
    refine ⟨17434384052264259400757315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11622922701509506267171543 17434384052264259400757315)
    ·
      refine ⟨26151576078396389101135973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434384052264259400757315 26151576078396389101135973)
      ·
        refine ⟨4903420514699322956462995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26151576078396389101135973 4903420514699322956462995)
        ·
          refine ⟨7355130772048984434694493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903420514699322956462995 7355130772048984434694493)
          ·
            refine ⟨2758174039518369163010435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7355130772048984434694493 2758174039518369163010435)
            ·
              refine ⟨4137261059277553744515653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758174039518369163010435 4137261059277553744515653)
              ·
                refine ⟨775736448614541327096685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4137261059277553744515653 775736448614541327096685)
                ·
                  refine ⟨290901168230452997661257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775736448614541327096685 290901168230452997661257)
                  ·
                    rfl

theorem cell20_637344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_637344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637344 prefixEnd_637344 := by exact prefixLift 637344
  have htrace : WordTrace (prefixWord ++ tailWord_637344) baseStart_637344 baseEnd_637344 := by
    simpa [prefixWord, tailWord_637344, baseEnd_637344] using wordTrace_append hprefix tailTrace_637344
  have hstable : (prefixWord ++ tailWord_637344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637344).length < 2 ^ (prefixWord ++ tailWord_637344).sum := by decide
  have hdescent : baseEnd_637344 < baseStart_637344 := by decide
  rcases family_descends (prefixWord ++ tailWord_637344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637347 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 2]
def baseStart_637347 : Nat := 118140960795 + 637347 * 2 ^ 59
def prefixEnd_637347 : Nat := 4983230072969 + 3 ^ 40 * 637347 * 2
def baseEnd_637347 : Nat := 290902537512198320561245

theorem tailTrace_637347 : CollatzResearch.WordTrace tailWord_637347 prefixEnd_637347 290902537512198320561245 := by
  unfold tailWord_637347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23245954822008144046702295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15497303214672096031134863 23245954822008144046702295)
  ·
    refine ⟨34868932233012216070053443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23245954822008144046702295 34868932233012216070053443)
    ·
      refine ⟨52303398349518324105080165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34868932233012216070053443 52303398349518324105080165)
      ·
        refine ⟨9806887190534685769702531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52303398349518324105080165 9806887190534685769702531)
        ·
          refine ⟨14710330785802028654553797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806887190534685769702531 14710330785802028654553797)
          ·
            refine ⟨2758187022337880372728837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14710330785802028654553797 2758187022337880372728837)
            ·
              refine ⟨517160066688352569886657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2758187022337880372728837 517160066688352569886657)
              ·
                refine ⟨387870050016264427414993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517160066688352569886657 387870050016264427414993)
                ·
                  refine ⟨290902537512198320561245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387870050016264427414993 290902537512198320561245)
                  ·
                    rfl

theorem cell20_637347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2].length) (baseStart_637347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637347 prefixEnd_637347 := by exact prefixLift 637347
  have htrace : WordTrace (prefixWord ++ tailWord_637347) baseStart_637347 baseEnd_637347 := by
    simpa [prefixWord, tailWord_637347, baseEnd_637347] using wordTrace_append hprefix tailTrace_637347
  have hstable : (prefixWord ++ tailWord_637347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637347).length < 2 ^ (prefixWord ++ tailWord_637347).sum := by decide
  have hdescent : baseEnd_637347 < baseStart_637347 := by decide
  rcases family_descends (prefixWord ++ tailWord_637347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637364 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_637364 : Nat := 118140960795 + 637364 * 2 ^ 59
def prefixEnd_637364 : Nat := 4983230072969 + 3 ^ 40 * 637364 * 2
def baseEnd_637364 : Nat := 290910296775421816994509

theorem tailTrace_637364 : CollatzResearch.WordTrace tailWord_637364 prefixEnd_637364 290910296775421816994509 := by
  unfold tailWord_637364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623287431473277975035573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15497716575297703966714097 11623287431473277975035573)
  ·
    refine ⟨1089683196700619810159585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11623287431473277975035573 1089683196700619810159585)
    ·
      refine ⟨817262397525464857619689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1089683196700619810159585 817262397525464857619689)
      ·
        refine ⟨612946798144098643214767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 817262397525464857619689 612946798144098643214767)
        ·
          refine ⟨919420197216147964822151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612946798144098643214767 919420197216147964822151)
          ·
            refine ⟨1379130295824221947233227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919420197216147964822151 1379130295824221947233227)
            ·
              refine ⟨2068695443736332920849841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379130295824221947233227 2068695443736332920849841)
              ·
                refine ⟨1551521582802249690637381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068695443736332920849841 1551521582802249690637381)
                ·
                  refine ⟨290910296775421816994509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551521582802249690637381 290910296775421816994509)
                  ·
                    rfl

theorem cell20_637364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_637364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637364 prefixEnd_637364 := by exact prefixLift 637364
  have htrace : WordTrace (prefixWord ++ tailWord_637364) baseStart_637364 baseEnd_637364 := by
    simpa [prefixWord, tailWord_637364, baseEnd_637364] using wordTrace_append hprefix tailTrace_637364
  have hstable : (prefixWord ++ tailWord_637364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637364).length < 2 ^ (prefixWord ++ tailWord_637364).sum := by decide
  have hdescent : baseEnd_637364 < baseStart_637364 := by decide
  rcases family_descends (prefixWord ++ tailWord_637364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637461 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 2]
def baseStart_637461 : Nat := 118140960795 + 637461 * 2 ^ 59
def prefixEnd_637461 : Nat := 4983230072969 + 3 ^ 40 * 637461 * 2
def baseEnd_637461 : Nat := 290954570218520590760779

theorem tailTrace_637461 : CollatzResearch.WordTrace tailWord_637461 prefixEnd_637461 290954570218520590760779 := by
  unfold tailWord_637461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23250112743595141516352237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15500075162396761010901491 23250112743595141516352237)
  ·
    refine ⟨8718792278848178068632089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23250112743595141516352237 8718792278848178068632089)
    ·
      refine ⟨6539094209136133551474067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8718792278848178068632089 6539094209136133551474067)
      ·
        refine ⟨9808641313704200327211101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539094209136133551474067 9808641313704200327211101)
        ·
          refine ⟨3678240492639075122704163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9808641313704200327211101 3678240492639075122704163)
          ·
            refine ⟨5517360738958612684056245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678240492639075122704163 5517360738958612684056245)
            ·
              refine ⟨517252569277369939130273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5517360738958612684056245 517252569277369939130273)
              ·
                refine ⟨387939426958027454347705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517252569277369939130273 387939426958027454347705)
                ·
                  refine ⟨290954570218520590760779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387939426958027454347705 290954570218520590760779)
                  ·
                    rfl

theorem cell20_637461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_637461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637461 prefixEnd_637461 := by exact prefixLift 637461
  have htrace : WordTrace (prefixWord ++ tailWord_637461) baseStart_637461 baseEnd_637461 := by
    simpa [prefixWord, tailWord_637461, baseEnd_637461] using wordTrace_append hprefix tailTrace_637461
  have hstable : (prefixWord ++ tailWord_637461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637461).length < 2 ^ (prefixWord ++ tailWord_637461).sum := by decide
  have hdescent : baseEnd_637461 < baseStart_637461 := by decide
  rcases family_descends (prefixWord ++ tailWord_637461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637475 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_637475 : Nat := 118140960795 + 637475 * 2 ^ 59
def prefixEnd_637475 : Nat := 4983230072969 + 3 ^ 40 * 637475 * 2
def baseEnd_637475 : Nat := 290960960199998764294055

theorem tailTrace_637475 : CollatzResearch.WordTrace tailWord_637475 prefixEnd_637475 290960960199998764294055 := by
  unfold tailWord_637475
  simp only [CollatzResearch.WordTrace]
  refine ⟨23250623365544421907361879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15500415577029614604907919 23250623365544421907361879)
  ·
    refine ⟨34875935048316632861042819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23250623365544421907361879 34875935048316632861042819)
    ·
      refine ⟨52313902572474949291564229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34875935048316632861042819 52313902572474949291564229)
      ·
        refine ⟨9808856732339052992168293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52313902572474949291564229 9808856732339052992168293)
        ·
          refine ⟨1839160637313572436031555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9808856732339052992168293 1839160637313572436031555)
          ·
            refine ⟨2758740955970358654047333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839160637313572436031555 2758740955970358654047333)
            ·
              refine ⟨517263929244442247633875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2758740955970358654047333 517263929244442247633875)
              ·
                refine ⟨775895893866663371450813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517263929244442247633875 775895893866663371450813)
                ·
                  refine ⟨290960960199998764294055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775895893866663371450813 290960960199998764294055)
                  ·
                    rfl

theorem cell20_637475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_637475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637475 prefixEnd_637475 := by exact prefixLift 637475
  have htrace : WordTrace (prefixWord ++ tailWord_637475) baseStart_637475 baseEnd_637475 := by
    simpa [prefixWord, tailWord_637475, baseEnd_637475] using wordTrace_append hprefix tailTrace_637475
  have hstable : (prefixWord ++ tailWord_637475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637475).length < 2 ^ (prefixWord ++ tailWord_637475).sum := by decide
  have hdescent : baseEnd_637475 < baseStart_637475 := by decide
  rcases family_descends (prefixWord ++ tailWord_637475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637544 : List Nat := [2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_637544 : Nat := 118140960795 + 637544 * 2 ^ 59
def prefixEnd_637544 : Nat := 4983230072969 + 3 ^ 40 * 637544 * 2
def baseEnd_637544 : Nat := 96997484560047063664591

theorem tailTrace_637544 : CollatzResearch.WordTrace tailWord_637544 prefixEnd_637544 96997484560047063664591 := by
  unfold tailWord_637544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626570001147223345811843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15502093334862964461082457 11626570001147223345811843)
  ·
    refine ⟨17439855001720835018717765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11626570001147223345811843 17439855001720835018717765)
    ·
      refine ⟨3269972812822656566009581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17439855001720835018717765 3269972812822656566009581)
      ·
        refine ⟨1226239804808496212253593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3269972812822656566009581 1226239804808496212253593)
        ·
          refine ⟨919679853606372159190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226239804808496212253593 919679853606372159190195)
          ·
            refine ⟨1379519780409558238785293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919679853606372159190195 1379519780409558238785293)
            ·
              refine ⟨517319917653584339544485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1379519780409558238785293 517319917653584339544485)
              ·
                refine ⟨96997484560047063664591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517319917653584339544485 96997484560047063664591)
                ·
                  rfl

theorem cell20_637544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_637544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637544 prefixEnd_637544 := by exact prefixLift 637544
  have htrace : WordTrace (prefixWord ++ tailWord_637544) baseStart_637544 baseEnd_637544 := by
    simpa [prefixWord, tailWord_637544, baseEnd_637544] using wordTrace_append hprefix tailTrace_637544
  have hstable : (prefixWord ++ tailWord_637544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637544).length < 2 ^ (prefixWord ++ tailWord_637544).sum := by decide
  have hdescent : baseEnd_637544 < baseStart_637544 := by decide
  rcases family_descends (prefixWord ++ tailWord_637544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637572 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_637572 : Nat := 118140960795 + 637572 * 2 ^ 59
def prefixEnd_637572 : Nat := 4983230072969 + 3 ^ 40 * 637572 * 2
def baseEnd_637572 : Nat := 291005233643097538060325

theorem tailTrace_637572 : CollatzResearch.WordTrace tailWord_637572 prefixEnd_637572 291005233643097538060325 := by
  unfold tailWord_637572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627080623096503736821485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15502774164128671649095313 11627080623096503736821485)
  ·
    refine ⟨4360155233661188901308057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11627080623096503736821485 4360155233661188901308057)
    ·
      refine ⟨3270116425245891675981043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360155233661188901308057 3270116425245891675981043)
      ·
        refine ⟨4905174637868837513971565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270116425245891675981043 4905174637868837513971565)
        ·
          refine ⟨1839440489200814067739337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4905174637868837513971565 1839440489200814067739337)
          ·
            refine ⟨1379580366900610550804503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839440489200814067739337 1379580366900610550804503)
            ·
              refine ⟨2069370550350915826206755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379580366900610550804503 2069370550350915826206755)
              ·
                refine ⟨3104055825526373739310133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069370550350915826206755 3104055825526373739310133)
                ·
                  refine ⟨291005233643097538060325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104055825526373739310133 291005233643097538060325)
                  ·
                    rfl

theorem cell20_637572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_637572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637572 prefixEnd_637572 := by exact prefixLift 637572
  have htrace : WordTrace (prefixWord ++ tailWord_637572) baseStart_637572 baseEnd_637572 := by
    simpa [prefixWord, tailWord_637572, baseEnd_637572] using wordTrace_append hprefix tailTrace_637572
  have hstable : (prefixWord ++ tailWord_637572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637572).length < 2 ^ (prefixWord ++ tailWord_637572).sum := by decide
  have hdescent : baseEnd_637572 < baseStart_637572 := by decide
  rcases family_descends (prefixWord ++ tailWord_637572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637613 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 2]
def baseStart_637613 : Nat := 118140960795 + 637613 * 2 ^ 59
def prefixEnd_637613 : Nat := 4983230072969 + 3 ^ 40 * 637613 * 2
def baseEnd_637613 : Nat := 291023947160283617693491

theorem tailTrace_637613 : CollatzResearch.WordTrace tailWord_637613 prefixEnd_637613 291023947160283617693491 := by
  unfold tailWord_637613
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255656639044471475885493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15503771092696314317256995 23255656639044471475885493)
  ·
    refine ⟨2180217809910419200864265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23255656639044471475885493 2180217809910419200864265)
    ·
      refine ⟨1635163357432814400648199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2180217809910419200864265 1635163357432814400648199)
      ·
        refine ⟨2452745036149221600972299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635163357432814400648199 2452745036149221600972299)
        ·
          refine ⟨3679117554223832401458449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452745036149221600972299 3679117554223832401458449)
          ·
            refine ⟨2759338165667874301093837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3679117554223832401458449 2759338165667874301093837)
            ·
              refine ⟨1034751812125452862910189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2759338165667874301093837 1034751812125452862910189)
              ·
                refine ⟨388031929547044823591321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034751812125452862910189 388031929547044823591321)
                ·
                  refine ⟨291023947160283617693491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388031929547044823591321 291023947160283617693491)
                  ·
                    rfl

theorem cell20_637613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_637613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637613 prefixEnd_637613 := by exact prefixLift 637613
  have htrace : WordTrace (prefixWord ++ tailWord_637613) baseStart_637613 baseEnd_637613 := by
    simpa [prefixWord, tailWord_637613, baseEnd_637613] using wordTrace_append hprefix tailTrace_637613
  have hstable : (prefixWord ++ tailWord_637613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637613).length < 2 ^ (prefixWord ++ tailWord_637613).sum := by decide
  have hdescent : baseEnd_637613 < baseStart_637613 := by decide
  rcases family_descends (prefixWord ++ tailWord_637613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637631 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_637631 : Nat := 118140960795 + 637631 * 2 ^ 59
def prefixEnd_637631 : Nat := 4983230072969 + 3 ^ 40 * 637631 * 2
def baseEnd_637631 : Nat := 291032162850755555093417

theorem tailTrace_637631 : CollatzResearch.WordTrace tailWord_637631 prefixEnd_637631 291032162850755555093417 := by
  unfold tailWord_637631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256313152979260550040747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15504208768652840366693831 23256313152979260550040747)
  ·
    refine ⟨34884469729468890825061121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256313152979260550040747 34884469729468890825061121)
    ·
      refine ⟨26163352297101668118795841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34884469729468890825061121 26163352297101668118795841)
      ·
        refine ⟨19622514222826251089096881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163352297101668118795841 19622514222826251089096881)
        ·
          refine ⟨14716885667119688316822661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19622514222826251089096881 14716885667119688316822661)
          ·
            refine ⟨2759416062584941559404249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14716885667119688316822661 2759416062584941559404249)
            ·
              refine ⟨2069562046938706169553187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2759416062584941559404249 2069562046938706169553187)
              ·
                refine ⟨3104343070408059254329781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069562046938706169553187 3104343070408059254329781)
                ·
                  refine ⟨291032162850755555093417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104343070408059254329781 291032162850755555093417)
                  ·
                    rfl

theorem cell20_637631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_637631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637631 prefixEnd_637631 := by exact prefixLift 637631
  have htrace : WordTrace (prefixWord ++ tailWord_637631) baseStart_637631 baseEnd_637631 := by
    simpa [prefixWord, tailWord_637631, baseEnd_637631] using wordTrace_append hprefix tailTrace_637631
  have hstable : (prefixWord ++ tailWord_637631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637631).length < 2 ^ (prefixWord ++ tailWord_637631).sum := by decide
  have hdescent : baseEnd_637631 < baseStart_637631 := by decide
  rcases family_descends (prefixWord ++ tailWord_637631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637644 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_637644 : Nat := 118140960795 + 637644 * 2 ^ 59
def prefixEnd_637644 : Nat := 4983230072969 + 3 ^ 40 * 637644 * 2
def baseEnd_637644 : Nat := 291038096404985287660031

theorem tailTrace_637644 : CollatzResearch.WordTrace tailWord_637644 prefixEnd_637644 291038096404985287660031 := by
  unfold tailWord_637644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11628393650966081885131993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15504524867954775846842657 11628393650966081885131993)
  ·
    refine ⟨8721295238224561413848995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11628393650966081885131993 8721295238224561413848995)
    ·
      refine ⟨13081942857336842120773493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8721295238224561413848995 13081942857336842120773493)
      ·
        refine ⟨1226432142875328948822515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13081942857336842120773493 1226432142875328948822515)
        ·
          refine ⟨1839648214312993423233773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226432142875328948822515 1839648214312993423233773)
          ·
            refine ⟨689868080367372533712665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1839648214312993423233773 689868080367372533712665)
            ·
              refine ⟨517401060275529400284499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689868080367372533712665 517401060275529400284499)
              ·
                refine ⟨776101590413294100426749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517401060275529400284499 776101590413294100426749)
                ·
                  refine ⟨291038096404985287660031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776101590413294100426749 291038096404985287660031)
                  ·
                    rfl

theorem cell20_637644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_637644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637644 prefixEnd_637644 := by exact prefixLift 637644
  have htrace : WordTrace (prefixWord ++ tailWord_637644) baseStart_637644 baseEnd_637644 := by
    simpa [prefixWord, tailWord_637644, baseEnd_637644] using wordTrace_append hprefix tailTrace_637644
  have hstable : (prefixWord ++ tailWord_637644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637644).length < 2 ^ (prefixWord ++ tailWord_637644).sum := by decide
  have hdescent : baseEnd_637644 < baseStart_637644 := by decide
  rcases family_descends (prefixWord ++ tailWord_637644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637685 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 2]
def baseStart_637685 : Nat := 118140960795 + 637685 * 2 ^ 59
def prefixEnd_637685 : Nat := 4983230072969 + 3 ^ 40 * 637685 * 2
def baseEnd_637685 : Nat := 291056809922171367293197

theorem tailTrace_637685 : CollatzResearch.WordTrace tailWord_637685 prefixEnd_637685 291056809922171367293197 := by
  unfold tailWord_637685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258282694783627772506509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15505521796522418515004339 23258282694783627772506509)
  ·
    refine ⟨8721856010543860414689941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23258282694783627772506509 8721856010543860414689941)
    ·
      refine ⟨408837000494243456938591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8721856010543860414689941 408837000494243456938591)
      ·
        refine ⟨613255500741365185407887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408837000494243456938591 613255500741365185407887)
        ·
          refine ⟨919883251112047778111831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613255500741365185407887 919883251112047778111831)
          ·
            refine ⟨1379824876668071667167747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919883251112047778111831 1379824876668071667167747)
            ·
              refine ⟨2069737315002107500751621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379824876668071667167747 2069737315002107500751621)
              ·
                refine ⟨388075746562895156390929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2069737315002107500751621 388075746562895156390929)
                ·
                  refine ⟨291056809922171367293197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388075746562895156390929 291056809922171367293197)
                  ·
                    rfl

theorem cell20_637685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_637685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637685 prefixEnd_637685 := by exact prefixLift 637685
  have htrace : WordTrace (prefixWord ++ tailWord_637685) baseStart_637685 baseEnd_637685 := by
    simpa [prefixWord, tailWord_637685, baseEnd_637685] using wordTrace_append hprefix tailTrace_637685
  have hstable : (prefixWord ++ tailWord_637685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637685).length < 2 ^ (prefixWord ++ tailWord_637685).sum := by decide
  have hdescent : baseEnd_637685 < baseStart_637685 := by decide
  rcases family_descends (prefixWord ++ tailWord_637685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637745 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_637745 : Nat := 118140960795 + 637745 * 2 ^ 59
def prefixEnd_637745 : Nat := 4983230072969 + 3 ^ 40 * 637745 * 2
def baseEnd_637745 : Nat := 291084195557077825292951

theorem tailTrace_637745 : CollatzResearch.WordTrace tailWord_637745 prefixEnd_637745 291084195557077825292951 := by
  unfold tailWord_637745
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260471074566258019690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506980716377505346460459 23260471074566258019690689)
  ·
    refine ⟨17445353305924693514768017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23260471074566258019690689 17445353305924693514768017)
    ·
      refine ⟨13084014979443520136076013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17445353305924693514768017 13084014979443520136076013)
      ·
        refine ⟨4906505617291320051028505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13084014979443520136076013 4906505617291320051028505)
        ·
          refine ⟨3679879212968490038271379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4906505617291320051028505 3679879212968490038271379)
          ·
            refine ⟨5519818819452735057407069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679879212968490038271379 5519818819452735057407069)
            ·
              refine ⟨2069932057294775646527651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5519818819452735057407069 2069932057294775646527651)
              ·
                refine ⟨3104898085942163469791477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069932057294775646527651 3104898085942163469791477)
                ·
                  refine ⟨291084195557077825292951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104898085942163469791477 291084195557077825292951)
                  ·
                    rfl

theorem cell20_637745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_637745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637745 prefixEnd_637745 := by exact prefixLift 637745
  have htrace : WordTrace (prefixWord ++ tailWord_637745) baseStart_637745 baseEnd_637745 := by
    simpa [prefixWord, tailWord_637745, baseEnd_637745] using wordTrace_append hprefix tailTrace_637745
  have hstable : (prefixWord ++ tailWord_637745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637745).length < 2 ^ (prefixWord ++ tailWord_637745).sum := by decide
  have hdescent : baseEnd_637745 < baseStart_637745 := by decide
  rcases family_descends (prefixWord ++ tailWord_637745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637758 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_637758 : Nat := 118140960795 + 637758 * 2 ^ 59
def prefixEnd_637758 : Nat := 4983230072969 + 3 ^ 40 * 637758 * 2
def baseEnd_637758 : Nat := 291090129111307557859565

theorem tailTrace_637758 : CollatzResearch.WordTrace tailWord_637758 prefixEnd_637758 291090129111307557859565 := by
  unfold tailWord_637758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907618152939895154989241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15507296815679440826609285 2907618152939895154989241)
  ·
    refine ⟨2180713614704921366241931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907618152939895154989241 2180713614704921366241931)
    ·
      refine ⟨3271070422057382049362897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180713614704921366241931 3271070422057382049362897)
      ·
        refine ⟨2453302816543036537022173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3271070422057382049362897 2453302816543036537022173)
        ·
          refine ⟨919988556203638701383315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2453302816543036537022173 919988556203638701383315)
          ·
            refine ⟨1379982834305458052074973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919988556203638701383315 1379982834305458052074973)
            ·
              refine ⟨517493562864546769528115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1379982834305458052074973 517493562864546769528115)
              ·
                refine ⟨776240344296820154292173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517493562864546769528115 776240344296820154292173)
                ·
                  refine ⟨291090129111307557859565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776240344296820154292173 291090129111307557859565)
                  ·
                    rfl

theorem cell20_637758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_637758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637758 prefixEnd_637758 := by exact prefixLift 637758
  have htrace : WordTrace (prefixWord ++ tailWord_637758) baseStart_637758 baseEnd_637758 := by
    simpa [prefixWord, tailWord_637758, baseEnd_637758] using wordTrace_append hprefix tailTrace_637758
  have hstable : (prefixWord ++ tailWord_637758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637758).length < 2 ^ (prefixWord ++ tailWord_637758).sum := by decide
  have hdescent : baseEnd_637758 < baseStart_637758 := by decide
  rcases family_descends (prefixWord ++ tailWord_637758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637776 : List Nat := [2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_637776 : Nat := 118140960795 + 637776 * 2 ^ 59
def prefixEnd_637776 : Nat := 4983230072969 + 3 ^ 40 * 637776 * 2
def baseEnd_637776 : Nat := 97032781600593165086497

theorem tailTrace_637776 : CollatzResearch.WordTrace tailWord_637776 prefixEnd_637776 97032781600593165086497 := by
  unfold tailWord_637776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630800868726975157034591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15507734491635966876046121 11630800868726975157034591)
  ·
    refine ⟨17446201303090462735551887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11630800868726975157034591 17446201303090462735551887)
    ·
      refine ⟨26169301954635694103327831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446201303090462735551887 26169301954635694103327831)
      ·
        refine ⟨39253952931953541154991747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26169301954635694103327831 39253952931953541154991747)
        ·
          refine ⟨58880929397930311732487621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39253952931953541154991747 58880929397930311732487621)
          ·
            refine ⟨11040174262111933449841429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58880929397930311732487621 11040174262111933449841429)
            ·
              refine ⟨517508168536496880461317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11040174262111933449841429 517508168536496880461317)
              ·
                refine ⟨97032781600593165086497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517508168536496880461317 97032781600593165086497)
                ·
                  rfl

theorem cell20_637776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_637776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637776 prefixEnd_637776 := by exact prefixLift 637776
  have htrace : WordTrace (prefixWord ++ tailWord_637776) baseStart_637776 baseEnd_637776 := by
    simpa [prefixWord, tailWord_637776, baseEnd_637776] using wordTrace_append hprefix tailTrace_637776
  have hstable : (prefixWord ++ tailWord_637776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637776).length < 2 ^ (prefixWord ++ tailWord_637776).sum := by decide
  have hdescent : baseEnd_637776 < baseStart_637776 := by decide
  rcases family_descends (prefixWord ++ tailWord_637776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637783 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_637783 : Nat := 118140960795 + 637783 * 2 ^ 59
def prefixEnd_637783 : Nat := 4983230072969 + 3 ^ 40 * 637783 * 2
def baseEnd_637783 : Nat := 291101539792518582026129

theorem tailTrace_637783 : CollatzResearch.WordTrace tailWord_637783 prefixEnd_637783 291101539792518582026129 := by
  unfold tailWord_637783
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261857048428590509574003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15507904698952393673049335 23261857048428590509574003)
  ·
    refine ⟨34892785572642885764361005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23261857048428590509574003 34892785572642885764361005)
    ·
      refine ⟨13084794589741082161635377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34892785572642885764361005 13084794589741082161635377)
      ·
        refine ⟨9813595942305811621226533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13084794589741082161635377 9813595942305811621226533)
        ·
          refine ⟨1840049239182339678979975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9813595942305811621226533 1840049239182339678979975)
          ·
            refine ⟨2760073858773509518469963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840049239182339678979975 2760073858773509518469963)
            ·
              refine ⟨4140110788160264277704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760073858773509518469963 4140110788160264277704945)
              ·
                refine ⟨3105083091120198208278709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140110788160264277704945 3105083091120198208278709)
                ·
                  refine ⟨291101539792518582026129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3105083091120198208278709 291101539792518582026129)
                  ·
                    rfl

theorem cell20_637783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_637783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637783 prefixEnd_637783 := by exact prefixLift 637783
  have htrace : WordTrace (prefixWord ++ tailWord_637783) baseStart_637783 baseEnd_637783 := by
    simpa [prefixWord, tailWord_637783, baseEnd_637783] using wordTrace_append hprefix tailTrace_637783
  have hstable : (prefixWord ++ tailWord_637783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637783).length < 2 ^ (prefixWord ++ tailWord_637783).sum := by decide
  have hdescent : baseEnd_637783 < baseStart_637783 := by decide
  rcases family_descends (prefixWord ++ tailWord_637783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637786 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_637786 : Nat := 118140960795 + 637786 * 2 ^ 59
def prefixEnd_637786 : Nat := 4983230072969 + 3 ^ 40 * 637786 * 2
def baseEnd_637786 : Nat := 291102909074263904926117

theorem tailTrace_637786 : CollatzResearch.WordTrace tailWord_637786 prefixEnd_637786 291102909074263904926117 := by
  unfold tailWord_637786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815491616854430505483303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15507977644945148014622141 5815491616854430505483303)
  ·
    refine ⟨8723237425281645758224955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815491616854430505483303 8723237425281645758224955)
    ·
      refine ⟨13084856137922468637337433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8723237425281645758224955 13084856137922468637337433)
      ·
        refine ⟨9813642103441851478003075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13084856137922468637337433 9813642103441851478003075)
        ·
          refine ⟨14720463155162777217004613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813642103441851478003075 14720463155162777217004613)
          ·
            refine ⟨2760086841593020728188365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14720463155162777217004613 2760086841593020728188365)
            ·
              refine ⟨1035032565597382773070637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2760086841593020728188365 1035032565597382773070637)
              ·
                refine ⟨388137212099018539901489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035032565597382773070637 388137212099018539901489)
                ·
                  refine ⟨291102909074263904926117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388137212099018539901489 291102909074263904926117)
                  ·
                    rfl

theorem cell20_637786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_637786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637786 prefixEnd_637786 := by exact prefixLift 637786
  have htrace : WordTrace (prefixWord ++ tailWord_637786) baseStart_637786 baseEnd_637786 := by
    simpa [prefixWord, tailWord_637786, baseEnd_637786] using wordTrace_append hprefix tailTrace_637786
  have hstable : (prefixWord ++ tailWord_637786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637786).length < 2 ^ (prefixWord ++ tailWord_637786).sum := by decide
  have hdescent : baseEnd_637786 < baseStart_637786 := by decide
  rcases family_descends (prefixWord ++ tailWord_637786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637797 : List Nat := [1, 3, 1, 3, 1, 1, 10]
def baseStart_637797 : Nat := 118140960795 + 637797 * 2 ^ 59
def prefixEnd_637797 : Nat := 4983230072969 + 3 ^ 40 * 637797 * 2
def baseEnd_637797 : Nat := 32345325530444083951045

theorem tailTrace_637797 : CollatzResearch.WordTrace tailWord_637797 prefixEnd_637797 32345325530444083951045 := by
  unfold tailWord_637797
  simp only [CollatzResearch.WordTrace]
  refine ⟨23262367670377870900583645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15508245113585247267055763 23262367670377870900583645)
  ·
    refine ⟨8723387876391701587718867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23262367670377870900583645 8723387876391701587718867)
    ·
      refine ⟨13085081814587552381578301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8723387876391701587718867 13085081814587552381578301)
      ·
        refine ⟨4906905680470332143091863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13085081814587552381578301 4906905680470332143091863)
        ·
          refine ⟨7360358520705498214637795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906905680470332143091863 7360358520705498214637795)
          ·
            refine ⟨11040537781058247321956693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360358520705498214637795 11040537781058247321956693)
            ·
              refine ⟨32345325530444083951045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11040537781058247321956693 32345325530444083951045)
              ·
                rfl

theorem cell20_637797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_637797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637797 prefixEnd_637797 := by exact prefixLift 637797
  have htrace : WordTrace (prefixWord ++ tailWord_637797) baseStart_637797 baseEnd_637797 := by
    simpa [prefixWord, tailWord_637797, baseEnd_637797] using wordTrace_append hprefix tailTrace_637797
  have hstable : (prefixWord ++ tailWord_637797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637797).length < 2 ^ (prefixWord ++ tailWord_637797).sum := by decide
  have hdescent : baseEnd_637797 < baseStart_637797 := by decide
  rcases family_descends (prefixWord ++ tailWord_637797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637807 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 2]
def baseStart_637807 : Nat := 118140960795 + 637807 * 2 ^ 59
def prefixEnd_637807 : Nat := 4983230072969 + 3 ^ 40 * 637807 * 2
def baseEnd_637807 : Nat := 291112494046481165226031

theorem tailTrace_637807 : CollatzResearch.WordTrace tailWord_637807 prefixEnd_637807 291112494046481165226031 := by
  unfold tailWord_637807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23262732400341642608447675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15508488266894428405631783 23262732400341642608447675)
  ·
    refine ⟨34894098600512463912671513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23262732400341642608447675 34894098600512463912671513)
    ·
      refine ⟨26170573950384347934503635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34894098600512463912671513 26170573950384347934503635)
      ·
        refine ⟨39255860925576521901755453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26170573950384347934503635 39255860925576521901755453)
        ·
          refine ⟨14720947847091195713158295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39255860925576521901755453 14720947847091195713158295)
          ·
            refine ⟨22081421770636793569737443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720947847091195713158295 22081421770636793569737443)
            ·
              refine ⟨33122132655955190354606165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22081421770636793569737443 33122132655955190354606165)
              ·
                refine ⟨388149992061974886968041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33122132655955190354606165 388149992061974886968041)
                ·
                  refine ⟨291112494046481165226031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388149992061974886968041 291112494046481165226031)
                  ·
                    rfl

theorem cell20_637807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2].length) (baseStart_637807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637807 prefixEnd_637807 := by exact prefixLift 637807
  have htrace : WordTrace (prefixWord ++ tailWord_637807) baseStart_637807 baseEnd_637807 := by
    simpa [prefixWord, tailWord_637807, baseEnd_637807] using wordTrace_append hprefix tailTrace_637807
  have hstable : (prefixWord ++ tailWord_637807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637807).length < 2 ^ (prefixWord ++ tailWord_637807).sum := by decide
  have hdescent : baseEnd_637807 < baseStart_637807 := by decide
  rcases family_descends (prefixWord ++ tailWord_637807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637817 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_637817 : Nat := 118140960795 + 637817 * 2 ^ 59
def prefixEnd_637817 : Nat := 4983230072969 + 3 ^ 40 * 637817 * 2
def baseEnd_637817 : Nat := 291117058318965574892657

theorem tailTrace_637817 : CollatzResearch.WordTrace tailWord_637817 prefixEnd_637817 291117058318965574892657 := by
  unfold tailWord_637817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263097130305414316311705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15508731420203609544207803 23263097130305414316311705)
  ·
    refine ⟨17447322847729060737233779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23263097130305414316311705 17447322847729060737233779)
    ·
      refine ⟨26170984271593591105850669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447322847729060737233779 26170984271593591105850669)
      ·
        refine ⟨9814119101847596664694001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26170984271593591105850669 9814119101847596664694001)
        ·
          refine ⟨7360589326385697498520501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9814119101847596664694001 7360589326385697498520501)
          ·
            refine ⟨690055249348659140486297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7360589326385697498520501 690055249348659140486297)
            ·
              refine ⟨517541437011494355364723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690055249348659140486297 517541437011494355364723)
              ·
                refine ⟨776312155517241533047085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517541437011494355364723 776312155517241533047085)
                ·
                  refine ⟨291117058318965574892657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776312155517241533047085 291117058318965574892657)
                  ·
                    rfl

theorem cell20_637817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_637817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637817 prefixEnd_637817 := by exact prefixLift 637817
  have htrace : WordTrace (prefixWord ++ tailWord_637817) baseStart_637817 baseEnd_637817 := by
    simpa [prefixWord, tailWord_637817, baseEnd_637817] using wordTrace_append hprefix tailTrace_637817
  have hstable : (prefixWord ++ tailWord_637817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637817).length < 2 ^ (prefixWord ++ tailWord_637817).sum := by decide
  have hdescent : baseEnd_637817 < baseStart_637817 := by decide
  rcases family_descends (prefixWord ++ tailWord_637817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637828 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_637828 : Nat := 118140960795 + 637828 * 2 ^ 59
def prefixEnd_637828 : Nat := 4983230072969 + 3 ^ 40 * 637828 * 2
def baseEnd_637828 : Nat := 291122079018698425525945

theorem tailTrace_637828 : CollatzResearch.WordTrace tailWord_637828 prefixEnd_637828 291122079018698425525945 := by
  unfold tailWord_637828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631749166632781597481069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15508998888843708796641425 11631749166632781597481069)
  ·
    refine ⟨4361905937487293099055401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11631749166632781597481069 4361905937487293099055401)
    ·
      refine ⟨3271429453115469824291551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4361905937487293099055401 3271429453115469824291551)
      ·
        refine ⟨4907144179673204736437327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271429453115469824291551 4907144179673204736437327)
        ·
          refine ⟨7360716269509807104655991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907144179673204736437327 7360716269509807104655991)
          ·
            refine ⟨11041074404264710656983987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360716269509807104655991 11041074404264710656983987)
            ·
              refine ⟨16561611606397065985475981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11041074404264710656983987 16561611606397065985475981)
              ·
                refine ⟨6210604352398899744553493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16561611606397065985475981 6210604352398899744553493)
                ·
                  refine ⟨291122079018698425525945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6210604352398899744553493 291122079018698425525945)
                  ·
                    rfl

theorem cell20_637828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_637828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637828 prefixEnd_637828 := by exact prefixLift 637828
  have htrace : WordTrace (prefixWord ++ tailWord_637828) baseStart_637828 baseEnd_637828 := by
    simpa [prefixWord, tailWord_637828, baseEnd_637828] using wordTrace_append hprefix tailTrace_637828
  have hstable : (prefixWord ++ tailWord_637828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637828).length < 2 ^ (prefixWord ++ tailWord_637828).sum := by decide
  have hdescent : baseEnd_637828 < baseStart_637828 := by decide
  rcases family_descends (prefixWord ++ tailWord_637828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637835 : List Nat := [1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_637835 : Nat := 118140960795 + 637835 * 2 ^ 59
def prefixEnd_637835 : Nat := 4983230072969 + 3 ^ 40 * 637835 * 2
def baseEnd_637835 : Nat := 97041758003145837430861

theorem tailTrace_637835 : CollatzResearch.WordTrace tailWord_637835 prefixEnd_637835 97041758003145837430861 := by
  unfold tailWord_637835
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263753644240203390466959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15509169096160135593644639 23263753644240203390466959)
  ·
    refine ⟨34895630466360305085700439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23263753644240203390466959 34895630466360305085700439)
    ·
      refine ⟨52343445699540457628550659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34895630466360305085700439 52343445699540457628550659)
      ·
        refine ⟨78515168549310686442825989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52343445699540457628550659 78515168549310686442825989)
        ·
          refine ⟨14721594102995753708029873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78515168549310686442825989 14721594102995753708029873)
          ·
            refine ⟨11041195577246815281022405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14721594102995753708029873 11041195577246815281022405)
            ·
              refine ⟨2070224170733777865191701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11041195577246815281022405 2070224170733777865191701)
              ·
                refine ⟨97041758003145837430861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070224170733777865191701 97041758003145837430861)
                ·
                  rfl

theorem cell20_637835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_637835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637835 prefixEnd_637835 := by exact prefixLift 637835
  have htrace : WordTrace (prefixWord ++ tailWord_637835) baseStart_637835 baseEnd_637835 := by
    simpa [prefixWord, tailWord_637835, baseEnd_637835] using wordTrace_append hprefix tailTrace_637835
  have hstable : (prefixWord ++ tailWord_637835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637835).length < 2 ^ (prefixWord ++ tailWord_637835).sum := by decide
  have hdescent : baseEnd_637835 < baseStart_637835 := by decide
  rcases family_descends (prefixWord ++ tailWord_637835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637852 : List Nat := [2, 2, 3, 3, 2, 8]
def baseStart_637852 : Nat := 118140960795 + 637852 * 2 ^ 59
def prefixEnd_637852 : Nat := 4983230072969 + 3 ^ 40 * 637852 * 2
def baseEnd_637852 : Nat := 10782704936024481804661

theorem tailTrace_637852 : CollatzResearch.WordTrace tailWord_637852 prefixEnd_637852 10782704936024481804661 := by
  unfold tailWord_637852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632186842589307646917905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15509582456785743529223873 11632186842589307646917905)
  ·
    refine ⟨8724140131941980735188429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11632186842589307646917905 8724140131941980735188429)
    ·
      refine ⟨3271552549478242775695661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8724140131941980735188429 3271552549478242775695661)
      ·
        refine ⟨1226832206054341040885873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3271552549478242775695661 1226832206054341040885873)
        ·
          refine ⟨920124154540755780664405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226832206054341040885873 920124154540755780664405)
          ·
            refine ⟨10782704936024481804661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 920124154540755780664405 10782704936024481804661)
            ·
              rfl

theorem cell20_637852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 8].length) (baseStart_637852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637852 prefixEnd_637852 := by exact prefixLift 637852
  have htrace : WordTrace (prefixWord ++ tailWord_637852) baseStart_637852 baseEnd_637852 := by
    simpa [prefixWord, tailWord_637852, baseEnd_637852] using wordTrace_append hprefix tailTrace_637852
  have hstable : (prefixWord ++ tailWord_637852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637852).length < 2 ^ (prefixWord ++ tailWord_637852).sum := by decide
  have hdescent : baseEnd_637852 < baseStart_637852 := by decide
  rcases family_descends (prefixWord ++ tailWord_637852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637858 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_637858 : Nat := 118140960795 + 637858 * 2 ^ 59
def prefixEnd_637858 : Nat := 4983230072969 + 3 ^ 40 * 637858 * 2
def baseEnd_637858 : Nat := 291135771836151654525823

theorem tailTrace_637858 : CollatzResearch.WordTrace tailWord_637858 prefixEnd_637858 291135771836151654525823 := by
  unfold tailWord_637858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816148130789219579638557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15509728348771252212369485 5816148130789219579638557)
  ·
    refine ⟨2181055549045957342364459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5816148130789219579638557 2181055549045957342364459)
    ·
      refine ⟨3271583323568936013546689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181055549045957342364459 3271583323568936013546689)
      ·
        refine ⟨2453687492676702010160017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3271583323568936013546689 2453687492676702010160017)
        ·
          refine ⟨1840265619507526507620013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453687492676702010160017 1840265619507526507620013)
          ·
            refine ⟨690099607315322440357505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1840265619507526507620013 690099607315322440357505)
            ·
              refine ⟨517574705486491830268129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690099607315322440357505 517574705486491830268129)
              ·
                refine ⟨388181029114868872701097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517574705486491830268129 388181029114868872701097)
                ·
                  refine ⟨291135771836151654525823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388181029114868872701097 291135771836151654525823)
                  ·
                    rfl

theorem cell20_637858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_637858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637858 prefixEnd_637858 := by exact prefixLift 637858
  have htrace : WordTrace (prefixWord ++ tailWord_637858) baseStart_637858 baseEnd_637858 := by
    simpa [prefixWord, tailWord_637858, baseEnd_637858] using wordTrace_append hprefix tailTrace_637858
  have hstable : (prefixWord ++ tailWord_637858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637858).length < 2 ^ (prefixWord ++ tailWord_637858).sum := by decide
  have hdescent : baseEnd_637858 < baseStart_637858 := by decide
  rcases family_descends (prefixWord ++ tailWord_637858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637859 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_637859 : Nat := 118140960795 + 637859 * 2 ^ 59
def prefixEnd_637859 : Nat := 4983230072969 + 3 ^ 40 * 637859 * 2
def baseEnd_637859 : Nat := 291136228263400095492485

theorem tailTrace_637859 : CollatzResearch.WordTrace tailWord_637859 prefixEnd_637859 291136228263400095492485 := by
  unfold tailWord_637859
  simp only [CollatzResearch.WordTrace]
  refine ⟨23264628996153255489340631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15509752664102170326227087 23264628996153255489340631)
  ·
    refine ⟨34896943494229883234010947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23264628996153255489340631 34896943494229883234010947)
    ·
      refine ⟨52345415241344824851016421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34896943494229883234010947 52345415241344824851016421)
      ·
        refine ⟨9814765357752154659565579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52345415241344824851016421 9814765357752154659565579)
        ·
          refine ⟨14722148036628231989348369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814765357752154659565579 14722148036628231989348369)
          ·
            refine ⟨11041611027471173992011277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14722148036628231989348369 11041611027471173992011277)
            ·
              refine ⟨4140604135301690247004229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11041611027471173992011277 4140604135301690247004229)
              ·
                refine ⟨776363275369066921313293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4140604135301690247004229 776363275369066921313293)
                ·
                  refine ⟨291136228263400095492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776363275369066921313293 291136228263400095492485)
                  ·
                    rfl

theorem cell20_637859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_637859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637859 prefixEnd_637859 := by exact prefixLift 637859
  have htrace : WordTrace (prefixWord ++ tailWord_637859) baseStart_637859 baseEnd_637859 := by
    simpa [prefixWord, tailWord_637859, baseEnd_637859] using wordTrace_append hprefix tailTrace_637859
  have hstable : (prefixWord ++ tailWord_637859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637859).length < 2 ^ (prefixWord ++ tailWord_637859).sum := by decide
  have hdescent : baseEnd_637859 < baseStart_637859 := by decide
  rcases family_descends (prefixWord ++ tailWord_637859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637900 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_637900 : Nat := 118140960795 + 637900 * 2 ^ 59
def prefixEnd_637900 : Nat := 4983230072969 + 3 ^ 40 * 637900 * 2
def baseEnd_637900 : Nat := 291154941780586175125651

theorem tailTrace_637900 : CollatzResearch.WordTrace tailWord_637900 prefixEnd_637900 291154941780586175125651 := by
  unfold tailWord_637900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633062194502359745791577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15510749592669812994388769 11633062194502359745791577)
  ·
    refine ⟨8724796645876769809343683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11633062194502359745791577 8724796645876769809343683)
    ·
      refine ⟨13087194968815154714015525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724796645876769809343683 13087194968815154714015525)
      ·
        refine ⟨2453849056652841508877911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13087194968815154714015525 2453849056652841508877911)
        ·
          refine ⟨3680773584979262263316867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453849056652841508877911 3680773584979262263316867)
          ·
            refine ⟨5521160377468893394975301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680773584979262263316867 5521160377468893394975301)
            ·
              refine ⟨1035217570775417511557869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5521160377468893394975301 1035217570775417511557869)
              ·
                refine ⟨388206589040781566834201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035217570775417511557869 388206589040781566834201)
                ·
                  refine ⟨291154941780586175125651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388206589040781566834201 291154941780586175125651)
                  ·
                    rfl

theorem cell20_637900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_637900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637900 prefixEnd_637900 := by exact prefixLift 637900
  have htrace : WordTrace (prefixWord ++ tailWord_637900) baseStart_637900 baseEnd_637900 := by
    simpa [prefixWord, tailWord_637900, baseEnd_637900] using wordTrace_append hprefix tailTrace_637900
  have hstable : (prefixWord ++ tailWord_637900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637900).length < 2 ^ (prefixWord ++ tailWord_637900).sum := by decide
  have hdescent : baseEnd_637900 < baseStart_637900 := by decide
  rcases family_descends (prefixWord ++ tailWord_637900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637910 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_637910 : Nat := 118140960795 + 637910 * 2 ^ 59
def prefixEnd_637910 : Nat := 4983230072969 + 3 ^ 40 * 637910 * 2
def baseEnd_637910 : Nat := 291159506053070584792277

theorem tailTrace_637910 : CollatzResearch.WordTrace tailWord_637910 prefixEnd_637910 291159506053070584792277 := by
  unfold tailWord_637910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454155569935530699965449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15510992745978994132964789 1454155569935530699965449)
  ·
    refine ⟨1090616677451648024974087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1454155569935530699965449 1090616677451648024974087)
    ·
      refine ⟨1635925016177472037461131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090616677451648024974087 1635925016177472037461131)
      ·
        refine ⟨2453887524266208056191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635925016177472037461131 2453887524266208056191697)
        ·
          refine ⟨1840415643199656042143773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453887524266208056191697 1840415643199656042143773)
          ·
            refine ⟨690155866199871015803915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1840415643199656042143773 690155866199871015803915)
            ·
              refine ⟨1035233799299806523705873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690155866199871015803915 1035233799299806523705873)
              ·
                refine ⟨776425349474854892779405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035233799299806523705873 776425349474854892779405)
                ·
                  refine ⟨291159506053070584792277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776425349474854892779405 291159506053070584792277)
                  ·
                    rfl

theorem cell20_637910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_637910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637910 prefixEnd_637910 := by exact prefixLift 637910
  have htrace : WordTrace (prefixWord ++ tailWord_637910) baseStart_637910 baseEnd_637910 := by
    simpa [prefixWord, tailWord_637910, baseEnd_637910] using wordTrace_append hprefix tailTrace_637910
  have hstable : (prefixWord ++ tailWord_637910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637910).length < 2 ^ (prefixWord ++ tailWord_637910).sum := by decide
  have hdescent : baseEnd_637910 < baseStart_637910 := by decide
  rcases family_descends (prefixWord ++ tailWord_637910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637914 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_637914 : Nat := 118140960795 + 637914 * 2 ^ 59
def prefixEnd_637914 : Nat := 4983230072969 + 3 ^ 40 * 637914 * 2
def baseEnd_637914 : Nat := 291161331762064348658927

theorem tailTrace_637914 : CollatzResearch.WordTrace tailWord_637914 prefixEnd_637914 291161331762064348658927 := by
  unfold tailWord_637914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816658752738499970648199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15511090007302666588395197 5816658752738499970648199)
  ·
    refine ⟨8724988129107749955972299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816658752738499970648199 8724988129107749955972299)
    ·
      refine ⟨13087482193661624933958449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724988129107749955972299 13087482193661624933958449)
      ·
        refine ⟨9815611645246218700468837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13087482193661624933958449 9815611645246218700468837)
        ·
          refine ⟨1840427183483666006337907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9815611645246218700468837 1840427183483666006337907)
          ·
            refine ⟨2760640775225499009506861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840427183483666006337907 2760640775225499009506861)
            ·
              refine ⟨1035240290709562128565073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2760640775225499009506861 1035240290709562128565073)
              ·
                refine ⟨776430218032171596423805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035240290709562128565073 776430218032171596423805)
                ·
                  refine ⟨291161331762064348658927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776430218032171596423805 291161331762064348658927)
                  ·
                    rfl

theorem cell20_637914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_637914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637914 prefixEnd_637914 := by exact prefixLift 637914
  have htrace : WordTrace (prefixWord ++ tailWord_637914) baseStart_637914 baseEnd_637914 := by
    simpa [prefixWord, tailWord_637914, baseEnd_637914] using wordTrace_append hprefix tailTrace_637914
  have hstable : (prefixWord ++ tailWord_637914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637914).length < 2 ^ (prefixWord ++ tailWord_637914).sum := by decide
  have hdescent : baseEnd_637914 < baseStart_637914 := by decide
  rcases family_descends (prefixWord ++ tailWord_637914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637941 : List Nat := [1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_637941 : Nat := 118140960795 + 637941 * 2 ^ 59
def prefixEnd_637941 : Nat := 4983230072969 + 3 ^ 40 * 637941 * 2
def baseEnd_637941 : Nat := 97057885099257418252939

theorem tailTrace_637941 : CollatzResearch.WordTrace tailWord_637941 prefixEnd_637941 97057885099257418252939 := by
  unfold tailWord_637941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23267619781856183493825677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15511746521237455662550451 23267619781856183493825677)
  ·
    refine ⟨8725357418196068810184629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23267619781856183493825677 8725357418196068810184629)
    ·
      refine ⟨818002257955881450954809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8725357418196068810184629 818002257955881450954809)
      ·
        refine ⟨613501693466911088216107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818002257955881450954809 613501693466911088216107)
        ·
          refine ⟨920252540200366632324161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613501693466911088216107 920252540200366632324161)
          ·
            refine ⟨690189405150274974243121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920252540200366632324161 690189405150274974243121)
            ·
              refine ⟨517642053862706230682341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690189405150274974243121 517642053862706230682341)
              ·
                refine ⟨97057885099257418252939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517642053862706230682341 97057885099257418252939)
                ·
                  rfl

theorem cell20_637941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_637941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637941 prefixEnd_637941 := by exact prefixLift 637941
  have htrace : WordTrace (prefixWord ++ tailWord_637941) baseStart_637941 baseEnd_637941 := by
    simpa [prefixWord, tailWord_637941, baseEnd_637941] using wordTrace_append hprefix tailTrace_637941
  have hstable : (prefixWord ++ tailWord_637941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637941).length < 2 ^ (prefixWord ++ tailWord_637941).sum := by decide
  have hdescent : baseEnd_637941 < baseStart_637941 := by decide
  rcases family_descends (prefixWord ++ tailWord_637941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637966 : List Nat := [4, 1, 1, 2, 2, 4, 6]
def baseStart_637966 : Nat := 118140960795 + 637966 * 2 ^ 59
def prefixEnd_637966 : Nat := 4983230072969 + 3 ^ 40 * 637966 * 2
def baseEnd_637966 : Nat := 32353896219887030991709

theorem tailTrace_637966 : CollatzResearch.WordTrace tailWord_637966 prefixEnd_637966 32353896219887030991709 := by
  unfold tailWord_637966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908566450845701595435719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15512354404510408508990501 2908566450845701595435719)
  ·
    refine ⟨4362849676268552393153579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908566450845701595435719 4362849676268552393153579)
    ·
      refine ⟨6544274514402828589730369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362849676268552393153579 6544274514402828589730369)
      ·
        refine ⟨4908205885802121442297777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6544274514402828589730369 4908205885802121442297777)
        ·
          refine ⟨3681154414351591081723333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4908205885802121442297777 3681154414351591081723333)
          ·
            refine ⟨690216452690923327823125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3681154414351591081723333 690216452690923327823125)
            ·
              refine ⟨32353896219887030991709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 690216452690923327823125 32353896219887030991709)
              ·
                rfl

theorem cell20_637966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_637966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637966 prefixEnd_637966 := by exact prefixLift 637966
  have htrace : WordTrace (prefixWord ++ tailWord_637966) baseStart_637966 baseEnd_637966 := by
    simpa [prefixWord, tailWord_637966, baseEnd_637966] using wordTrace_append hprefix tailTrace_637966
  have hstable : (prefixWord ++ tailWord_637966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637966).length < 2 ^ (prefixWord ++ tailWord_637966).sum := by decide
  have hdescent : baseEnd_637966 < baseStart_637966 := by decide
  rcases family_descends (prefixWord ++ tailWord_637966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637973 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_637973 : Nat := 118140960795 + 637973 * 2 ^ 59
def prefixEnd_637973 : Nat := 4983230072969 + 3 ^ 40 * 637973 * 2
def baseEnd_637973 : Nat := 291188260969722365692019

theorem tailTrace_637973 : CollatzResearch.WordTrace tailWord_637973 prefixEnd_637973 291188260969722365692019 := by
  unfold tailWord_637973
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268786917740252958990573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15512524611826835305993715 23268786917740252958990573)
  ·
    refine ⟨8725795094152594859621465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23268786917740252958990573 8725795094152594859621465)
    ·
      refine ⟨6544346320614446144716099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8725795094152594859621465 6544346320614446144716099)
      ·
        refine ⟨9816519480921669217074149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544346320614446144716099 9816519480921669217074149)
        ·
          refine ⟨1840597402672812978201403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9816519480921669217074149 1840597402672812978201403)
          ·
            refine ⟨2760896104009219467302105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840597402672812978201403 2760896104009219467302105)
            ·
              refine ⟨2070672078006914600476579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760896104009219467302105 2070672078006914600476579)
              ·
                refine ⟨3106008117010371900714869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070672078006914600476579 3106008117010371900714869)
                ·
                  refine ⟨291188260969722365692019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106008117010371900714869 291188260969722365692019)
                  ·
                    rfl

theorem cell20_637973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_637973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637973 prefixEnd_637973 := by exact prefixLift 637973
  have htrace : WordTrace (prefixWord ++ tailWord_637973) baseStart_637973 baseEnd_637973 := by
    simpa [prefixWord, tailWord_637973, baseEnd_637973] using wordTrace_append hprefix tailTrace_637973
  have hstable : (prefixWord ++ tailWord_637973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637973).length < 2 ^ (prefixWord ++ tailWord_637973).sum := by decide
  have hdescent : baseEnd_637973 < baseStart_637973 := by decide
  rcases family_descends (prefixWord ++ tailWord_637973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637987 : List Nat := [1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_637987 : Nat := 118140960795 + 637987 * 2 ^ 59
def prefixEnd_637987 : Nat := 4983230072969 + 3 ^ 40 * 637987 * 2
def baseEnd_637987 : Nat := 97064883650400179741765

theorem tailTrace_637987 : CollatzResearch.WordTrace tailWord_637987 prefixEnd_637987 97064883650400179741765 := by
  unfold tailWord_637987
  simp only [CollatzResearch.WordTrace]
  refine ⟨23269297539689533350000215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15512865026459688900000143 23269297539689533350000215)
  ·
    refine ⟨34903946309534300025000323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23269297539689533350000215 34903946309534300025000323)
    ·
      refine ⟨52355919464301450037500485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34903946309534300025000323 52355919464301450037500485)
      ·
        refine ⟨9816734899556521882031341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52355919464301450037500485 9816734899556521882031341)
        ·
          refine ⟨3681275587333695705761753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9816734899556521882031341 3681275587333695705761753)
          ·
            refine ⟨2760956690500271779321315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3681275587333695705761753 2760956690500271779321315)
            ·
              refine ⟨4141435035750407668981973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760956690500271779321315 4141435035750407668981973)
              ·
                refine ⟨97064883650400179741765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4141435035750407668981973 97064883650400179741765)
                ·
                  rfl

theorem cell20_637987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_637987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_637987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_637987 prefixEnd_637987 := by exact prefixLift 637987
  have htrace : WordTrace (prefixWord ++ tailWord_637987) baseStart_637987 baseEnd_637987 := by
    simpa [prefixWord, tailWord_637987, baseEnd_637987] using wordTrace_append hprefix tailTrace_637987
  have hstable : (prefixWord ++ tailWord_637987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637987).length < 2 ^ (prefixWord ++ tailWord_637987).sum := by decide
  have hdescent : baseEnd_637987 < baseStart_637987 := by decide
  rcases family_descends (prefixWord ++ tailWord_637987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638032 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_638032 : Nat := 118140960795 + 638032 * 2 ^ 59
def prefixEnd_638032 : Nat := 4983230072969 + 3 ^ 40 * 638032 * 2
def baseEnd_638032 : Nat := 291215190177380382725111

theorem tailTrace_638032 : CollatzResearch.WordTrace tailWord_638032 prefixEnd_638032 291215190177380382725111 := by
  unfold tailWord_638032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635469412263253017694175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15513959216351004023592233 11635469412263253017694175)
  ·
    refine ⟨17453204118394879526541263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635469412263253017694175 17453204118394879526541263)
    ·
      refine ⟨26179806177592319289811895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17453204118394879526541263 26179806177592319289811895)
      ·
        refine ⟨39269709266388478934717843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26179806177592319289811895 39269709266388478934717843)
        ·
          refine ⟨58904563899582718402076765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39269709266388478934717843 58904563899582718402076765)
          ·
            refine ⟨22089211462343519400778787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58904563899582718402076765 22089211462343519400778787)
            ·
              refine ⟨33133817193515279101168181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22089211462343519400778787 33133817193515279101168181)
              ·
                refine ⟨3106295361892057415734517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33133817193515279101168181 3106295361892057415734517)
                ·
                  refine ⟨291215190177380382725111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106295361892057415734517 291215190177380382725111)
                  ·
                    rfl

theorem cell20_638032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_638032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638032 prefixEnd_638032 := by exact prefixLift 638032
  have htrace : WordTrace (prefixWord ++ tailWord_638032) baseStart_638032 baseEnd_638032 := by
    simpa [prefixWord, tailWord_638032, baseEnd_638032] using wordTrace_append hprefix tailTrace_638032
  have hstable : (prefixWord ++ tailWord_638032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638032).length < 2 ^ (prefixWord ++ tailWord_638032).sum := by decide
  have hdescent : baseEnd_638032 < baseStart_638032 := by decide
  rcases family_descends (prefixWord ++ tailWord_638032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638049 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_638049 : Nat := 118140960795 + 638049 * 2 ^ 59
def prefixEnd_638049 : Nat := 4983230072969 + 3 ^ 40 * 638049 * 2
def baseEnd_638049 : Nat := 291222949440603879158375

theorem tailTrace_638049 : CollatzResearch.WordTrace tailWord_638049 prefixEnd_638049 291222949440603879158375 := by
  unfold tailWord_638049
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271558865464917938757201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15514372576976611959171467 23271558865464917938757201)
  ·
    refine ⟨17453669149098688454067901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23271558865464917938757201 17453669149098688454067901)
    ·
      refine ⟨6545125930912008170275463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17453669149098688454067901 6545125930912008170275463)
      ·
        refine ⟨9817688896368012255413195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545125930912008170275463 9817688896368012255413195)
        ·
          refine ⟨14726533344552018383119793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817688896368012255413195 14726533344552018383119793)
          ·
            refine ⟨11044900008414013787339845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14726533344552018383119793 11044900008414013787339845)
            ·
              refine ⟨2070918751577627585126221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11044900008414013787339845 2070918751577627585126221)
              ·
                refine ⟨776594531841610344422333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2070918751577627585126221 776594531841610344422333)
                ·
                  refine ⟨291222949440603879158375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776594531841610344422333 291222949440603879158375)
                  ·
                    rfl

theorem cell20_638049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_638049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638049 prefixEnd_638049 := by exact prefixLift 638049
  have htrace : WordTrace (prefixWord ++ tailWord_638049) baseStart_638049 baseEnd_638049 := by
    simpa [prefixWord, tailWord_638049, baseEnd_638049] using wordTrace_append hprefix tailTrace_638049
  have hstable : (prefixWord ++ tailWord_638049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638049).length < 2 ^ (prefixWord ++ tailWord_638049).sum := by decide
  have hdescent : baseEnd_638049 < baseStart_638049 := by decide
  rcases family_descends (prefixWord ++ tailWord_638049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638114 : List Nat := [3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_638114 : Nat := 118140960795 + 638114 * 2 ^ 59
def prefixEnd_638114 : Nat := 4983230072969 + 3 ^ 40 * 638114 * 2
def baseEnd_638114 : Nat := 97084205737250847330481

theorem tailTrace_638114 : CollatzResearch.WordTrace tailWord_638114 prefixEnd_638114 97084205737250847330481 := by
  unfold tailWord_638114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818482402557358509968349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15515953073486289359915597 5818482402557358509968349)
  ·
    refine ⟨2181930900959009441238131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5818482402557358509968349 2181930900959009441238131)
    ·
      refine ⟨3272896351438514161857197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181930900959009441238131 3272896351438514161857197)
      ·
        refine ⟨1227336131789442810696449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3272896351438514161857197 1227336131789442810696449)
        ·
          refine ⟨920502098842082108022337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227336131789442810696449 920502098842082108022337)
          ·
            refine ⟨690376574131561581016753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920502098842082108022337 690376574131561581016753)
            ·
              refine ⟨517782430598671185762565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690376574131561581016753 517782430598671185762565)
              ·
                refine ⟨97084205737250847330481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517782430598671185762565 97084205737250847330481)
                ·
                  rfl

theorem cell20_638114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_638114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638114 prefixEnd_638114 := by exact prefixLift 638114
  have htrace : WordTrace (prefixWord ++ tailWord_638114) baseStart_638114 baseEnd_638114 := by
    simpa [prefixWord, tailWord_638114, baseEnd_638114] using wordTrace_append hprefix tailTrace_638114
  have hstable : (prefixWord ++ tailWord_638114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638114).length < 2 ^ (prefixWord ++ tailWord_638114).sum := by decide
  have hdescent : baseEnd_638114 < baseStart_638114 := by decide
  rcases family_descends (prefixWord ++ tailWord_638114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638177 : List Nat := [1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_638177 : Nat := 118140960795 + 638177 * 2 ^ 59
def prefixEnd_638177 : Nat := 4983230072969 + 3 ^ 40 * 638177 * 2
def baseEnd_638177 : Nat := 97093790709468107630395

theorem tailTrace_638177 : CollatzResearch.WordTrace tailWord_638177 prefixEnd_638177 97093790709468107630395 := by
  unfold tailWord_638177
  simp only [CollatzResearch.WordTrace]
  refine ⟨23276227409001195799416785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15517484939334130532944523 23276227409001195799416785)
  ·
    refine ⟨17457170556750896849562589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23276227409001195799416785 17457170556750896849562589)
    ·
      refine ⟨6546438958781586318585971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17457170556750896849562589 6546438958781586318585971)
      ·
        refine ⟨9819658438172379477878957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6546438958781586318585971 9819658438172379477878957)
        ·
          refine ⟨3682371914314642304204609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9819658438172379477878957 3682371914314642304204609)
          ·
            refine ⟨2761778935735981728153457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682371914314642304204609 2761778935735981728153457)
            ·
              refine ⟨2071334201801986296115093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761778935735981728153457 2071334201801986296115093)
              ·
                refine ⟨97093790709468107630395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2071334201801986296115093 97093790709468107630395)
                ·
                  rfl

theorem cell20_638177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_638177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638177 prefixEnd_638177 := by exact prefixLift 638177
  have htrace : WordTrace (prefixWord ++ tailWord_638177) baseStart_638177 baseEnd_638177 := by
    simpa [prefixWord, tailWord_638177, baseEnd_638177] using wordTrace_append hprefix tailTrace_638177
  have hstable : (prefixWord ++ tailWord_638177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638177).length < 2 ^ (prefixWord ++ tailWord_638177).sum := by decide
  have hdescent : baseEnd_638177 < baseStart_638177 := by decide
  rcases family_descends (prefixWord ++ tailWord_638177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638194 : List Nat := [3, 2, 1, 3, 4, 7]
def baseStart_638194 : Nat := 118140960795 + 638194 * 2 ^ 59
def prefixEnd_638194 : Nat := 4983230072969 + 3 ^ 40 * 638194 * 2
def baseEnd_638194 : Nat := 10788486347838067382387

theorem tailTrace_638194 : CollatzResearch.WordTrace tailWord_638194 prefixEnd_638194 10788486347838067382387 := by
  unfold tailWord_638194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819211862484901925696409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15517898299959738468523757 5819211862484901925696409)
  ·
    refine ⟨4364408896863676444272307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5819211862484901925696409 4364408896863676444272307)
    ·
      refine ⟨6546613345295514666408461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4364408896863676444272307 6546613345295514666408461)
      ·
        refine ⟨2454980004485817999903173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6546613345295514666408461 2454980004485817999903173)
        ·
          refine ⟨460308750841090874981845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2454980004485817999903173 460308750841090874981845)
          ·
            refine ⟨10788486347838067382387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 460308750841090874981845 10788486347838067382387)
            ·
              rfl

theorem cell20_638194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 7].length) (baseStart_638194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638194 prefixEnd_638194 := by exact prefixLift 638194
  have htrace : WordTrace (prefixWord ++ tailWord_638194) baseStart_638194 baseEnd_638194 := by
    simpa [prefixWord, tailWord_638194, baseEnd_638194] using wordTrace_append hprefix tailTrace_638194
  have hstable : (prefixWord ++ tailWord_638194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638194).length < 2 ^ (prefixWord ++ tailWord_638194).sum := by decide
  have hdescent : baseEnd_638194 < baseStart_638194 := by decide
  rcases family_descends (prefixWord ++ tailWord_638194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638196 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_638196 : Nat := 118140960795 + 638196 * 2 ^ 59
def prefixEnd_638196 : Nat := 4983230072969 + 3 ^ 40 * 638196 * 2
def baseEnd_638196 : Nat := 291290044246124701257775

theorem tailTrace_638196 : CollatzResearch.WordTrace tailWord_638196 prefixEnd_638196 291290044246124701257775 := by
  unfold tailWord_638196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638460197966181022179221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15517946930621574696238961 11638460197966181022179221)
  ·
    refine ⟨545552821779664735414651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11638460197966181022179221 545552821779664735414651)
    ·
      refine ⟨818329232669497103121977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545552821779664735414651 818329232669497103121977)
      ·
        refine ⟨613746924502122827341483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818329232669497103121977 613746924502122827341483)
        ·
          refine ⟨920620386753184241012225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613746924502122827341483 920620386753184241012225)
          ·
            refine ⟨690465290064888180759169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920620386753184241012225 690465290064888180759169)
            ·
              refine ⟨517848967548666135569377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690465290064888180759169 517848967548666135569377)
              ·
                refine ⟨388386725661499601677033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517848967548666135569377 388386725661499601677033)
                ·
                  refine ⟨291290044246124701257775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388386725661499601677033 291290044246124701257775)
                  ·
                    rfl

theorem cell20_638196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_638196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638196 prefixEnd_638196 := by exact prefixLift 638196
  have htrace : WordTrace (prefixWord ++ tailWord_638196) baseStart_638196 baseEnd_638196 := by
    simpa [prefixWord, tailWord_638196, baseEnd_638196] using wordTrace_append hprefix tailTrace_638196
  have hstable : (prefixWord ++ tailWord_638196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638196).length < 2 ^ (prefixWord ++ tailWord_638196).sum := by decide
  have hdescent : baseEnd_638196 < baseStart_638196 := by decide
  rcases family_descends (prefixWord ++ tailWord_638196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638201 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_638201 : Nat := 118140960795 + 638201 * 2 ^ 59
def prefixEnd_638201 : Nat := 4983230072969 + 3 ^ 40 * 638201 * 2
def baseEnd_638201 : Nat := 291292326382366906091087

theorem tailTrace_638201 : CollatzResearch.WordTrace tailWord_638201 prefixEnd_638201 291292326382366906091087 := by
  unfold tailWord_638201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277102760914247898290457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15518068507276165265526971 23277102760914247898290457)
  ·
    refine ⟨17457827070685685923717843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23277102760914247898290457 17457827070685685923717843)
    ·
      refine ⟨26186740606028528885576765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17457827070685685923717843 26186740606028528885576765)
      ·
        refine ⟨9820027727260698332091287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26186740606028528885576765 9820027727260698332091287)
        ·
          refine ⟨14730041590891047498136931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9820027727260698332091287 14730041590891047498136931)
          ·
            refine ⟨22095062386336571247205397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14730041590891047498136931 22095062386336571247205397)
            ·
              refine ⟨1035706049359526777212753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22095062386336571247205397 1035706049359526777212753)
              ·
                refine ⟨776779537019645082909565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035706049359526777212753 776779537019645082909565)
                ·
                  refine ⟨291292326382366906091087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776779537019645082909565 291292326382366906091087)
                  ·
                    rfl

theorem cell20_638201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_638201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638201 prefixEnd_638201 := by exact prefixLift 638201
  have htrace : WordTrace (prefixWord ++ tailWord_638201) baseStart_638201 baseEnd_638201 := by
    simpa [prefixWord, tailWord_638201, baseEnd_638201] using wordTrace_append hprefix tailTrace_638201
  have hstable : (prefixWord ++ tailWord_638201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638201).length < 2 ^ (prefixWord ++ tailWord_638201).sum := by decide
  have hdescent : baseEnd_638201 < baseStart_638201 := by decide
  rcases family_descends (prefixWord ++ tailWord_638201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638204 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_638204 : Nat := 118140960795 + 638204 * 2 ^ 59
def prefixEnd_638204 : Nat := 4983230072969 + 3 ^ 40 * 638204 * 2
def baseEnd_638204 : Nat := 291293695664112228991075

theorem tailTrace_638204 : CollatzResearch.WordTrace tailWord_638204 prefixEnd_638204 291293695664112228991075 := by
  unfold tailWord_638204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638606089951689705324833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15518141453268919607099777 11638606089951689705324833)
  ·
    refine ⟨8728954567463767278993625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11638606089951689705324833 8728954567463767278993625)
    ·
      refine ⟨6546715925597825459245219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8728954567463767278993625 6546715925597825459245219)
      ·
        refine ⟨9820073888396738188867829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6546715925597825459245219 9820073888396738188867829)
        ·
          refine ⟨920631927037194205206359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9820073888396738188867829 920631927037194205206359)
          ·
            refine ⟨1380947890555791307809539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920631927037194205206359 1380947890555791307809539)
            ·
              refine ⟨2071421835833686961714309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380947890555791307809539 2071421835833686961714309)
              ·
                refine ⟨388391594218816305321433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2071421835833686961714309 388391594218816305321433)
                ·
                  refine ⟨291293695664112228991075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388391594218816305321433 291293695664112228991075)
                  ·
                    rfl

theorem cell20_638204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_638204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638204 prefixEnd_638204 := by exact prefixLift 638204
  have htrace : WordTrace (prefixWord ++ tailWord_638204) baseStart_638204 baseEnd_638204 := by
    simpa [prefixWord, tailWord_638204, baseEnd_638204] using wordTrace_append hprefix tailTrace_638204
  have hstable : (prefixWord ++ tailWord_638204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638204).length < 2 ^ (prefixWord ++ tailWord_638204).sum := by decide
  have hdescent : baseEnd_638204 < baseStart_638204 := by decide
  rcases family_descends (prefixWord ++ tailWord_638204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638232 : List Nat := [2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_638232 : Nat := 118140960795 + 638232 * 2 ^ 59
def prefixEnd_638232 : Nat := 4983230072969 + 3 ^ 40 * 638232 * 2
def baseEnd_638232 : Nat := 97102158542356192019209

theorem tailTrace_638232 : CollatzResearch.WordTrace tailWord_638232 prefixEnd_638232 97102158542356192019209 := by
  unfold tailWord_638232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11639116711900970096334475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15518822282534626795112633 11639116711900970096334475)
  ·
    refine ⟨17458675067851455144501713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11639116711900970096334475 17458675067851455144501713)
    ·
      refine ⟨13094006300888591358376285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17458675067851455144501713 13094006300888591358376285)
      ·
        refine ⟨4910252362833221759391107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13094006300888591358376285 4910252362833221759391107)
        ·
          refine ⟨7365378544249832639086661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910252362833221759391107 7365378544249832639086661)
          ·
            refine ⟨1381008477046843619828749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7365378544249832639086661 1381008477046843619828749)
            ·
              refine ⟨517878178892566357435781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1381008477046843619828749 517878178892566357435781)
              ·
                refine ⟨97102158542356192019209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517878178892566357435781 97102158542356192019209)
                ·
                  rfl

theorem cell20_638232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_638232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638232 prefixEnd_638232 := by exact prefixLift 638232
  have htrace : WordTrace (prefixWord ++ tailWord_638232) baseStart_638232 baseEnd_638232 := by
    simpa [prefixWord, tailWord_638232, baseEnd_638232] using wordTrace_append hprefix tailTrace_638232
  have hstable : (prefixWord ++ tailWord_638232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638232).length < 2 ^ (prefixWord ++ tailWord_638232).sum := by decide
  have hdescent : baseEnd_638232 < baseStart_638232 := by decide
  rcases family_descends (prefixWord ++ tailWord_638232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638238 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_638238 : Nat := 118140960795 + 638238 * 2 ^ 59
def prefixEnd_638238 : Nat := 4983230072969 + 3 ^ 40 * 638238 * 2
def baseEnd_638238 : Nat := 291309214190559221857603

theorem tailTrace_638238 : CollatzResearch.WordTrace tailWord_638238 prefixEnd_638238 291309214190559221857603 := by
  unfold tailWord_638238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909806532722525402173421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15518968174520135478258245 2909806532722525402173421)
  ·
    refine ⟨1091177449770947025815033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2909806532722525402173421 1091177449770947025815033)
    ·
      refine ⟨818383087328210269361275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091177449770947025815033 818383087328210269361275)
      ·
        refine ⟨1227574630992315404041913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818383087328210269361275 1227574630992315404041913)
        ·
          refine ⟨920680973244236553031435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227574630992315404041913 920680973244236553031435)
          ·
            refine ⟨1381021459866354829547153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920680973244236553031435 1381021459866354829547153)
            ·
              refine ⟨1035766094899766122160365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381021459866354829547153 1035766094899766122160365)
              ·
                refine ⟨388412285587412295810137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035766094899766122160365 388412285587412295810137)
                ·
                  refine ⟨291309214190559221857603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388412285587412295810137 291309214190559221857603)
                  ·
                    rfl

theorem cell20_638238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_638238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638238 prefixEnd_638238 := by exact prefixLift 638238
  have htrace : WordTrace (prefixWord ++ tailWord_638238) baseStart_638238 baseEnd_638238 := by
    simpa [prefixWord, tailWord_638238, baseEnd_638238] using wordTrace_append hprefix tailTrace_638238
  have hstable : (prefixWord ++ tailWord_638238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638238).length < 2 ^ (prefixWord ++ tailWord_638238).sum := by decide
  have hdescent : baseEnd_638238 < baseStart_638238 := by decide
  rcases family_descends (prefixWord ++ tailWord_638238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638273 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_638273 : Nat := 118140960795 + 638273 * 2 ^ 59
def prefixEnd_638273 : Nat := 4983230072969 + 3 ^ 40 * 638273 * 2
def baseEnd_638273 : Nat := 291325189144254655690793

theorem tailTrace_638273 : CollatzResearch.WordTrace tailWord_638273 prefixEnd_638273 291325189144254655690793 := by
  unfold tailWord_638273
  simp only [CollatzResearch.WordTrace]
  refine ⟨23279728816653404194911473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15519819211102269463274315 23279728816653404194911473)
  ·
    refine ⟨17459796612490053146183605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23279728816653404194911473 17459796612490053146183605)
    ·
      refine ⟨1636855932420942482454713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17459796612490053146183605 1636855932420942482454713)
      ·
        refine ⟨1227641949315706861841035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636855932420942482454713 1227641949315706861841035)
        ·
          refine ⟨1841462923973560292761553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227641949315706861841035 1841462923973560292761553)
          ·
            refine ⟨1381097192980170219571165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841462923973560292761553 1381097192980170219571165)
            ·
              refine ⟨517911447367563832339187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1381097192980170219571165 517911447367563832339187)
              ·
                refine ⟨776867171051345748508781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517911447367563832339187 776867171051345748508781)
                ·
                  refine ⟨291325189144254655690793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776867171051345748508781 291325189144254655690793)
                  ·
                    rfl

theorem cell20_638273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_638273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638273 prefixEnd_638273 := by exact prefixLift 638273
  have htrace : WordTrace (prefixWord ++ tailWord_638273) baseStart_638273 baseEnd_638273 := by
    simpa [prefixWord, tailWord_638273, baseEnd_638273] using wordTrace_append hprefix tailTrace_638273
  have hstable : (prefixWord ++ tailWord_638273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638273).length < 2 ^ (prefixWord ++ tailWord_638273).sum := by decide
  have hdescent : baseEnd_638273 < baseStart_638273 := by decide
  rcases family_descends (prefixWord ++ tailWord_638273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
