import V185TrunkScan23Chunk0381

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2258542 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_2258542 : Nat := 118140960795 + 2258542 * 2 ^ 59
def prefixEnd_2258542 : Nat := 4983230072969 + 3 ^ 40 * 2258542 * 2
def baseEnd_2258542 : Nat := 1159717624367007677738161

theorem tailTrace_2258542 : CollatzResearch.WordTrace tailWord_2258542 prefixEnd_2258542 1159717624367007677738161 := by
  unfold tailWord_2258542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296974272961942138664235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54917196122463691406209253 10296974272961942138664235)
  ·
    refine ⟨15445461409442913207996353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10296974272961942138664235 15445461409442913207996353)
    ·
      refine ⟨11584096057082184905997265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15445461409442913207996353 11584096057082184905997265)
      ·
        refine ⟨8688072042811638679497949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11584096057082184905997265 8688072042811638679497949)
        ·
          refine ⟨3258027016054364504811731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8688072042811638679497949 3258027016054364504811731)
          ·
            refine ⟨4887040524081546757217597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258027016054364504811731 4887040524081546757217597)
            ·
              refine ⟨1832640196530580033956599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4887040524081546757217597 1832640196530580033956599)
              ·
                refine ⟨2748960294795870050934899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832640196530580033956599 2748960294795870050934899)
                ·
                  refine ⟨4123440442193805076402349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748960294795870050934899 4123440442193805076402349)
                  ·
                    refine ⟨1546290165822676903650881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4123440442193805076402349 1546290165822676903650881)
                    ·
                      refine ⟨1159717624367007677738161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546290165822676903650881 1159717624367007677738161)
                      ·
                        rfl

theorem cell23_2258542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_2258542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258542 prefixEnd_2258542 := by exact prefixLift 2258542
  have htrace : WordTrace (prefixWord ++ tailWord_2258542) baseStart_2258542 baseEnd_2258542 := by
    simpa [prefixWord, tailWord_2258542, baseEnd_2258542] using wordTrace_append hprefix tailTrace_2258542
  have hstable : (prefixWord ++ tailWord_2258542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258542).length < 2 ^ (prefixWord ++ tailWord_2258542).sum := by decide
  have hdescent : baseEnd_2258542 < baseStart_2258542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258547 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_2258547 : Nat := 118140960795 + 2258547 * 2 ^ 59
def prefixEnd_2258547 : Nat := 4983230072969 + 3 ^ 40 * 2258547 * 2
def baseEnd_2258547 : Nat := 1159720191770280158175637

theorem tailTrace_2258547 : CollatzResearch.WordTrace tailWord_2258547 prefixEnd_2258547 1159720191770280158175637 := by
  unfold tailWord_2258547
  simp only [CollatzResearch.WordTrace]
  refine ⟨82375976548677422963245895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54917317699118281975497263 82375976548677422963245895)
  ·
    refine ⟨123563964823016134444868843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82375976548677422963245895 123563964823016134444868843)
    ·
      refine ⟨185345947234524201667303265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123563964823016134444868843 185345947234524201667303265)
      ·
        refine ⟨139009460425893151250477449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185345947234524201667303265 139009460425893151250477449)
        ·
          refine ⟨104257095319419863437858087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139009460425893151250477449 104257095319419863437858087)
          ·
            refine ⟨156385642979129795156787131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104257095319419863437858087 156385642979129795156787131)
            ·
              refine ⟨234578464468694692735180697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156385642979129795156787131 234578464468694692735180697)
              ·
                refine ⟨175933848351521019551385523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234578464468694692735180697 175933848351521019551385523)
                ·
                  refine ⟨263900772527281529327078285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175933848351521019551385523 263900772527281529327078285)
                  ·
                    refine ⟨98962789697730573497654357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 263900772527281529327078285 98962789697730573497654357)
                    ·
                      refine ⟨1159720191770280158175637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98962789697730573497654357 1159720191770280158175637)
                      ·
                        rfl

theorem cell23_2258547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_2258547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258547 prefixEnd_2258547 := by exact prefixLift 2258547
  have htrace : WordTrace (prefixWord ++ tailWord_2258547) baseStart_2258547 baseEnd_2258547 := by
    simpa [prefixWord, tailWord_2258547, baseEnd_2258547] using wordTrace_append hprefix tailTrace_2258547
  have hstable : (prefixWord ++ tailWord_2258547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258547).length < 2 ^ (prefixWord ++ tailWord_2258547).sum := by decide
  have hdescent : baseEnd_2258547 < baseStart_2258547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258568 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2258568 : Nat := 118140960795 + 2258568 * 2 ^ 59
def prefixEnd_2258568 : Nat := 4983230072969 + 3 ^ 40 * 2258568 * 2
def baseEnd_2258568 : Nat := 1159730974864024576013041

theorem tailTrace_2258568 : CollatzResearch.WordTrace tailWord_2258568 prefixEnd_2258568 1159730974864024576013041 := by
  unfold tailWord_2258568
  simp only [CollatzResearch.WordTrace]
  refine ⟨41188371240800671774880179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54917828321067562366506905 41188371240800671774880179)
  ·
    refine ⟨61782556861201007662320269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41188371240800671774880179 61782556861201007662320269)
    ·
      refine ⟨23168458822950377873370101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61782556861201007662320269 23168458822950377873370101)
      ·
        refine ⟨2172043014651597925628447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23168458822950377873370101 2172043014651597925628447)
        ·
          refine ⟨3258064521977396888442671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172043014651597925628447 3258064521977396888442671)
          ·
            refine ⟨4887096782966095332664007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258064521977396888442671 4887096782966095332664007)
            ·
              refine ⟨7330645174449142998996011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887096782966095332664007 7330645174449142998996011)
              ·
                refine ⟨10995967761673714498494017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7330645174449142998996011 10995967761673714498494017)
                ·
                  refine ⟨8246975821255285873870513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10995967761673714498494017 8246975821255285873870513)
                  ·
                    refine ⟨6185231865941464405402885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8246975821255285873870513 6185231865941464405402885)
                    ·
                      refine ⟨1159730974864024576013041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6185231865941464405402885 1159730974864024576013041)
                      ·
                        rfl

theorem cell23_2258568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2258568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258568 prefixEnd_2258568 := by exact prefixLift 2258568
  have htrace : WordTrace (prefixWord ++ tailWord_2258568) baseStart_2258568 baseEnd_2258568 := by
    simpa [prefixWord, tailWord_2258568, baseEnd_2258568] using wordTrace_append hprefix tailTrace_2258568
  have hstable : (prefixWord ++ tailWord_2258568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258568).length < 2 ^ (prefixWord ++ tailWord_2258568).sum := by decide
  have hdescent : baseEnd_2258568 < baseStart_2258568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258606 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2258606 : Nat := 118140960795 + 2258606 * 2 ^ 59
def prefixEnd_2258606 : Nat := 4983230072969 + 3 ^ 40 * 2258606 * 2
def baseEnd_2258606 : Nat := 1159750487128895427337867

theorem tailTrace_2258606 : CollatzResearch.WordTrace tailWord_2258606 prefixEnd_2258606 1159750487128895427337867 := by
  unfold tailWord_2258606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297266056932959504955459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54918752303642450693095781 10297266056932959504955459)
  ·
    refine ⟨15445899085399439257433189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10297266056932959504955459 15445899085399439257433189)
    ·
      refine ⟨2896106078512394860768723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15445899085399439257433189 2896106078512394860768723)
      ·
        refine ⟨4344159117768592291153085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896106078512394860768723 4344159117768592291153085)
        ·
          refine ⟨1629059669163222109182407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4344159117768592291153085 1629059669163222109182407)
          ·
            refine ⟨2443589503744833163773611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629059669163222109182407 2443589503744833163773611)
            ·
              refine ⟨3665384255617249745660417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443589503744833163773611 3665384255617249745660417)
              ·
                refine ⟨2749038191712937309245313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665384255617249745660417 2749038191712937309245313)
                ·
                  refine ⟨2061778643784702981933985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2749038191712937309245313 2061778643784702981933985)
                  ·
                    refine ⟨1546333982838527236450489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061778643784702981933985 1546333982838527236450489)
                    ·
                      refine ⟨1159750487128895427337867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546333982838527236450489 1159750487128895427337867)
                      ·
                        rfl

theorem cell23_2258606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2258606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258606 prefixEnd_2258606 := by exact prefixLift 2258606
  have htrace : WordTrace (prefixWord ++ tailWord_2258606) baseStart_2258606 baseEnd_2258606 := by
    simpa [prefixWord, tailWord_2258606, baseEnd_2258606] using wordTrace_append hprefix tailTrace_2258606
  have hstable : (prefixWord ++ tailWord_2258606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258606).length < 2 ^ (prefixWord ++ tailWord_2258606).sum := by decide
  have hdescent : baseEnd_2258606 < baseStart_2258606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258611 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 4, 2]
def baseStart_2258611 : Nat := 118140960795 + 2258611 * 2 ^ 59
def prefixEnd_2258611 : Nat := 4983230072969 + 3 ^ 40 * 2258611 * 2
def baseEnd_2258611 : Nat := 1159753054532167907775343

theorem tailTrace_2258611 : CollatzResearch.WordTrace tailWord_2258611 prefixEnd_2258611 1159753054532167907775343 := by
  unfold tailWord_2258611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82378310820445561893575687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54918873880297041262383791 82378310820445561893575687)
  ·
    refine ⟨123567466230668342840363531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82378310820445561893575687 123567466230668342840363531)
    ·
      refine ⟨185351199346002514260545297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123567466230668342840363531 185351199346002514260545297)
      ·
        refine ⟨139013399509501885695408973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185351199346002514260545297 139013399509501885695408973)
        ·
          refine ⟨52130024816063207135778365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139013399509501885695408973 52130024816063207135778365)
          ·
            refine ⟨19548759306023702675916887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52130024816063207135778365 19548759306023702675916887)
            ·
              refine ⟨29323138959035554013875331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19548759306023702675916887 29323138959035554013875331)
              ·
                refine ⟨43984708438553331020812997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29323138959035554013875331 43984708438553331020812997)
                ·
                  refine ⟨8247132832228749566402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43984708438553331020812997 8247132832228749566402437)
                  ·
                    refine ⟨1546337406042890543700457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8247132832228749566402437 1546337406042890543700457)
                    ·
                      refine ⟨1159753054532167907775343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546337406042890543700457 1159753054532167907775343)
                      ·
                        rfl

theorem cell23_2258611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4, 2].length) (baseStart_2258611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258611 prefixEnd_2258611 := by exact prefixLift 2258611
  have htrace : WordTrace (prefixWord ++ tailWord_2258611) baseStart_2258611 baseEnd_2258611 := by
    simpa [prefixWord, tailWord_2258611, baseEnd_2258611] using wordTrace_append hprefix tailTrace_2258611
  have hstable : (prefixWord ++ tailWord_2258611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258611).length < 2 ^ (prefixWord ++ tailWord_2258611).sum := by decide
  have hdescent : baseEnd_2258611 < baseStart_2258611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258624 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2258624 : Nat := 118140960795 + 2258624 * 2 ^ 59
def prefixEnd_2258624 : Nat := 4983230072969 + 3 ^ 40 * 2258624 * 2
def baseEnd_2258624 : Nat := 1159759729780676356912783

theorem tailTrace_2258624 : CollatzResearch.WordTrace tailWord_2258624 prefixEnd_2258624 1159759729780676356912783 := by
  unfold tailWord_2258624
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189392484699232556899463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54919189979598976742532617 41189392484699232556899463)
  ·
    refine ⟨61784088727048848835349195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41189392484699232556899463 61784088727048848835349195)
    ·
      refine ⟨92676133090573273253023793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61784088727048848835349195 92676133090573273253023793)
      ·
        refine ⟨69507099817929954939767845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92676133090573273253023793 69507099817929954939767845)
        ·
          refine ⟨13032581215861866551206471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69507099817929954939767845 13032581215861866551206471)
          ·
            refine ⟨19548871823792799826809707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032581215861866551206471 19548871823792799826809707)
            ·
              refine ⟨29323307735689199740214561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19548871823792799826809707 29323307735689199740214561)
              ·
                refine ⟨21992480801766899805160921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29323307735689199740214561 21992480801766899805160921)
                ·
                  refine ⟨16494360601325174853870691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21992480801766899805160921 16494360601325174853870691)
                  ·
                    refine ⟨24741540901987762280806037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16494360601325174853870691 24741540901987762280806037)
                    ·
                      refine ⟨1159759729780676356912783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24741540901987762280806037 1159759729780676356912783)
                      ·
                        rfl

theorem cell23_2258624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2258624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258624 prefixEnd_2258624 := by exact prefixLift 2258624
  have htrace : WordTrace (prefixWord ++ tailWord_2258624) baseStart_2258624 baseEnd_2258624 := by
    simpa [prefixWord, tailWord_2258624, baseEnd_2258624] using wordTrace_append hprefix tailTrace_2258624
  have hstable : (prefixWord ++ tailWord_2258624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258624).length < 2 ^ (prefixWord ++ tailWord_2258624).sum := by decide
  have hdescent : baseEnd_2258624 < baseStart_2258624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258628 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2258628 : Nat := 118140960795 + 2258628 * 2 ^ 59
def prefixEnd_2258628 : Nat := 4983230072969 + 3 ^ 40 * 2258628 * 2
def baseEnd_2258628 : Nat := 1159761783703294341262765

theorem tailTrace_2258628 : CollatzResearch.WordTrace tailWord_2258628 prefixEnd_2258628 1159761783703294341262765 := by
  unfold tailWord_2258628
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189465430691986898472269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54919287240922649197963025 41189465430691986898472269)
  ·
    refine ⟨15446049536509495086927101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41189465430691986898472269 15446049536509495086927101)
    ·
      refine ⟨5792268576191060657597663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15446049536509495086927101 5792268576191060657597663)
      ·
        refine ⟨8688402864286590986396495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792268576191060657597663 8688402864286590986396495)
        ·
          refine ⟨13032604296429886479594743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688402864286590986396495 13032604296429886479594743)
          ·
            refine ⟨19548906444644829719392115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032604296429886479594743 19548906444644829719392115)
            ·
              refine ⟨29323359666967244579088173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19548906444644829719392115 29323359666967244579088173)
              ·
                refine ⟨10996259875112716717158065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29323359666967244579088173 10996259875112716717158065)
                ·
                  refine ⟨8247194906334537537868549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10996259875112716717158065 8247194906334537537868549)
                  ·
                    refine ⟨1546349044937725788350353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8247194906334537537868549 1546349044937725788350353)
                    ·
                      refine ⟨1159761783703294341262765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546349044937725788350353 1159761783703294341262765)
                      ·
                        rfl

theorem cell23_2258628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2258628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258628 prefixEnd_2258628 := by exact prefixLift 2258628
  have htrace : WordTrace (prefixWord ++ tailWord_2258628) baseStart_2258628 baseEnd_2258628 := by
    simpa [prefixWord, tailWord_2258628, baseEnd_2258628] using wordTrace_append hprefix tailTrace_2258628
  have hstable : (prefixWord ++ tailWord_2258628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258628).length < 2 ^ (prefixWord ++ tailWord_2258628).sum := by decide
  have hdescent : baseEnd_2258628 < baseStart_2258628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258698 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_2258698 : Nat := 118140960795 + 2258698 * 2 ^ 59
def prefixEnd_2258698 : Nat := 4983230072969 + 3 ^ 40 * 2258698 * 2
def baseEnd_2258698 : Nat := 386599242449703022462481

theorem tailTrace_2258698 : CollatzResearch.WordTrace tailWord_2258698 prefixEnd_2258698 386599242449703022462481 := by
  unfold tailWord_2258698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20595370992782593937998187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54920989314086917167995165 20595370992782593937998187)
  ·
    refine ⟨30893056489173890906997281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20595370992782593937998187 30893056489173890906997281)
    ·
      refine ⟨23169792366880418180247961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30893056489173890906997281 23169792366880418180247961)
      ·
        refine ⟨17377344275160313635185971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23169792366880418180247961 17377344275160313635185971)
        ·
          refine ⟨26066016412740470452778957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17377344275160313635185971 26066016412740470452778957)
          ·
            refine ⟨9774756154777676419792109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26066016412740470452778957 9774756154777676419792109)
            ·
              refine ⟨3665533558041628657422041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9774756154777676419792109 3665533558041628657422041)
              ·
                refine ⟨2749150168531221493066531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665533558041628657422041 2749150168531221493066531)
                ·
                  refine ⟨4123725252796832239599797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749150168531221493066531 4123725252796832239599797)
                  ·
                    refine ⟨386599242449703022462481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4123725252796832239599797 386599242449703022462481)
                    ·
                      rfl

theorem cell23_2258698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_2258698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258698 prefixEnd_2258698 := by exact prefixLift 2258698
  have htrace : WordTrace (prefixWord ++ tailWord_2258698) baseStart_2258698 baseEnd_2258698 := by
    simpa [prefixWord, tailWord_2258698, baseEnd_2258698] using wordTrace_append hprefix tailTrace_2258698
  have hstable : (prefixWord ++ tailWord_2258698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258698).length < 2 ^ (prefixWord ++ tailWord_2258698).sum := by decide
  have hdescent : baseEnd_2258698 < baseStart_2258698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258711 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 6]
def baseStart_2258711 : Nat := 118140960795 + 2258711 * 2 ^ 59
def prefixEnd_2258711 : Nat := 4983230072969 + 3 ^ 40 * 2258711 * 2
def baseEnd_2258711 : Nat := 386601467532539172174961

theorem tailTrace_2258711 : CollatzResearch.WordTrace tailWord_2258711 prefixEnd_2258711 386601467532539172174961 := by
  unfold tailWord_2258711
  simp only [CollatzResearch.WordTrace]
  refine ⟨82381958120083278972215987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54921305413388852648143991 82381958120083278972215987)
  ·
    refine ⟨123572937180124918458323981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82381958120083278972215987 123572937180124918458323981)
    ·
      refine ⟨46339851442546844421871493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123572937180124918458323981 46339851442546844421871493)
      ·
        refine ⟨8688722145477533329100905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46339851442546844421871493 8688722145477533329100905)
        ·
          refine ⟨6516541609108149996825679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8688722145477533329100905 6516541609108149996825679)
          ·
            refine ⟨9774812413662224995238519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516541609108149996825679 9774812413662224995238519)
            ·
              refine ⟨14662218620493337492857779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774812413662224995238519 14662218620493337492857779)
              ·
                refine ⟨21993327930740006239286669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14662218620493337492857779 21993327930740006239286669)
                ·
                  refine ⟨8247497974027502339732501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21993327930740006239286669 8247497974027502339732501)
                  ·
                    refine ⟨386601467532539172174961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8247497974027502339732501 386601467532539172174961)
                    ·
                      rfl

theorem cell23_2258711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_2258711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258711 prefixEnd_2258711 := by exact prefixLift 2258711
  have htrace : WordTrace (prefixWord ++ tailWord_2258711) baseStart_2258711 baseEnd_2258711 := by
    simpa [prefixWord, tailWord_2258711, baseEnd_2258711] using wordTrace_append hprefix tailTrace_2258711
  have hstable : (prefixWord ++ tailWord_2258711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258711).length < 2 ^ (prefixWord ++ tailWord_2258711).sum := by decide
  have hdescent : baseEnd_2258711 < baseStart_2258711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258738 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2258738 : Nat := 118140960795 + 2258738 * 2 ^ 59
def prefixEnd_2258738 : Nat := 4983230072969 + 3 ^ 40 * 2258738 * 2
def baseEnd_2258738 : Nat := 1159818266575288910887259

theorem tailTrace_2258738 : CollatzResearch.WordTrace tailWord_2258738 prefixEnd_2258738 1159818266575288910887259 := by
  unfold tailWord_2258738
  simp only [CollatzResearch.WordTrace]
  refine ⟨20595735722746365645862217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54921961927323641722299245 20595735722746365645862217)
  ·
    refine ⟨15446801792059774234396663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20595735722746365645862217 15446801792059774234396663)
    ·
      refine ⟨23170202688089661351594995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15446801792059774234396663 23170202688089661351594995)
      ·
        refine ⟨34755304032134492027392493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23170202688089661351594995 34755304032134492027392493)
        ·
          refine ⟨13033239012050434510272185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34755304032134492027392493 13033239012050434510272185)
          ·
            refine ⟨9774929259037825882704139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13033239012050434510272185 9774929259037825882704139)
            ·
              refine ⟨14662393888556738824056209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774929259037825882704139 14662393888556738824056209)
              ·
                refine ⟨10996795416417554118042157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14662393888556738824056209 10996795416417554118042157)
                ·
                  refine ⟨4123798281156582794265809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10996795416417554118042157 4123798281156582794265809)
                  ·
                    refine ⟨3092848710867437095699357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123798281156582794265809 3092848710867437095699357)
                    ·
                      refine ⟨1159818266575288910887259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3092848710867437095699357 1159818266575288910887259)
                      ·
                        rfl

theorem cell23_2258738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2258738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258738 prefixEnd_2258738 := by exact prefixLift 2258738
  have htrace : WordTrace (prefixWord ++ tailWord_2258738) baseStart_2258738 baseEnd_2258738 := by
    simpa [prefixWord, tailWord_2258738, baseEnd_2258738] using wordTrace_append hprefix tailTrace_2258738
  have hstable : (prefixWord ++ tailWord_2258738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258738).length < 2 ^ (prefixWord ++ tailWord_2258738).sum := by decide
  have hdescent : baseEnd_2258738 < baseStart_2258738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258745 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_2258745 : Nat := 118140960795 + 2258745 * 2 ^ 59
def prefixEnd_2258745 : Nat := 4983230072969 + 3 ^ 40 * 2258745 * 2
def baseEnd_2258745 : Nat := 386607286979956794499909

theorem tailTrace_2258745 : CollatzResearch.WordTrace tailWord_2258745 prefixEnd_2258745 386607286979956794499909 := by
  unfold tailWord_2258745
  simp only [CollatzResearch.WordTrace]
  refine ⟨82383198201960102778953689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54922132134640068519302459 82383198201960102778953689)
  ·
    refine ⟨61787398651470077084215267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82383198201960102778953689 61787398651470077084215267)
    ·
      refine ⟨92681097977205115626322901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61787398651470077084215267 92681097977205115626322901)
      ·
        refine ⟨2172213233840744897491943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 92681097977205115626322901 2172213233840744897491943)
        ·
          refine ⟨3258319850761117346237915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172213233840744897491943 3258319850761117346237915)
          ·
            refine ⟨4887479776141676019356873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258319850761117346237915 4887479776141676019356873)
            ·
              refine ⟨3665609832106257014517655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887479776141676019356873 3665609832106257014517655)
              ·
                refine ⟨5498414748159385521776483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665609832106257014517655 5498414748159385521776483)
                ·
                  refine ⟨8247622122239078282664725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498414748159385521776483 8247622122239078282664725)
                  ·
                    refine ⟨386607286979956794499909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8247622122239078282664725 386607286979956794499909)
                    ·
                      rfl

theorem cell23_2258745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_2258745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258745 prefixEnd_2258745 := by exact prefixLift 2258745
  have htrace : WordTrace (prefixWord ++ tailWord_2258745) baseStart_2258745 baseEnd_2258745 := by
    simpa [prefixWord, tailWord_2258745, baseEnd_2258745] using wordTrace_append hprefix tailTrace_2258745
  have hstable : (prefixWord ++ tailWord_2258745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258745).length < 2 ^ (prefixWord ++ tailWord_2258745).sum := by decide
  have hdescent : baseEnd_2258745 < baseStart_2258745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258765 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2258765 : Nat := 118140960795 + 2258765 * 2 ^ 59
def prefixEnd_2258765 : Nat := 4983230072969 + 3 ^ 40 * 2258765 * 2
def baseEnd_2258765 : Nat := 1159832130552960305249635

theorem tailTrace_2258765 : CollatzResearch.WordTrace tailWord_2258765 prefixEnd_2258765 1159832130552960305249635 := by
  unfold tailWord_2258765
  simp only [CollatzResearch.WordTrace]
  refine ⟨82383927661887646194681749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54922618441258430796454499 82383927661887646194681749)
  ·
    refine ⟨3861746609150983415375707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82383927661887646194681749 3861746609150983415375707)
    ·
      refine ⟨5792619913726475123063561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861746609150983415375707 5792619913726475123063561)
      ·
        refine ⟨4344464935294856342297671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792619913726475123063561 4344464935294856342297671)
        ·
          refine ⟨6516697402942284513446507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344464935294856342297671 6516697402942284513446507)
          ·
            refine ⟨9775046104413426770169761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516697402942284513446507 9775046104413426770169761)
            ·
              refine ⟨7331284578310070077627321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9775046104413426770169761 7331284578310070077627321)
              ·
                refine ⟨5498463433732552558220491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7331284578310070077627321 5498463433732552558220491)
                ·
                  refine ⟨8247695150598828837330737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498463433732552558220491 8247695150598828837330737)
                  ·
                    refine ⟨6185771362949121627998053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8247695150598828837330737 6185771362949121627998053)
                    ·
                      refine ⟨1159832130552960305249635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6185771362949121627998053 1159832130552960305249635)
                      ·
                        rfl

theorem cell23_2258765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2258765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258765 prefixEnd_2258765 := by exact prefixLift 2258765
  have htrace : WordTrace (prefixWord ++ tailWord_2258765) baseStart_2258765 baseEnd_2258765 := by
    simpa [prefixWord, tailWord_2258765, baseEnd_2258765] using wordTrace_append hprefix tailTrace_2258765
  have hstable : (prefixWord ++ tailWord_2258765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258765).length < 2 ^ (prefixWord ++ tailWord_2258765).sum := by decide
  have hdescent : baseEnd_2258765 < baseStart_2258765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258768 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_2258768 : Nat := 118140960795 + 2258768 * 2 ^ 59
def prefixEnd_2258768 : Nat := 4983230072969 + 3 ^ 40 * 2258768 * 2
def baseEnd_2258768 : Nat := 1159833670994923793512121

theorem tailTrace_2258768 : CollatzResearch.WordTrace tailWord_2258768 prefixEnd_2258768 1159833670994923793512121 := by
  unfold tailWord_2258768
  simp only [CollatzResearch.WordTrace]
  refine ⟨41192018540438388853520479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54922691387251185138027305 41192018540438388853520479)
  ·
    refine ⟨61788027810657583280280719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41192018540438388853520479 61788027810657583280280719)
    ·
      refine ⟨92682041715986374920421079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61788027810657583280280719 92682041715986374920421079)
      ·
        refine ⟨139023062573979562380631619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92682041715986374920421079 139023062573979562380631619)
        ·
          refine ⟨208534593860969343570947429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139023062573979562380631619 208534593860969343570947429)
          ·
            refine ⟨39100236348931751919552643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208534593860969343570947429 39100236348931751919552643)
            ·
              refine ⟨58650354523397627879328965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39100236348931751919552643 58650354523397627879328965)
              ·
                refine ⟨10996941473137055227374181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58650354523397627879328965 10996941473137055227374181)
                ·
                  refine ⟨2061926526213197855132659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10996941473137055227374181 2061926526213197855132659)
                  ·
                    refine ⟨3092889789319796782698989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2061926526213197855132659 3092889789319796782698989)
                    ·
                      refine ⟨1159833670994923793512121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3092889789319796782698989 1159833670994923793512121)
                      ·
                        rfl

theorem cell23_2258768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_2258768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258768 prefixEnd_2258768 := by exact prefixLift 2258768
  have htrace : WordTrace (prefixWord ++ tailWord_2258768) baseStart_2258768 baseEnd_2258768 := by
    simpa [prefixWord, tailWord_2258768, baseEnd_2258768] using wordTrace_append hprefix tailTrace_2258768
  have hstable : (prefixWord ++ tailWord_2258768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258768).length < 2 ^ (prefixWord ++ tailWord_2258768).sum := by decide
  have hdescent : baseEnd_2258768 < baseStart_2258768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258769 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_2258769 : Nat := 118140960795 + 2258769 * 2 ^ 59
def prefixEnd_2258769 : Nat := 4983230072969 + 3 ^ 40 * 2258769 * 2
def baseEnd_2258769 : Nat := 1159834184475578289599617

theorem tailTrace_2258769 : CollatzResearch.WordTrace tailWord_2258769 prefixEnd_2258769 1159834184475578289599617 := by
  unfold tailWord_2258769
  simp only [CollatzResearch.WordTrace]
  refine ⟨82384073553873154877827361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54922715702582103251884907 82384073553873154877827361)
  ·
    refine ⟨61788055165404866158370521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82384073553873154877827361 61788055165404866158370521)
    ·
      refine ⟨46341041374053649618777891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61788055165404866158370521 46341041374053649618777891)
      ·
        refine ⟨69511562061080474428166837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46341041374053649618777891 69511562061080474428166837)
        ·
          refine ⟨6516708943226294477640641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69511562061080474428166837 6516708943226294477640641)
          ·
            refine ⟨4887531707419720858230481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6516708943226294477640641 4887531707419720858230481)
            ·
              refine ⟨3665648780564790643672861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887531707419720858230481 3665648780564790643672861)
              ·
                refine ⟨1374618292711796491377323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665648780564790643672861 1374618292711796491377323)
                ·
                  refine ⟨2061927439067694737065985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374618292711796491377323 2061927439067694737065985)
                  ·
                    refine ⟨1546445579300771052799489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061927439067694737065985 1546445579300771052799489)
                    ·
                      refine ⟨1159834184475578289599617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546445579300771052799489 1159834184475578289599617)
                      ·
                        rfl

theorem cell23_2258769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_2258769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258769 prefixEnd_2258769 := by exact prefixLift 2258769
  have htrace : WordTrace (prefixWord ++ tailWord_2258769) baseStart_2258769 baseEnd_2258769 := by
    simpa [prefixWord, tailWord_2258769, baseEnd_2258769] using wordTrace_append hprefix tailTrace_2258769
  have hstable : (prefixWord ++ tailWord_2258769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258769).length < 2 ^ (prefixWord ++ tailWord_2258769).sum := by decide
  have hdescent : baseEnd_2258769 < baseStart_2258769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258772 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_2258772 : Nat := 118140960795 + 2258772 * 2 ^ 59
def prefixEnd_2258772 : Nat := 4983230072969 + 3 ^ 40 * 2258772 * 2
def baseEnd_2258772 : Nat := 1159835724917541777862103

theorem tailTrace_2258772 : CollatzResearch.WordTrace tailWord_2258772 prefixEnd_2258772 1159835724917541777862103 := by
  unfold tailWord_2258772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41192091486431143195093285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54922788648574857593457713 41192091486431143195093285)
  ·
    refine ⟨7723517153705839349079991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41192091486431143195093285 7723517153705839349079991)
    ·
      refine ⟨11585275730558759023619987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7723517153705839349079991 11585275730558759023619987)
      ·
        refine ⟨17377913595838138535429981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11585275730558759023619987 17377913595838138535429981)
        ·
          refine ⟨6516717598439301950786243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17377913595838138535429981 6516717598439301950786243)
          ·
            refine ⟨9775076397658952926179365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516717598439301950786243 9775076397658952926179365)
            ·
              refine ⟨1832826824561053673658631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9775076397658952926179365 1832826824561053673658631)
              ·
                refine ⟨2749240236841580510487947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832826824561053673658631 2749240236841580510487947)
                ·
                  refine ⟨4123860355262370765731921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749240236841580510487947 4123860355262370765731921)
                  ·
                    refine ⟨3092895266446778074298941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123860355262370765731921 3092895266446778074298941)
                    ·
                      refine ⟨1159835724917541777862103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3092895266446778074298941 1159835724917541777862103)
                      ·
                        rfl

theorem cell23_2258772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_2258772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258772 prefixEnd_2258772 := by exact prefixLift 2258772
  have htrace : WordTrace (prefixWord ++ tailWord_2258772) baseStart_2258772 baseEnd_2258772 := by
    simpa [prefixWord, tailWord_2258772, baseEnd_2258772] using wordTrace_append hprefix tailTrace_2258772
  have hstable : (prefixWord ++ tailWord_2258772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258772).length < 2 ^ (prefixWord ++ tailWord_2258772).sum := by decide
  have hdescent : baseEnd_2258772 < baseStart_2258772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258801 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_2258801 : Nat := 118140960795 + 2258801 * 2 ^ 59
def prefixEnd_2258801 : Nat := 4983230072969 + 3 ^ 40 * 2258801 * 2
def baseEnd_2258801 : Nat := 386616871952174054799823

theorem tailTrace_2258801 : CollatzResearch.WordTrace tailWord_2258801 prefixEnd_2258801 386616871952174054799823 := by
  unfold tailWord_2258801
  simp only [CollatzResearch.WordTrace]
  refine ⟨82385240689757224342992257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54923493793171482895328171 82385240689757224342992257)
  ·
    refine ⟨61788930517317918257244193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82385240689757224342992257 61788930517317918257244193)
    ·
      refine ⟨46341697887988438692933145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61788930517317918257244193 46341697887988438692933145)
      ·
        refine ⟨34756273415991329019699859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46341697887988438692933145 34756273415991329019699859)
        ·
          refine ⟨52134410123986993529549789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34756273415991329019699859 52134410123986993529549789)
          ·
            refine ⟨19550403796495122573581171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52134410123986993529549789 19550403796495122573581171)
            ·
              refine ⟨29325605694742683860371757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19550403796495122573581171 29325605694742683860371757)
              ·
                refine ⟨10997102135528506447639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29325605694742683860371757 10997102135528506447639409)
                ·
                  refine ⟨8247826601646379835729557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997102135528506447639409 8247826601646379835729557)
                  ·
                    refine ⟨386616871952174054799823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8247826601646379835729557 386616871952174054799823)
                    ·
                      rfl

theorem cell23_2258801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_2258801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258801 prefixEnd_2258801 := by exact prefixLift 2258801
  have htrace : WordTrace (prefixWord ++ tailWord_2258801) baseStart_2258801 baseEnd_2258801 := by
    simpa [prefixWord, tailWord_2258801, baseEnd_2258801] using wordTrace_append hprefix tailTrace_2258801
  have hstable : (prefixWord ++ tailWord_2258801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258801).length < 2 ^ (prefixWord ++ tailWord_2258801).sum := by decide
  have hdescent : baseEnd_2258801 < baseStart_2258801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258811 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_2258811 : Nat := 118140960795 + 2258811 * 2 ^ 59
def prefixEnd_2258811 : Nat := 4983230072969 + 3 ^ 40 * 2258811 * 2
def baseEnd_2258811 : Nat := 1159855750663067125274423

theorem tailTrace_2258811 : CollatzResearch.WordTrace tailWord_2258811 prefixEnd_2258811 1159855750663067125274423 := by
  unfold tailWord_2258811
  simp only [CollatzResearch.WordTrace]
  refine ⟨82385605419720996050856287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54923736946480664033904191 82385605419720996050856287)
  ·
    refine ⟨123578408129581494076284431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82385605419720996050856287 123578408129581494076284431)
    ·
      refine ⟨185367612194372241114426647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123578408129581494076284431 185367612194372241114426647)
      ·
        refine ⟨278051418291558361671639971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185367612194372241114426647 278051418291558361671639971)
        ·
          refine ⟨417077127437337542507459957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278051418291558361671639971 417077127437337542507459957)
          ·
            refine ⟨39100980697250394610074371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 417077127437337542507459957 39100980697250394610074371)
            ·
              refine ⟨58651471045875591915111557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39100980697250394610074371 58651471045875591915111557)
              ·
                refine ⟨10997150821101673484083417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58651471045875591915111557 10997150821101673484083417)
                ·
                  refine ⟨8247863115826255113062563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997150821101673484083417 8247863115826255113062563)
                  ·
                    refine ⟨12371794673739382669593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8247863115826255113062563 12371794673739382669593845)
                    ·
                      refine ⟨1159855750663067125274423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12371794673739382669593845 1159855750663067125274423)
                      ·
                        rfl

theorem cell23_2258811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_2258811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258811 prefixEnd_2258811 := by exact prefixLift 2258811
  have htrace : WordTrace (prefixWord ++ tailWord_2258811) baseStart_2258811 baseEnd_2258811 := by
    simpa [prefixWord, tailWord_2258811, baseEnd_2258811] using wordTrace_append hprefix tailTrace_2258811
  have hstable : (prefixWord ++ tailWord_2258811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258811).length < 2 ^ (prefixWord ++ tailWord_2258811).sum := by decide
  have hdescent : baseEnd_2258811 < baseStart_2258811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258825 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 6, 2, 2]
def baseStart_2258825 : Nat := 118140960795 + 2258825 * 2 ^ 59
def prefixEnd_2258825 : Nat := 4983230072969 + 3 ^ 40 * 2258825 * 2
def baseEnd_2258825 : Nat := 1159862939392230070499359

theorem tailTrace_2258825 : CollatzResearch.WordTrace tailWord_2258825 prefixEnd_2258825 1159862939392230070499359 := by
  unfold tailWord_2258825
  simp only [CollatzResearch.WordTrace]
  refine ⟨82386116041670276441865929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54924077361113517627910619 82386116041670276441865929)
  ·
    refine ⟨61789587031252707331399447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82386116041670276441865929 61789587031252707331399447)
    ·
      refine ⟨92684380546879060997099171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61789587031252707331399447 92684380546879060997099171)
      ·
        refine ⟨139026570820318591495648757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92684380546879060997099171 139026570820318591495648757)
        ·
          refine ⟨13033741014404867952717071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139026570820318591495648757 13033741014404867952717071)
          ·
            refine ⟨19550611521607301929075607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13033741014404867952717071 19550611521607301929075607)
            ·
              refine ⟨29325917282410952893613411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19550611521607301929075607 29325917282410952893613411)
              ·
                refine ⟨43988875923616429340420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29325917282410952893613411 43988875923616429340420117)
                ·
                  refine ⟨2061978558919520125332193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43988875923616429340420117 2061978558919520125332193)
                  ·
                    refine ⟨1546483919189640093999145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061978558919520125332193 1546483919189640093999145)
                    ·
                      refine ⟨1159862939392230070499359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546483919189640093999145 1159862939392230070499359)
                      ·
                        rfl

theorem cell23_2258825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2, 2].length) (baseStart_2258825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258825 prefixEnd_2258825 := by exact prefixLift 2258825
  have htrace : WordTrace (prefixWord ++ tailWord_2258825) baseStart_2258825 baseEnd_2258825 := by
    simpa [prefixWord, tailWord_2258825, baseEnd_2258825] using wordTrace_append hprefix tailTrace_2258825
  have hstable : (prefixWord ++ tailWord_2258825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258825).length < 2 ^ (prefixWord ++ tailWord_2258825).sum := by decide
  have hdescent : baseEnd_2258825 < baseStart_2258825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258842 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2258842 : Nat := 118140960795 + 2258842 * 2 ^ 59
def prefixEnd_2258842 : Nat := 4983230072969 + 3 ^ 40 * 2258842 * 2
def baseEnd_2258842 : Nat := 1159871668563356503986781

theorem tailTrace_2258842 : CollatzResearch.WordTrace tailWord_2258842 prefixEnd_2258842 1159871668563356503986781 := by
  unfold tailWord_2258842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596684020652172086308695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54924490721739125563489853 20596684020652172086308695)
  ·
    refine ⟨30895026030978258129463043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20596684020652172086308695 30895026030978258129463043)
    ·
      refine ⟨46342539046467387194194565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30895026030978258129463043 46342539046467387194194565)
      ·
        refine ⟨8689226071212635098911481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46342539046467387194194565 8689226071212635098911481)
        ·
          refine ⟨6516919553409476324183611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689226071212635098911481 6516919553409476324183611)
          ·
            refine ⟨9775379330114214486275417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516919553409476324183611 9775379330114214486275417)
            ·
              refine ⟨7331534497585660864706563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9775379330114214486275417 7331534497585660864706563)
              ·
                refine ⟨10997301746378491297059845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7331534497585660864706563 10997301746378491297059845)
                ·
                  refine ⟨2061994077445967118198721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10997301746378491297059845 2061994077445967118198721)
                  ·
                    refine ⟨1546495558084475338649041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061994077445967118198721 1546495558084475338649041)
                    ·
                      refine ⟨1159871668563356503986781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546495558084475338649041 1159871668563356503986781)
                      ·
                        rfl

theorem cell23_2258842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2258842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258842 prefixEnd_2258842 := by exact prefixLift 2258842
  have htrace : WordTrace (prefixWord ++ tailWord_2258842) baseStart_2258842 baseEnd_2258842 := by
    simpa [prefixWord, tailWord_2258842, baseEnd_2258842] using wordTrace_append hprefix tailTrace_2258842
  have hstable : (prefixWord ++ tailWord_2258842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258842).length < 2 ^ (prefixWord ++ tailWord_2258842).sum := by decide
  have hdescent : baseEnd_2258842 < baseStart_2258842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258871 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_2258871 : Nat := 118140960795 + 2258871 * 2 ^ 59
def prefixEnd_2258871 : Nat := 4983230072969 + 3 ^ 40 * 2258871 * 2
def baseEnd_2258871 : Nat := 1159886559502336890524147

theorem tailTrace_2258871 : CollatzResearch.WordTrace tailWord_2258871 prefixEnd_2258871 1159886559502336890524147 := by
  unfold tailWord_2258871
  simp only [CollatzResearch.WordTrace]
  refine ⟨82387793799503626298040467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54925195866335750865360311 82387793799503626298040467)
  ·
    refine ⟨123581690699255439447060701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82387793799503626298040467 123581690699255439447060701)
    ·
      refine ⟨46343134012220789792647763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123581690699255439447060701 46343134012220789792647763)
      ·
        refine ⟨69514701018331184688971645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46343134012220789792647763 69514701018331184688971645)
        ·
          refine ⟨26068012881874194258364367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69514701018331184688971645 26068012881874194258364367)
          ·
            refine ⟨39102019322811291387546551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26068012881874194258364367 39102019322811291387546551)
            ·
              refine ⟨58653028984216937081319827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39102019322811291387546551 58653028984216937081319827)
              ·
                refine ⟨87979543476325405621979741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58653028984216937081319827 87979543476325405621979741)
                ·
                  refine ⟨32992328803622027108242403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87979543476325405621979741 32992328803622027108242403)
                  ·
                    refine ⟨49488493205433040662363605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32992328803622027108242403 49488493205433040662363605)
                    ·
                      refine ⟨1159886559502336890524147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49488493205433040662363605 1159886559502336890524147)
                      ·
                        rfl

theorem cell23_2258871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_2258871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258871 prefixEnd_2258871 := by exact prefixLift 2258871
  have htrace : WordTrace (prefixWord ++ tailWord_2258871) baseStart_2258871 baseEnd_2258871 := by
    simpa [prefixWord, tailWord_2258871, baseEnd_2258871] using wordTrace_append hprefix tailTrace_2258871
  have hstable : (prefixWord ++ tailWord_2258871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258871).length < 2 ^ (prefixWord ++ tailWord_2258871).sum := by decide
  have hdescent : baseEnd_2258871 < baseStart_2258871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258888 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2258888 : Nat := 118140960795 + 2258888 * 2 ^ 59
def prefixEnd_2258888 : Nat := 4983230072969 + 3 ^ 40 * 2258888 * 2
def baseEnd_2258888 : Nat := 1159895288673463324011569

theorem tailTrace_2258888 : CollatzResearch.WordTrace tailWord_2258888 prefixEnd_2258888 1159895288673463324011569 := by
  unfold tailWord_2258888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41194206920221019100704659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54925609226961358800939545 41194206920221019100704659)
  ·
    refine ⟨61791310380331528651056989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41194206920221019100704659 61791310380331528651056989)
    ·
      refine ⟨23171741392624323244146371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61791310380331528651056989 23171741392624323244146371)
      ·
        refine ⟨34757612088936484866219557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23171741392624323244146371 34757612088936484866219557)
        ·
          refine ⟨6517052266675590912416167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34757612088936484866219557 6517052266675590912416167)
          ·
            refine ⟨9775578400013386368624251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6517052266675590912416167 9775578400013386368624251)
            ·
              refine ⟨14663367600020079552936377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9775578400013386368624251 14663367600020079552936377)
              ·
                refine ⟨10997525700015059664702283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14663367600020079552936377 10997525700015059664702283)
                ·
                  refine ⟨16496288550022589497053425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10997525700015059664702283 16496288550022589497053425)
                  ·
                    refine ⟨12372216412516942122790069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16496288550022589497053425 12372216412516942122790069)
                    ·
                      refine ⟨1159895288673463324011569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12372216412516942122790069 1159895288673463324011569)
                      ·
                        rfl

theorem cell23_2258888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2258888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258888 prefixEnd_2258888 := by exact prefixLift 2258888
  have htrace : WordTrace (prefixWord ++ tailWord_2258888) baseStart_2258888 baseEnd_2258888 := by
    simpa [prefixWord, tailWord_2258888, baseEnd_2258888] using wordTrace_append hprefix tailTrace_2258888
  have hstable : (prefixWord ++ tailWord_2258888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258888).length < 2 ^ (prefixWord ++ tailWord_2258888).sum := by decide
  have hdescent : baseEnd_2258888 < baseStart_2258888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258915 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2258915 : Nat := 118140960795 + 2258915 * 2 ^ 59
def prefixEnd_2258915 : Nat := 4983230072969 + 3 ^ 40 * 2258915 * 2
def baseEnd_2258915 : Nat := 1159909152651134718373945

theorem tailTrace_2258915 : CollatzResearch.WordTrace tailWord_2258915 prefixEnd_2258915 1159909152651134718373945 := by
  unfold tailWord_2258915
  simp only [CollatzResearch.WordTrace]
  refine ⟨82389398611344221812642199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54926265740896147875094799 82389398611344221812642199)
  ·
    refine ⟨123584097917016332718963299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82389398611344221812642199 123584097917016332718963299)
    ·
      refine ⟨185376146875524499078444949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123584097917016332718963299 185376146875524499078444949)
      ·
        refine ⟨8689506884790210894302107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185376146875524499078444949 8689506884790210894302107)
        ·
          refine ⟨13034260327185316341453161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8689506884790210894302107 13034260327185316341453161)
          ·
            refine ⟨9775695245388987256089871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13034260327185316341453161 9775695245388987256089871)
            ·
              refine ⟨14663542868083480884134807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9775695245388987256089871 14663542868083480884134807)
              ·
                refine ⟨21995314302125221326202211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14663542868083480884134807 21995314302125221326202211)
                ·
                  refine ⟨32992971453187831989303317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21995314302125221326202211 32992971453187831989303317)
                  ·
                    refine ⟨1546545536868179624498593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32992971453187831989303317 1546545536868179624498593)
                    ·
                      refine ⟨1159909152651134718373945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546545536868179624498593 1159909152651134718373945)
                      ·
                        rfl

theorem cell23_2258915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2258915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258915 prefixEnd_2258915 := by exact prefixLift 2258915
  have htrace : WordTrace (prefixWord ++ tailWord_2258915) baseStart_2258915 baseEnd_2258915 := by
    simpa [prefixWord, tailWord_2258915, baseEnd_2258915] using wordTrace_append hprefix tailTrace_2258915
  have hstable : (prefixWord ++ tailWord_2258915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258915).length < 2 ^ (prefixWord ++ tailWord_2258915).sum := by decide
  have hdescent : baseEnd_2258915 < baseStart_2258915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258958 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2258958 : Nat := 118140960795 + 2258958 * 2 ^ 59
def prefixEnd_2258958 : Nat := 4983230072969 + 3 ^ 40 * 2258958 * 2
def baseEnd_2258958 : Nat := 1159931232319278050136247

theorem tailTrace_2258958 : CollatzResearch.WordTrace tailWord_2258958 prefixEnd_2258958 1159931232319278050136247 := by
  unfold tailWord_2258958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298870868773555019557191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54927311300125626770971685 10298870868773555019557191)
  ·
    refine ⟨15448306303160332529335787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298870868773555019557191 15448306303160332529335787)
    ·
      refine ⟨23172459454740498794003681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15448306303160332529335787 23172459454740498794003681)
      ·
        refine ⟨17379344591055374095502761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23172459454740498794003681 17379344591055374095502761)
        ·
          refine ⟨13034508443291530571627071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17379344591055374095502761 13034508443291530571627071)
          ·
            refine ⟨19551762664937295857440607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13034508443291530571627071 19551762664937295857440607)
            ·
              refine ⟨29327643997405943786160911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19551762664937295857440607 29327643997405943786160911)
              ·
                refine ⟨43991465996108915679241367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29327643997405943786160911 43991465996108915679241367)
                ·
                  refine ⟨65987198994163373518862051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43991465996108915679241367 65987198994163373518862051)
                  ·
                    refine ⟨98980798491245060278293077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65987198994163373518862051 98980798491245060278293077)
                    ·
                      refine ⟨1159931232319278050136247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98980798491245060278293077 1159931232319278050136247)
                      ·
                        rfl

theorem cell23_2258958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2258958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258958 prefixEnd_2258958 := by exact prefixLift 2258958
  have htrace : WordTrace (prefixWord ++ tailWord_2258958) baseStart_2258958 baseEnd_2258958 := by
    simpa [prefixWord, tailWord_2258958, baseEnd_2258958] using wordTrace_append hprefix tailTrace_2258958
  have hstable : (prefixWord ++ tailWord_2258958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258958).length < 2 ^ (prefixWord ++ tailWord_2258958).sum := by decide
  have hdescent : baseEnd_2258958 < baseStart_2258958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258972 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 6]
def baseStart_2258972 : Nat := 118140960795 + 2258972 * 2 ^ 59
def prefixEnd_2258972 : Nat := 4983230072969 + 3 ^ 40 * 2258972 * 2
def baseEnd_2258972 : Nat := 128882046783160110595687

theorem tailTrace_2258972 : CollatzResearch.WordTrace tailWord_2258972 prefixEnd_2258972 128882046783160110595687 := by
  unfold tailWord_2258972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41195738786068860273733585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54927651714758480364978113 41195738786068860273733585)
  ·
    refine ⟨30896804089551645205300189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41195738786068860273733585 30896804089551645205300189)
    ·
      refine ⟨11586301533581866951987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30896804089551645205300189 11586301533581866951987571)
      ·
        refine ⟨17379452300372800427981357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11586301533581866951987571 17379452300372800427981357)
        ·
          refine ⟨6517294612639800160493009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17379452300372800427981357 6517294612639800160493009)
          ·
            refine ⟨4887970959479850120369757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6517294612639800160493009 4887970959479850120369757)
            ·
              refine ⟨1832989109804943795138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4887970959479850120369757 1832989109804943795138659)
              ·
                refine ⟨2749483664707415692707989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832989109804943795138659 2749483664707415692707989)
                ·
                  refine ⟨128882046783160110595687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2749483664707415692707989 128882046783160110595687)
                  ·
                    rfl

theorem cell23_2258972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_2258972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258972 prefixEnd_2258972 := by exact prefixLift 2258972
  have htrace : WordTrace (prefixWord ++ tailWord_2258972) baseStart_2258972 baseEnd_2258972 := by
    simpa [prefixWord, tailWord_2258972, baseEnd_2258972] using wordTrace_append hprefix tailTrace_2258972
  have hstable : (prefixWord ++ tailWord_2258972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258972).length < 2 ^ (prefixWord ++ tailWord_2258972).sum := by decide
  have hdescent : baseEnd_2258972 < baseStart_2258972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258975 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 5, 2]
def baseStart_2258975 : Nat := 118140960795 + 2258975 * 2 ^ 59
def prefixEnd_2258975 : Nat := 4983230072969 + 3 ^ 40 * 2258975 * 2
def baseEnd_2258975 : Nat := 1159939961490404483623669

theorem tailTrace_2258975 : CollatzResearch.WordTrace tailWord_2258975 prefixEnd_2258975 1159939961490404483623669 := by
  unfold tailWord_2258975
  simp only [CollatzResearch.WordTrace]
  refine ⟨82391586991126852059826379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54927724660751234706550919 82391586991126852059826379)
  ·
    refine ⟨123587380486690278089739569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82391586991126852059826379 123587380486690278089739569)
    ·
      refine ⟨92690535365017708567304677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123587380486690278089739569 92690535365017708567304677)
      ·
        refine ⟨17379475380940820356369627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92690535365017708567304677 17379475380940820356369627)
        ·
          refine ⟨26069213071411230534554441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379475380940820356369627 26069213071411230534554441)
          ·
            refine ⟨19551909803558422900915831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26069213071411230534554441 19551909803558422900915831)
            ·
              refine ⟨29327864705337634351373747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19551909803558422900915831 29327864705337634351373747)
              ·
                refine ⟨43991797058006451527060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29327864705337634351373747 43991797058006451527060621)
                ·
                  refine ⟨16496923896752419322647733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43991797058006451527060621 16496923896752419322647733)
                  ·
                    refine ⟨1546586615320539311498225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16496923896752419322647733 1546586615320539311498225)
                    ·
                      refine ⟨1159939961490404483623669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546586615320539311498225 1159939961490404483623669)
                      ·
                        rfl

theorem cell23_2258975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_2258975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258975 prefixEnd_2258975 := by exact prefixLift 2258975
  have htrace : WordTrace (prefixWord ++ tailWord_2258975) baseStart_2258975 baseEnd_2258975 := by
    simpa [prefixWord, tailWord_2258975, baseEnd_2258975] using wordTrace_append hprefix tailTrace_2258975
  have hstable : (prefixWord ++ tailWord_2258975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258975).length < 2 ^ (prefixWord ++ tailWord_2258975).sum := by decide
  have hdescent : baseEnd_2258975 < baseStart_2258975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258999 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_2258999 : Nat := 118140960795 + 2258999 * 2 ^ 59
def prefixEnd_2258999 : Nat := 4983230072969 + 3 ^ 40 * 2258999 * 2
def baseEnd_2258999 : Nat := 1159952285026112389723559

theorem tailTrace_2258999 : CollatzResearch.WordTrace tailWord_2258999 prefixEnd_2258999 1159952285026112389723559 := by
  unfold tailWord_2258999
  simp only [CollatzResearch.WordTrace]
  refine ⟨82392462343039904158700051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54928308228693269439133367 82392462343039904158700051)
  ·
    refine ⟨123588693514559856238050077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82392462343039904158700051 123588693514559856238050077)
    ·
      refine ⟨46345760067959946089268779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123588693514559856238050077 46345760067959946089268779)
      ·
        refine ⟨69518640101939919133903169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46345760067959946089268779 69518640101939919133903169)
        ·
          refine ⟨52138980076454939350427377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69518640101939919133903169 52138980076454939350427377)
          ·
            refine ⟨39104235057341204512820533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52138980076454939350427377 39104235057341204512820533)
            ·
              refine ⟨3666022036625737923076925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39104235057341204512820533 3666022036625737923076925)
              ·
                refine ⟨1374758263734651721153847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3666022036625737923076925 1374758263734651721153847)
                ·
                  refine ⟨2062137395601977581730771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374758263734651721153847 2062137395601977581730771)
                  ·
                    refine ⟨3093206093402966372596157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2062137395601977581730771 3093206093402966372596157)
                    ·
                      refine ⟨1159952285026112389723559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093206093402966372596157 1159952285026112389723559)
                      ·
                        rfl

theorem cell23_2258999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_2258999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258999 prefixEnd_2258999 := by exact prefixLift 2258999
  have htrace : WordTrace (prefixWord ++ tailWord_2258999) baseStart_2258999 baseEnd_2258999 := by
    simpa [prefixWord, tailWord_2258999, baseEnd_2258999] using wordTrace_append hprefix tailTrace_2258999
  have hstable : (prefixWord ++ tailWord_2258999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258999).length < 2 ^ (prefixWord ++ tailWord_2258999).sum := by decide
  have hdescent : baseEnd_2258999 < baseStart_2258999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259009 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2259009 : Nat := 118140960795 + 2259009 * 2 ^ 59
def prefixEnd_2259009 : Nat := 4983230072969 + 3 ^ 40 * 2259009 * 2
def baseEnd_2259009 : Nat := 1159957419832657350598513

theorem tailTrace_2259009 : CollatzResearch.WordTrace tailWord_2259009 prefixEnd_2259009 1159957419832657350598513 := by
  unfold tailWord_2259009
  simp only [CollatzResearch.WordTrace]
  refine ⟨82392827073003675866564081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54928551382002450577709387 82392827073003675866564081)
  ·
    refine ⟨61794620304752756899923061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82392827073003675866564081 61794620304752756899923061)
    ·
      refine ⟨5793245653570570959367787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61794620304752756899923061 5793245653570570959367787)
      ·
        refine ⟨8689868480355856439051681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793245653570570959367787 8689868480355856439051681)
        ·
          refine ⟨6517401360266892329288761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689868480355856439051681 6517401360266892329288761)
          ·
            refine ⟨4888051020200169246966571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6517401360266892329288761 4888051020200169246966571)
            ·
              refine ⟨7332076530300253870449857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888051020200169246966571 7332076530300253870449857)
              ·
                refine ⟨5499057397725190402837393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7332076530300253870449857 5499057397725190402837393)
                ·
                  refine ⟨4124293048293892802128045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5499057397725190402837393 4124293048293892802128045)
                  ·
                    refine ⟨1546609893110209800798017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4124293048293892802128045 1546609893110209800798017)
                    ·
                      refine ⟨1159957419832657350598513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546609893110209800798017 1159957419832657350598513)
                      ·
                        rfl

theorem cell23_2259009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2259009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259009 prefixEnd_2259009 := by exact prefixLift 2259009
  have htrace : WordTrace (prefixWord ++ tailWord_2259009) baseStart_2259009 baseEnd_2259009 := by
    simpa [prefixWord, tailWord_2259009, baseEnd_2259009] using wordTrace_append hprefix tailTrace_2259009
  have hstable : (prefixWord ++ tailWord_2259009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259009).length < 2 ^ (prefixWord ++ tailWord_2259009).sum := by decide
  have hdescent : baseEnd_2259009 < baseStart_2259009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259015 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2259015 : Nat := 118140960795 + 2259015 * 2 ^ 59
def prefixEnd_2259015 : Nat := 4983230072969 + 3 ^ 40 * 2259015 * 2
def baseEnd_2259015 : Nat := 386653500238861442374495

theorem tailTrace_2259015 : CollatzResearch.WordTrace tailWord_2259015 prefixEnd_2259015 386653500238861442374495 := by
  unfold tailWord_2259015
  simp only [CollatzResearch.WordTrace]
  refine ⟨82393045910981938891282499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54928697273987959260854999 82393045910981938891282499)
  ·
    refine ⟨123589568866472908336923749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82393045910981938891282499 123589568866472908336923749)
    ·
      refine ⟨23173044162463670313173203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123589568866472908336923749 23173044162463670313173203)
      ·
        refine ⟨34759566243695505469759805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23173044162463670313173203 34759566243695505469759805)
        ·
          refine ⟨13034837341385814551159927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34759566243695505469759805 13034837341385814551159927)
          ·
            refine ⟨19552256012078721826739891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13034837341385814551159927 19552256012078721826739891)
            ·
              refine ⟨29328384018118082740109837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19552256012078721826739891 29328384018118082740109837)
              ·
                refine ⟨10998144006794281027541189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29328384018118082740109837 10998144006794281027541189)
                ·
                  refine ⟨2062152001273927692663973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10998144006794281027541189 2062152001273927692663973)
                  ·
                    refine ⟨386653500238861442374495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2062152001273927692663973 386653500238861442374495)
                    ·
                      rfl

theorem cell23_2259015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2259015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259015 prefixEnd_2259015 := by exact prefixLift 2259015
  have htrace : WordTrace (prefixWord ++ tailWord_2259015) baseStart_2259015 baseEnd_2259015 := by
    simpa [prefixWord, tailWord_2259015, baseEnd_2259015] using wordTrace_append hprefix tailTrace_2259015
  have hstable : (prefixWord ++ tailWord_2259015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259015).length < 2 ^ (prefixWord ++ tailWord_2259015).sum := by decide
  have hdescent : baseEnd_2259015 < baseStart_2259015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259025 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_2259025 : Nat := 118140960795 + 2259025 * 2 ^ 59
def prefixEnd_2259025 : Nat := 4983230072969 + 3 ^ 40 * 2259025 * 2
def baseEnd_2259025 : Nat := 1159965635523129287998439

theorem tailTrace_2259025 : CollatzResearch.WordTrace tailWord_2259025 prefixEnd_2259025 1159965635523129287998439 := by
  unfold tailWord_2259025
  simp only [CollatzResearch.WordTrace]
  refine ⟨82393410640945710599146529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54928940427297140399431019 82393410640945710599146529)
  ·
    refine ⟨61795057980709282949359897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82393410640945710599146529 61795057980709282949359897)
    ·
      refine ⟨46346293485531962212019923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61795057980709282949359897 46346293485531962212019923)
      ·
        refine ⟨69519440228297943318029885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46346293485531962212019923 69519440228297943318029885)
        ·
          refine ⟨26069790085611728744261207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69519440228297943318029885 26069790085611728744261207)
          ·
            refine ⟨39104685128417593116391811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26069790085611728744261207 39104685128417593116391811)
            ·
              refine ⟨58657027692626389674587717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39104685128417593116391811 58657027692626389674587717)
              ·
                refine ⟨10998192692367448063985197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58657027692626389674587717 10998192692367448063985197)
                ·
                  refine ⟨4124322259637793023994449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10998192692367448063985197 4124322259637793023994449)
                  ·
                    refine ⟨3093241694728344767995837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124322259637793023994449 3093241694728344767995837)
                    ·
                      refine ⟨1159965635523129287998439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093241694728344767995837 1159965635523129287998439)
                      ·
                        rfl

theorem cell23_2259025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_2259025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259025 prefixEnd_2259025 := by exact prefixLift 2259025
  have htrace : WordTrace (prefixWord ++ tailWord_2259025) baseStart_2259025 baseEnd_2259025 := by
    simpa [prefixWord, tailWord_2259025, baseEnd_2259025] using wordTrace_append hprefix tailTrace_2259025
  have hstable : (prefixWord ++ tailWord_2259025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259025).length < 2 ^ (prefixWord ++ tailWord_2259025).sum := by decide
  have hdescent : baseEnd_2259025 < baseStart_2259025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259032 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_2259032 : Nat := 118140960795 + 2259032 * 2 ^ 59
def prefixEnd_2259032 : Nat := 4983230072969 + 3 ^ 40 * 2259032 * 2
def baseEnd_2259032 : Nat := 386656409962570253536969

theorem tailTrace_2259032 : CollatzResearch.WordTrace tailWord_2259032 prefixEnd_2259032 386656409962570253536969 := by
  unfold tailWord_2259032
  simp only [CollatzResearch.WordTrace]
  refine ⟨41196832975960175397325675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54929110634613567196434233 41196832975960175397325675)
  ·
    refine ⟨61795249463940263095988513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41196832975960175397325675 61795249463940263095988513)
    ·
      refine ⟨46346437097955197321991385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61795249463940263095988513 46346437097955197321991385)
      ·
        refine ⟨34759827823466397991493539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46346437097955197321991385 34759827823466397991493539)
        ·
          refine ⟨52139741735199596987240309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34759827823466397991493539 52139741735199596987240309)
          ·
            refine ⟨4888100787674962217553779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52139741735199596987240309 4888100787674962217553779)
            ·
              refine ⟨7332151181512443326330669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888100787674962217553779 7332151181512443326330669)
              ·
                refine ⟨2749556693067166247374001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7332151181512443326330669 2749556693067166247374001)
                ·
                  refine ⟨2062167519800374685530501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2749556693067166247374001 2062167519800374685530501)
                  ·
                    refine ⟨386656409962570253536969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2062167519800374685530501 386656409962570253536969)
                    ·
                      rfl

theorem cell23_2259032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_2259032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259032 prefixEnd_2259032 := by exact prefixLift 2259032
  have htrace : WordTrace (prefixWord ++ tailWord_2259032) baseStart_2259032 baseEnd_2259032 := by
    simpa [prefixWord, tailWord_2259032, baseEnd_2259032] using wordTrace_append hprefix tailTrace_2259032
  have hstable : (prefixWord ++ tailWord_2259032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259032).length < 2 ^ (prefixWord ++ tailWord_2259032).sum := by decide
  have hdescent : baseEnd_2259032 < baseStart_2259032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259055 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_2259055 : Nat := 118140960795 + 2259055 * 2 ^ 59
def prefixEnd_2259055 : Nat := 4983230072969 + 3 ^ 40 * 2259055 * 2
def baseEnd_2259055 : Nat := 1159981039942764170623301

theorem tailTrace_2259055 : CollatzResearch.WordTrace tailWord_2259055 prefixEnd_2259055 1159981039942764170623301 := by
  unfold tailWord_2259055
  simp only [CollatzResearch.WordTrace]
  refine ⟨82394504830837025722738619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54929669887224683815159079 82394504830837025722738619)
  ·
    refine ⟨123591757246255538584107929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82394504830837025722738619 123591757246255538584107929)
    ·
      refine ⟨92693817934691653938080947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123591757246255538584107929 92693817934691653938080947)
      ·
        refine ⟨139040726902037480907121421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92693817934691653938080947 139040726902037480907121421)
        ·
          refine ⟨52140272588264055340170533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139040726902037480907121421 52140272588264055340170533)
          ·
            refine ⟨9776301110299510376281975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52140272588264055340170533 9776301110299510376281975)
            ·
              refine ⟨14664451665449265564422963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9776301110299510376281975 14664451665449265564422963)
              ·
                refine ⟨21996677498173898346634445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14664451665449265564422963 21996677498173898346634445)
                ·
                  refine ⟨8248754061815211879987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21996677498173898346634445 8248754061815211879987917)
                  ·
                    refine ⟨3093282773180704454995469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8248754061815211879987917 3093282773180704454995469)
                    ·
                      refine ⟨1159981039942764170623301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093282773180704454995469 1159981039942764170623301)
                      ·
                        rfl

theorem cell23_2259055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_2259055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259055 prefixEnd_2259055 := by exact prefixLift 2259055
  have htrace : WordTrace (prefixWord ++ tailWord_2259055) baseStart_2259055 baseEnd_2259055 := by
    simpa [prefixWord, tailWord_2259055, baseEnd_2259055] using wordTrace_append hprefix tailTrace_2259055
  have hstable : (prefixWord ++ tailWord_2259055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259055).length < 2 ^ (prefixWord ++ tailWord_2259055).sum := by decide
  have hdescent : baseEnd_2259055 < baseStart_2259055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259073 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_2259073 : Nat := 118140960795 + 2259073 * 2 ^ 59
def prefixEnd_2259073 : Nat := 4983230072969 + 3 ^ 40 * 2259073 * 2
def baseEnd_2259073 : Nat := 1159990282594545100198219

theorem tailTrace_2259073 : CollatzResearch.WordTrace tailWord_2259073 prefixEnd_2259073 1159990282594545100198219 := by
  unfold tailWord_2259073
  simp only [CollatzResearch.WordTrace]
  refine ⟨82395161344771814796893873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54930107563181209864595915 82395161344771814796893873)
  ·
    refine ⟨61796371008578861097670405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82395161344771814796893873 61796371008578861097670405)
    ·
      refine ⟨11586819564108536455813201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61796371008578861097670405 11586819564108536455813201)
      ·
        refine ⟨8690114673081402341859901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11586819564108536455813201 8690114673081402341859901)
        ·
          refine ⟨3258793002405525878197463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8690114673081402341859901 3258793002405525878197463)
          ·
            refine ⟨4888189503608288817296195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258793002405525878197463 4888189503608288817296195)
            ·
              refine ⟨7332284255412433225944293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888189503608288817296195 7332284255412433225944293)
              ·
                refine ⟨1374803297889831229864555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7332284255412433225944293 1374803297889831229864555)
                ·
                  refine ⟨2062204946834746844796833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374803297889831229864555 2062204946834746844796833)
                  ·
                    refine ⟨1546653710126060133597625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062204946834746844796833 1546653710126060133597625)
                    ·
                      refine ⟨1159990282594545100198219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546653710126060133597625 1159990282594545100198219)
                      ·
                        rfl

theorem cell23_2259073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_2259073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259073 prefixEnd_2259073 := by exact prefixLift 2259073
  have htrace : WordTrace (prefixWord ++ tailWord_2259073) baseStart_2259073 baseEnd_2259073 := by
    simpa [prefixWord, tailWord_2259073, baseEnd_2259073] using wordTrace_append hprefix tailTrace_2259073
  have hstable : (prefixWord ++ tailWord_2259073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259073).length < 2 ^ (prefixWord ++ tailWord_2259073).sum := by decide
  have hdescent : baseEnd_2259073 < baseStart_2259073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259094 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2259094 : Nat := 118140960795 + 2259094 * 2 ^ 59
def prefixEnd_2259094 : Nat := 4983230072969 + 3 ^ 40 * 2259094 * 2
def baseEnd_2259094 : Nat := 1160001065688289518035623

theorem tailTrace_2259094 : CollatzResearch.WordTrace tailWord_2259094 prefixEnd_2259094 1160001065688289518035623 := by
  unfold tailWord_2259094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149745454855983461463021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54930618185130490255605557 5149745454855983461463021)
  ·
    refine ⟨1931154545570993798048633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5149745454855983461463021 1931154545570993798048633)
    ·
      refine ⟨1448365909178245348536475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1931154545570993798048633 1448365909178245348536475)
      ·
        refine ⟨2172548863767368022804713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448365909178245348536475 2172548863767368022804713)
        ·
          refine ⟨1629411647825526017103535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172548863767368022804713 1629411647825526017103535)
          ·
            refine ⟨2444117471738289025655303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629411647825526017103535 2444117471738289025655303)
            ·
              refine ⟨3666176207607433538482955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444117471738289025655303 3666176207607433538482955)
              ·
                refine ⟨5499264311411150307724433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666176207607433538482955 5499264311411150307724433)
                ·
                  refine ⟨4124448233558362730793325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5499264311411150307724433 4124448233558362730793325)
                  ·
                    refine ⟨1546668087584386024047497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4124448233558362730793325 1546668087584386024047497)
                    ·
                      refine ⟨1160001065688289518035623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546668087584386024047497 1160001065688289518035623)
                      ·
                        rfl

theorem cell23_2259094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2259094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259094 prefixEnd_2259094 := by exact prefixLift 2259094
  have htrace : WordTrace (prefixWord ++ tailWord_2259094) baseStart_2259094 baseEnd_2259094 := by
    simpa [prefixWord, tailWord_2259094, baseEnd_2259094] using wordTrace_append hprefix tailTrace_2259094
  have hstable : (prefixWord ++ tailWord_2259094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259094).length < 2 ^ (prefixWord ++ tailWord_2259094).sum := by decide
  have hdescent : baseEnd_2259094 < baseStart_2259094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259129 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2259129 : Nat := 118140960795 + 2259129 * 2 ^ 59
def prefixEnd_2259129 : Nat := 4983230072969 + 3 ^ 40 * 2259129 * 2
def baseEnd_2259129 : Nat := 1160019037511196881097961

theorem tailTrace_2259129 : CollatzResearch.WordTrace tailWord_2259129 prefixEnd_2259129 1160019037511196881097961 := by
  unfold tailWord_2259129
  simp only [CollatzResearch.WordTrace]
  refine ⟨82397203832568936360932441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54931469221712624240621627 82397203832568936360932441)
  ·
    refine ⟨61797902874426702270699331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82397203832568936360932441 61797902874426702270699331)
    ·
      refine ⟨92696854311640053406048997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61797902874426702270699331 92696854311640053406048997)
      ·
        refine ⟨17380660183432510013634187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92696854311640053406048997 17380660183432510013634187)
        ·
          refine ⟨26070990275148765020451281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17380660183432510013634187 26070990275148765020451281)
          ·
            refine ⟨19553242706361573765338461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26070990275148765020451281 19553242706361573765338461)
            ·
              refine ⟨7332466014885590162001923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19553242706361573765338461 7332466014885590162001923)
              ·
                refine ⟨10998699022328385243002885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332466014885590162001923 10998699022328385243002885)
                ·
                  refine ⟨2062256066686572233063041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10998699022328385243002885 2062256066686572233063041)
                  ·
                    refine ⟨1546692050014929174797281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062256066686572233063041 1546692050014929174797281)
                    ·
                      refine ⟨1160019037511196881097961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546692050014929174797281 1160019037511196881097961)
                      ·
                        rfl

theorem cell23_2259129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2259129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259129 prefixEnd_2259129 := by exact prefixLift 2259129
  have htrace : WordTrace (prefixWord ++ tailWord_2259129) baseStart_2259129 baseEnd_2259129 := by
    simpa [prefixWord, tailWord_2259129, baseEnd_2259129] using wordTrace_append hprefix tailTrace_2259129
  have hstable : (prefixWord ++ tailWord_2259129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259129).length < 2 ^ (prefixWord ++ tailWord_2259129).sum := by decide
  have hdescent : baseEnd_2259129 < baseStart_2259129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259145 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_2259145 : Nat := 118140960795 + 2259145 * 2 ^ 59
def prefixEnd_2259145 : Nat := 4983230072969 + 3 ^ 40 * 2259145 * 2
def baseEnd_2259145 : Nat := 1160027253201668818497887

theorem tailTrace_2259145 : CollatzResearch.WordTrace tailWord_2259145 prefixEnd_2259145 1160027253201668818497887 := by
  unfold tailWord_2259145
  simp only [CollatzResearch.WordTrace]
  refine ⟨82397787400510971093514889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54931858267007314062343259 82397787400510971093514889)
  ·
    refine ⟨61798340550383228320136167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82397787400510971093514889 61798340550383228320136167)
    ·
      refine ⟨92697510825574842480204251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61798340550383228320136167 92697510825574842480204251)
      ·
        refine ⟨139046266238362263720306377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92697510825574842480204251 139046266238362263720306377)
        ·
          refine ⟨104284699678771697790229783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139046266238362263720306377 104284699678771697790229783)
          ·
            refine ⟨156427049518157546685344675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104284699678771697790229783 156427049518157546685344675)
            ·
              refine ⟨234640574277236320028017013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156427049518157546685344675 234640574277236320028017013)
              ·
                refine ⟨21997553838490905002626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234640574277236320028017013 21997553838490905002626595)
                ·
                  refine ⟨32996330757736357503939893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21997553838490905002626595 32996330757736357503939893)
                  ·
                    refine ⟨3093406008537783515994365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32996330757736357503939893 3093406008537783515994365)
                    ·
                      refine ⟨1160027253201668818497887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093406008537783515994365 1160027253201668818497887)
                      ·
                        rfl

theorem cell23_2259145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_2259145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259145 prefixEnd_2259145 := by exact prefixLift 2259145
  have htrace : WordTrace (prefixWord ++ tailWord_2259145) baseStart_2259145 baseEnd_2259145 := by
    simpa [prefixWord, tailWord_2259145, baseEnd_2259145] using wordTrace_append hprefix tailTrace_2259145
  have hstable : (prefixWord ++ tailWord_2259145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259145).length < 2 ^ (prefixWord ++ tailWord_2259145).sum := by decide
  have hdescent : baseEnd_2259145 < baseStart_2259145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259172 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_2259172 : Nat := 118140960795 + 2259172 * 2 ^ 59
def prefixEnd_2259172 : Nat := 4983230072969 + 3 ^ 40 * 2259172 * 2
def baseEnd_2259172 : Nat := 1160041117179340212860263

theorem tailTrace_2259172 : CollatzResearch.WordTrace tailWord_2259172 prefixEnd_2259172 1160041117179340212860263 := by
  unfold tailWord_2259172
  simp only [CollatzResearch.WordTrace]
  refine ⟨41199386085706577352373885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54932514780942103136498513 41199386085706577352373885)
  ·
    refine ⟨15449769782139966507140207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41199386085706577352373885 15449769782139966507140207)
    ·
      refine ⟨23174654673209949760710311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15449769782139966507140207 23174654673209949760710311)
      ·
        refine ⟨34761982009814924641065467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23174654673209949760710311 34761982009814924641065467)
        ·
          refine ⟨52142973014722386961598201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34761982009814924641065467 52142973014722386961598201)
          ·
            refine ⟨39107229761041790221198651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52142973014722386961598201 39107229761041790221198651)
            ·
              refine ⟨58660844641562685331797977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39107229761041790221198651 58660844641562685331797977)
              ·
                refine ⟨43995633481172013998848483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58660844641562685331797977 43995633481172013998848483)
                ·
                  refine ⟨65993450221758020998272725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43995633481172013998848483 65993450221758020998272725)
                  ·
                    refine ⟨1546721489572453617147017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65993450221758020998272725 1546721489572453617147017)
                    ·
                      refine ⟨1160041117179340212860263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546721489572453617147017 1160041117179340212860263)
                      ·
                        rfl

theorem cell23_2259172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_2259172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259172 prefixEnd_2259172 := by exact prefixLift 2259172
  have htrace : WordTrace (prefixWord ++ tailWord_2259172) baseStart_2259172 baseEnd_2259172 := by
    simpa [prefixWord, tailWord_2259172, baseEnd_2259172] using wordTrace_append hprefix tailTrace_2259172
  have hstable : (prefixWord ++ tailWord_2259172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259172).length < 2 ^ (prefixWord ++ tailWord_2259172).sum := by decide
  have hdescent : baseEnd_2259172 < baseStart_2259172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259186 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_2259186 : Nat := 118140960795 + 2259186 * 2 ^ 59
def prefixEnd_2259186 : Nat := 4983230072969 + 3 ^ 40 * 2259186 * 2
def baseEnd_2259186 : Nat := 128894256212055906453911

theorem tailTrace_2259186 : CollatzResearch.WordTrace tailWord_2259186 prefixEnd_2259186 128894256212055906453911 := by
  unfold tailWord_2259186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20599820698340608773939353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54932855195574956730504941 20599820698340608773939353)
  ·
    refine ⟨15449865523755456580454515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20599820698340608773939353 15449865523755456580454515)
    ·
      refine ⟨23174798285633184870681773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15449865523755456580454515 23174798285633184870681773)
      ·
        refine ⟨8690549357112444326505665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23174798285633184870681773 8690549357112444326505665)
        ·
          refine ⟨6517912017834333244879249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8690549357112444326505665 6517912017834333244879249)
          ·
            refine ⟨4888434013375749933659437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6517912017834333244879249 4888434013375749933659437)
            ·
              refine ⟨1833162755015906225122289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4888434013375749933659437 1833162755015906225122289)
              ·
                refine ⟨1374872066261929668841717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833162755015906225122289 1374872066261929668841717)
                ·
                  refine ⟨128894256212055906453911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1374872066261929668841717 128894256212055906453911)
                  ·
                    rfl

theorem cell23_2259186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_2259186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259186 prefixEnd_2259186 := by exact prefixLift 2259186
  have htrace : WordTrace (prefixWord ++ tailWord_2259186) baseStart_2259186 baseEnd_2259186 := by
    simpa [prefixWord, tailWord_2259186, baseEnd_2259186] using wordTrace_append hprefix tailTrace_2259186
  have hstable : (prefixWord ++ tailWord_2259186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259186).length < 2 ^ (prefixWord ++ tailWord_2259186).sum := by decide
  have hdescent : baseEnd_2259186 < baseStart_2259186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259212 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_2259212 : Nat := 118140960795 + 2259212 * 2 ^ 59
def prefixEnd_2259212 : Nat := 4983230072969 + 3 ^ 40 * 2259212 * 2
def baseEnd_2259212 : Nat := 386687218801840018786693

theorem tailTrace_2259212 : CollatzResearch.WordTrace tailWord_2259212 prefixEnd_2259212 386687218801840018786693 := by
  unfold tailWord_2259212
  simp only [CollatzResearch.WordTrace]
  refine ⟨41200115545634120768101945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54933487394178827690802593 41200115545634120768101945)
  ·
    refine ⟨30900086659225590576076459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41200115545634120768101945 30900086659225590576076459)
    ·
      refine ⟨46350129988838385864114689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30900086659225590576076459 46350129988838385864114689)
      ·
        refine ⟨34762597491628789398086017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46350129988838385864114689 34762597491628789398086017)
        ·
          refine ⟨26071948118721592048564513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34762597491628789398086017 26071948118721592048564513)
          ·
            refine ⟨19553961089041194036423385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26071948118721592048564513 19553961089041194036423385)
            ·
              refine ⟨14665470816780895527317539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19553961089041194036423385 14665470816780895527317539)
              ·
                refine ⟨21998206225171343290976309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14665470816780895527317539 21998206225171343290976309)
                ·
                  refine ⟨2062331833609813433529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21998206225171343290976309 2062331833609813433529029)
                  ·
                    refine ⟨386687218801840018786693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2062331833609813433529029 386687218801840018786693)
                    ·
                      rfl

theorem cell23_2259212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_2259212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259212 prefixEnd_2259212 := by exact prefixLift 2259212
  have htrace : WordTrace (prefixWord ++ tailWord_2259212) baseStart_2259212 baseEnd_2259212 := by
    simpa [prefixWord, tailWord_2259212, baseEnd_2259212] using wordTrace_append hprefix tailTrace_2259212
  have hstable : (prefixWord ++ tailWord_2259212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259212).length < 2 ^ (prefixWord ++ tailWord_2259212).sum := by decide
  have hdescent : baseEnd_2259212 < baseStart_2259212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259215 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_2259215 : Nat := 118140960795 + 2259215 * 2 ^ 59
def prefixEnd_2259215 : Nat := 4983230072969 + 3 ^ 40 * 2259215 * 2
def baseEnd_2259215 : Nat := 1160063196847483544622565

theorem tailTrace_2259215 : CollatzResearch.WordTrace tailWord_2259215 prefixEnd_2259215 1160063196847483544622565 := by
  unfold tailWord_2259215
  simp only [CollatzResearch.WordTrace]
  refine ⟨82400340510257373048563099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54933560340171582032375399 82400340510257373048563099)
  ·
    refine ⟨123600510765386059572844649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82400340510257373048563099 123600510765386059572844649)
    ·
      refine ⟨92700383074039544679633487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123600510765386059572844649 92700383074039544679633487)
      ·
        refine ⟨139050574611059317019450231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92700383074039544679633487 139050574611059317019450231)
        ·
          refine ⟨208575861916588975529175347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139050574611059317019450231 208575861916588975529175347)
          ·
            refine ⟨312863792874883463293763021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208575861916588975529175347 312863792874883463293763021)
            ·
              refine ⟨117323922328081298735161133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312863792874883463293763021 117323922328081298735161133)
              ·
                refine ⟨43996470873030487025685425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117323922328081298735161133 43996470873030487025685425)
                ·
                  refine ⟨32997353154772865269264069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43996470873030487025685425 32997353154772865269264069)
                  ·
                    refine ⟨6187003716519912237987013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32997353154772865269264069 6187003716519912237987013)
                    ·
                      refine ⟨1160063196847483544622565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6187003716519912237987013 1160063196847483544622565)
                      ·
                        rfl

theorem cell23_2259215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_2259215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259215 prefixEnd_2259215 := by exact prefixLift 2259215
  have htrace : WordTrace (prefixWord ++ tailWord_2259215) baseStart_2259215 baseEnd_2259215 := by
    simpa [prefixWord, tailWord_2259215, baseEnd_2259215] using wordTrace_append hprefix tailTrace_2259215
  have hstable : (prefixWord ++ tailWord_2259215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259215).length < 2 ^ (prefixWord ++ tailWord_2259215).sum := by decide
  have hdescent : baseEnd_2259215 < baseStart_2259215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259272 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2259272 : Nat := 118140960795 + 2259272 * 2 ^ 59
def prefixEnd_2259272 : Nat := 4983230072969 + 3 ^ 40 * 2259272 * 2
def baseEnd_2259272 : Nat := 386697488414929940536601

theorem tailTrace_2259272 : CollatzResearch.WordTrace tailWord_2259272 prefixEnd_2259272 386697488414929940536601 := by
  unfold tailWord_2259272
  simp only [CollatzResearch.WordTrace]
  refine ⟨41201209735525435891694035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54934946314033914522258713 41201209735525435891694035)
  ·
    refine ⟨61801814603288153837541053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41201209735525435891694035 61801814603288153837541053)
    ·
      refine ⟨23175680476233057689077895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61801814603288153837541053 23175680476233057689077895)
      ·
        refine ⟨34763520714349586533616843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23175680476233057689077895 34763520714349586533616843)
        ·
          refine ⟨52145281071524379800425265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34763520714349586533616843 52145281071524379800425265)
          ·
            refine ⟨39108960803643284850318949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52145281071524379800425265 39108960803643284850318949)
            ·
              refine ⟨7332930150683115909434803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39108960803643284850318949 7332930150683115909434803)
              ·
                refine ⟨10999395226024673864152205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332930150683115909434803 10999395226024673864152205)
                ·
                  refine ⟨4124773209759252699057077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10999395226024673864152205 4124773209759252699057077)
                  ·
                    refine ⟨386697488414929940536601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4124773209759252699057077 386697488414929940536601)
                    ·
                      rfl

theorem cell23_2259272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2259272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259272 prefixEnd_2259272 := by exact prefixLift 2259272
  have htrace : WordTrace (prefixWord ++ tailWord_2259272) baseStart_2259272 baseEnd_2259272 := by
    simpa [prefixWord, tailWord_2259272, baseEnd_2259272] using wordTrace_append hprefix tailTrace_2259272
  have hstable : (prefixWord ++ tailWord_2259272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259272).length < 2 ^ (prefixWord ++ tailWord_2259272).sum := by decide
  have hdescent : baseEnd_2259272 < baseStart_2259272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259279 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 2, 3, 2]
def baseStart_2259279 : Nat := 118140960795 + 2259279 * 2 ^ 59
def prefixEnd_2259279 : Nat := 4983230072969 + 3 ^ 40 * 2259279 * 2
def baseEnd_2259279 : Nat := 1160096059609371294222271

theorem tailTrace_2259279 : CollatzResearch.WordTrace tailWord_2259279 prefixEnd_2259279 1160096059609371294222271 := by
  unfold tailWord_2259279
  simp only [CollatzResearch.WordTrace]
  refine ⟨82402674782025511978892891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54935116521350341319261927 82402674782025511978892891)
  ·
    refine ⟨123604012173038267968339337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82402674782025511978892891 123604012173038267968339337)
    ·
      refine ⟨92703009129778700976254503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123604012173038267968339337 92703009129778700976254503)
      ·
        refine ⟨139054513694668051464381755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92703009129778700976254503 139054513694668051464381755)
        ·
          refine ⟨208581770542002077196572633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139054513694668051464381755 208581770542002077196572633)
          ·
            refine ⟨156436327906501557897429475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208581770542002077196572633 156436327906501557897429475)
            ·
              refine ⟨234654491859752336846144213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156436327906501557897429475 234654491859752336846144213)
              ·
                refine ⟨5499714652962945394831505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 234654491859752336846144213 5499714652962945394831505)
                ·
                  refine ⟨4124785989722209046123629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5499714652962945394831505 4124785989722209046123629)
                  ·
                    refine ⟨1546794746145828392296361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4124785989722209046123629 1546794746145828392296361)
                    ·
                      refine ⟨1160096059609371294222271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546794746145828392296361 1160096059609371294222271)
                      ·
                        rfl

theorem cell23_2259279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3, 2].length) (baseStart_2259279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259279 prefixEnd_2259279 := by exact prefixLift 2259279
  have htrace : WordTrace (prefixWord ++ tailWord_2259279) baseStart_2259279 baseEnd_2259279 := by
    simpa [prefixWord, tailWord_2259279, baseEnd_2259279] using wordTrace_append hprefix tailTrace_2259279
  have hstable : (prefixWord ++ tailWord_2259279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259279).length < 2 ^ (prefixWord ++ tailWord_2259279).sum := by decide
  have hdescent : baseEnd_2259279 < baseStart_2259279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259303 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_2259303 : Nat := 118140960795 + 2259303 * 2 ^ 59
def prefixEnd_2259303 : Nat := 4983230072969 + 3 ^ 40 * 2259303 * 2
def baseEnd_2259303 : Nat := 1160108383145079200322161

theorem tailTrace_2259303 : CollatzResearch.WordTrace tailWord_2259303 prefixEnd_2259303 1160108383145079200322161 := by
  unfold tailWord_2259303
  simp only [CollatzResearch.WordTrace]
  refine ⟨82403550133938564077766563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54935700089292376051844375 82403550133938564077766563)
  ·
    refine ⟨123605325200907846116649845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82403550133938564077766563 123605325200907846116649845)
    ·
      refine ⟨11587999237585110573435923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123605325200907846116649845 11587999237585110573435923)
      ·
        refine ⟨17381998856377665860153885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587999237585110573435923 17381998856377665860153885)
        ·
          refine ⟨6518249571141624697557707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17381998856377665860153885 6518249571141624697557707)
          ·
            refine ⟨9777374356712437046336561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518249571141624697557707 9777374356712437046336561)
            ·
              refine ⟨7333030767534327784752421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9777374356712437046336561 7333030767534327784752421)
              ·
                refine ⟨1374943268912686459641079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7333030767534327784752421 1374943268912686459641079)
                ·
                  refine ⟨2062414903369029689461619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374943268912686459641079 2062414903369029689461619)
                  ·
                    refine ⟨3093622355053544534192429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2062414903369029689461619 3093622355053544534192429)
                    ·
                      refine ⟨1160108383145079200322161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093622355053544534192429 1160108383145079200322161)
                      ·
                        rfl

theorem cell23_2259303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_2259303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259303 prefixEnd_2259303 := by exact prefixLift 2259303
  have htrace : WordTrace (prefixWord ++ tailWord_2259303) baseStart_2259303 baseEnd_2259303 := by
    simpa [prefixWord, tailWord_2259303, baseEnd_2259303] using wordTrace_append hprefix tailTrace_2259303
  have hstable : (prefixWord ++ tailWord_2259303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259303).length < 2 ^ (prefixWord ++ tailWord_2259303).sum := by decide
  have hdescent : baseEnd_2259303 < baseStart_2259303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259312 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_2259312 : Nat := 118140960795 + 2259312 * 2 ^ 59
def prefixEnd_2259312 : Nat := 4983230072969 + 3 ^ 40 * 2259312 * 2
def baseEnd_2259312 : Nat := 1160113004470969665109619

theorem tailTrace_2259312 : CollatzResearch.WordTrace tailWord_2259312 prefixEnd_2259312 1160113004470969665109619 := by
  unfold tailWord_2259312
  simp only [CollatzResearch.WordTrace]
  refine ⟨41201939195452979307422095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54935918927270639076562793 41201939195452979307422095)
  ·
    refine ⟨61802908793179468961133143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41201939195452979307422095 61802908793179468961133143)
    ·
      refine ⟨92704363189769203441699715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61802908793179468961133143 92704363189769203441699715)
      ·
        refine ⟨139056544784653805162549573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92704363189769203441699715 139056544784653805162549573)
        ·
          refine ⟨26073102147122588467978045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139056544784653805162549573 26073102147122588467978045)
          ·
            refine ⟨9777413305170970675491767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26073102147122588467978045 9777413305170970675491767)
            ·
              refine ⟨14666119957756456013237651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9777413305170970675491767 14666119957756456013237651)
              ·
                refine ⟨21999179936634684019856477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14666119957756456013237651 21999179936634684019856477)
                ·
                  refine ⟨8249692476238006507446179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21999179936634684019856477 8249692476238006507446179)
                  ·
                    refine ⟨12374538714357009761169269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8249692476238006507446179 12374538714357009761169269)
                    ·
                      refine ⟨1160113004470969665109619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12374538714357009761169269 1160113004470969665109619)
                      ·
                        rfl

theorem cell23_2259312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_2259312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259312 prefixEnd_2259312 := by exact prefixLift 2259312
  have htrace : WordTrace (prefixWord ++ tailWord_2259312) baseStart_2259312 baseEnd_2259312 := by
    simpa [prefixWord, tailWord_2259312, baseEnd_2259312] using wordTrace_append hprefix tailTrace_2259312
  have hstable : (prefixWord ++ tailWord_2259312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259312).length < 2 ^ (prefixWord ++ tailWord_2259312).sum := by decide
  have hdescent : baseEnd_2259312 < baseStart_2259312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259332 : List Nat := [2, 3, 2, 1, 1, 2, 3, 9]
def baseStart_2259332 : Nat := 118140960795 + 2259332 * 2 ^ 59
def prefixEnd_2259332 : Nat := 4983230072969 + 3 ^ 40 * 2259332 * 2
def baseEnd_2259332 : Nat := 42967528669779984698501

theorem tailTrace_2259332 : CollatzResearch.WordTrace tailWord_2259332 prefixEnd_2259332 42967528669779984698501 := by
  unfold tailWord_2259332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41202303925416751015286125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54936405233889001353714833 41202303925416751015286125)
  ·
    refine ⟨15450863972031281630732297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41202303925416751015286125 15450863972031281630732297)
    ·
      refine ⟨11588147979023461223049223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15450863972031281630732297 11588147979023461223049223)
      ·
        refine ⟨17382221968535191834573835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11588147979023461223049223 17382221968535191834573835)
        ·
          refine ⟨26073332952802787751860753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17382221968535191834573835 26073332952802787751860753)
          ·
            refine ⟨19554999714602090813895565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26073332952802787751860753 19554999714602090813895565)
            ·
              refine ⟨7333124892975784055210837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19554999714602090813895565 7333124892975784055210837)
              ·
                refine ⟨42967528669779984698501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7333124892975784055210837 42967528669779984698501)
                ·
                  rfl

theorem cell23_2259332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 9].length) (baseStart_2259332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259332 prefixEnd_2259332 := by exact prefixLift 2259332
  have htrace : WordTrace (prefixWord ++ tailWord_2259332) baseStart_2259332 baseEnd_2259332 := by
    simpa [prefixWord, tailWord_2259332, baseEnd_2259332] using wordTrace_append hprefix tailTrace_2259332
  have hstable : (prefixWord ++ tailWord_2259332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259332).length < 2 ^ (prefixWord ++ tailWord_2259332).sum := by decide
  have hdescent : baseEnd_2259332 < baseStart_2259332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259380 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2259380 : Nat := 118140960795 + 2259380 * 2 ^ 59
def prefixEnd_2259380 : Nat := 4983230072969 + 3 ^ 40 * 2259380 * 2
def baseEnd_2259380 : Nat := 1160147921155475399059307

theorem tailTrace_2259380 : CollatzResearch.WordTrace tailWord_2259380 prefixEnd_2259380 1160147921155475399059307 := by
  unfold tailWord_2259380
  simp only [CollatzResearch.WordTrace]
  refine ⟨41203179277329803114159797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54937572369773070818879729 41203179277329803114159797)
  ·
    refine ⟨3862798057249669041952481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41203179277329803114159797 3862798057249669041952481)
    ·
      refine ⟨2897098542937251781464361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3862798057249669041952481 2897098542937251781464361)
      ·
        refine ⟨2172823907202938836098271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2897098542937251781464361 2172823907202938836098271)
        ·
          refine ⟨3259235860804408254147407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172823907202938836098271 3259235860804408254147407)
          ·
            refine ⟨4888853791206612381221111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259235860804408254147407 4888853791206612381221111)
            ·
              refine ⟨7333280686809918571831667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888853791206612381221111 7333280686809918571831667)
              ·
                refine ⟨10999921030214877857747501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333280686809918571831667 10999921030214877857747501)
                ·
                  refine ⟨4124970386330579196655313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10999921030214877857747501 4124970386330579196655313)
                  ·
                    refine ⟨3093727789747934397491485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4124970386330579196655313 3093727789747934397491485)
                    ·
                      refine ⟨1160147921155475399059307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093727789747934397491485 1160147921155475399059307)
                      ·
                        rfl

theorem cell23_2259380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2259380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259380 prefixEnd_2259380 := by exact prefixLift 2259380
  have htrace : WordTrace (prefixWord ++ tailWord_2259380) baseStart_2259380 baseEnd_2259380 := by
    simpa [prefixWord, tailWord_2259380, baseEnd_2259380] using wordTrace_append hprefix tailTrace_2259380
  have hstable : (prefixWord ++ tailWord_2259380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259380).length < 2 ^ (prefixWord ++ tailWord_2259380).sum := by decide
  have hdescent : baseEnd_2259380 < baseStart_2259380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259392 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_2259392 : Nat := 118140960795 + 2259392 * 2 ^ 59
def prefixEnd_2259392 : Nat := 4983230072969 + 3 ^ 40 * 2259392 * 2
def baseEnd_2259392 : Nat := 386718027641109784036417

theorem tailTrace_2259392 : CollatzResearch.WordTrace tailWord_2259392 prefixEnd_2259392 386718027641109784036417 := by
  unfold tailWord_2259392
  simp only [CollatzResearch.WordTrace]
  refine ⟨41203398115308066138878215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54937864153744088185170953 41203398115308066138878215)
  ·
    refine ⟨61805097172962099208317323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41203398115308066138878215 61805097172962099208317323)
    ·
      refine ⟨92707645759443148812475985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61805097172962099208317323 92707645759443148812475985)
      ·
        refine ⟨69530734319582361609356989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92707645759443148812475985 69530734319582361609356989)
        ·
          refine ⟨26074025369843385603508871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69530734319582361609356989 26074025369843385603508871)
          ·
            refine ⟨39111038054765078405263307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26074025369843385603508871 39111038054765078405263307)
            ·
              refine ⟨58666557082147617607894961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39111038054765078405263307 58666557082147617607894961)
              ·
                refine ⟨43999917811610713205921221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58666557082147617607894961 43999917811610713205921221)
                ·
                  refine ⟨8249984589677008726110229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43999917811610713205921221 8249984589677008726110229)
                  ·
                    refine ⟨386718027641109784036417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8249984589677008726110229 386718027641109784036417)
                    ·
                      rfl

theorem cell23_2259392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_2259392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259392 prefixEnd_2259392 := by exact prefixLift 2259392
  have htrace : WordTrace (prefixWord ++ tailWord_2259392) baseStart_2259392 baseEnd_2259392 := by
    simpa [prefixWord, tailWord_2259392, baseEnd_2259392] using wordTrace_append hprefix tailTrace_2259392
  have hstable : (prefixWord ++ tailWord_2259392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259392).length < 2 ^ (prefixWord ++ tailWord_2259392).sum := by decide
  have hdescent : baseEnd_2259392 < baseStart_2259392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259489 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2259489 : Nat := 118140960795 + 2259489 * 2 ^ 59
def prefixEnd_2259489 : Nat := 4983230072969 + 3 ^ 40 * 2259489 * 2
def baseEnd_2259489 : Nat := 1160203890546815472596305

theorem tailTrace_2259489 : CollatzResearch.WordTrace tailWord_2259489 prefixEnd_2259489 1160203890546815472596305 := by
  unfold tailWord_2259489
  simp only [CollatzResearch.WordTrace]
  refine ⟨82410334111264717844037521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54940222740843145229358347 82410334111264717844037521)
  ·
    refine ⟨61807750583448538383028141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82410334111264717844037521 61807750583448538383028141)
    ·
      refine ⟨23177906468793201893635553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61807750583448538383028141 23177906468793201893635553)
      ·
        refine ⟨17383429851594901420226665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23177906468793201893635553 17383429851594901420226665)
        ·
          refine ⟨13037572388696176065169999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17383429851594901420226665 13037572388696176065169999)
          ·
            refine ⟨19556358583044264097754999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037572388696176065169999 19556358583044264097754999)
            ·
              refine ⟨29334537874566396146632499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19556358583044264097754999 29334537874566396146632499)
              ·
                refine ⟨44001806811849594219948749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29334537874566396146632499 44001806811849594219948749)
                ·
                  refine ⟨16500677554443597832480781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44001806811849594219948749 16500677554443597832480781)
                  ·
                    refine ⟨6187754082916349187180293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16500677554443597832480781 6187754082916349187180293)
                    ·
                      refine ⟨1160203890546815472596305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6187754082916349187180293 1160203890546815472596305)
                      ·
                        rfl

theorem cell23_2259489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2259489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259489 prefixEnd_2259489 := by exact prefixLift 2259489
  have htrace : WordTrace (prefixWord ++ tailWord_2259489) baseStart_2259489 baseEnd_2259489 := by
    simpa [prefixWord, tailWord_2259489, baseEnd_2259489] using wordTrace_append hprefix tailTrace_2259489
  have hstable : (prefixWord ++ tailWord_2259489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259489).length < 2 ^ (prefixWord ++ tailWord_2259489).sum := by decide
  have hdescent : baseEnd_2259489 < baseStart_2259489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259506 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_2259506 : Nat := 118140960795 + 2259506 * 2 ^ 59
def prefixEnd_2259506 : Nat := 4983230072969 + 3 ^ 40 * 2259506 * 2
def baseEnd_2259506 : Nat := 1160212619717941906083727

theorem tailTrace_2259506 : CollatzResearch.WordTrace tailWord_2259506 prefixEnd_2259506 1160212619717941906083727 := by
  unfold tailWord_2259506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20602738538050782436851593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54940636101468753164937581 20602738538050782436851593)
  ·
    refine ⟨15452053903538086827638695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20602738538050782436851593 15452053903538086827638695)
    ·
      refine ⟨23178080855307130241458043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15452053903538086827638695 23178080855307130241458043)
      ·
        refine ⟨34767121282960695362187065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23178080855307130241458043 34767121282960695362187065)
        ·
          refine ⟨26075340962220521521640299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34767121282960695362187065 26075340962220521521640299)
          ·
            refine ⟨39113011443330782282460449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26075340962220521521640299 39113011443330782282460449)
            ·
              refine ⟨29334758582498086711845337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39113011443330782282460449 29334758582498086711845337)
              ·
                refine ⟨22001068936873565033884003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29334758582498086711845337 22001068936873565033884003)
                ·
                  refine ⟨33001603405310347550826005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22001068936873565033884003 33001603405310347550826005)
                  ·
                    refine ⟨1546950159623922541444969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33001603405310347550826005 1546950159623922541444969)
                    ·
                      refine ⟨1160212619717941906083727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546950159623922541444969 1160212619717941906083727)
                      ·
                        rfl

theorem cell23_2259506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_2259506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259506 prefixEnd_2259506 := by exact prefixLift 2259506
  have htrace : WordTrace (prefixWord ++ tailWord_2259506) baseStart_2259506 baseEnd_2259506 := by
    simpa [prefixWord, tailWord_2259506, baseEnd_2259506] using wordTrace_append hprefix tailTrace_2259506
  have hstable : (prefixWord ++ tailWord_2259506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259506).length < 2 ^ (prefixWord ++ tailWord_2259506).sum := by decide
  have hdescent : baseEnd_2259506 < baseStart_2259506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259524 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 5]
def baseStart_2259524 : Nat := 118140960795 + 2259524 * 2 ^ 59
def prefixEnd_2259524 : Nat := 4983230072969 + 3 ^ 40 * 2259524 * 2
def baseEnd_2259524 : Nat := 128913540263302537295405

theorem tailTrace_2259524 : CollatzResearch.WordTrace tailWord_2259524 prefixEnd_2259524 128913540263302537295405 := by
  unfold tailWord_2259524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41205805333068959410780813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54941073777425279214374417 41205805333068959410780813)
  ·
    refine ⟨15452176999900859779042805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41205805333068959410780813 15452176999900859779042805)
    ·
      refine ⟨1448641593740705604285263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15452176999900859779042805 1448641593740705604285263)
      ·
        refine ⟨2172962390611058406427895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448641593740705604285263 2172962390611058406427895)
        ·
          refine ⟨3259443585916587609641843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172962390611058406427895 3259443585916587609641843)
          ·
            refine ⟨4889165378874881414462765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259443585916587609641843 4889165378874881414462765)
            ·
              refine ⟨1833437017078080530423537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4889165378874881414462765 1833437017078080530423537)
              ·
                refine ⟨1375077762808560397817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833437017078080530423537 1375077762808560397817653)
                ·
                  refine ⟨128913540263302537295405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1375077762808560397817653 128913540263302537295405)
                  ·
                    rfl

theorem cell23_2259524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_2259524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259524 prefixEnd_2259524 := by exact prefixLift 2259524
  have htrace : WordTrace (prefixWord ++ tailWord_2259524) baseStart_2259524 baseEnd_2259524 := by
    simpa [prefixWord, tailWord_2259524, baseEnd_2259524] using wordTrace_append hprefix tailTrace_2259524
  have hstable : (prefixWord ++ tailWord_2259524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259524).length < 2 ^ (prefixWord ++ tailWord_2259524).sum := by decide
  have hdescent : baseEnd_2259524 < baseStart_2259524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259560 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2259560 : Nat := 118140960795 + 2259560 * 2 ^ 59
def prefixEnd_2259560 : Nat := 4983230072969 + 3 ^ 40 * 2259560 * 2
def baseEnd_2259560 : Nat := 1160240347673284694808479

theorem tailTrace_2259560 : CollatzResearch.WordTrace tailWord_2259560 prefixEnd_2259560 1160240347673284694808479 := by
  unfold tailWord_2259560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41206461847003748484936067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54941949129338331313248089 41206461847003748484936067)
  ·
    refine ⟨61809692770505622727404101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41206461847003748484936067 61809692770505622727404101)
    ·
      refine ⟨11589317394469804261388269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61809692770505622727404101 11589317394469804261388269)
      ·
        refine ⟨4345994022926176598020601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11589317394469804261388269 4345994022926176598020601)
        ·
          refine ⟨3259495517194632448515451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345994022926176598020601 3259495517194632448515451)
          ·
            refine ⟨4889243275791948672773177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259495517194632448515451 4889243275791948672773177)
            ·
              refine ⟨3666932456843961504579883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889243275791948672773177 3666932456843961504579883)
              ·
                refine ⟨5500398685265942256869825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666932456843961504579883 5500398685265942256869825)
                ·
                  refine ⟨4125299013949456692652369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500398685265942256869825 4125299013949456692652369)
                  ·
                    refine ⟨3093974260462092519489277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125299013949456692652369 3093974260462092519489277)
                    ·
                      refine ⟨1160240347673284694808479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3093974260462092519489277 1160240347673284694808479)
                      ·
                        rfl

theorem cell23_2259560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2259560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259560 prefixEnd_2259560 := by exact prefixLift 2259560
  have htrace : WordTrace (prefixWord ++ tailWord_2259560) baseStart_2259560 baseEnd_2259560 := by
    simpa [prefixWord, tailWord_2259560, baseEnd_2259560] using wordTrace_append hprefix tailTrace_2259560
  have hstable : (prefixWord ++ tailWord_2259560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259560).length < 2 ^ (prefixWord ++ tailWord_2259560).sum := by decide
  have hdescent : baseEnd_2259560 < baseStart_2259560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259617 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2259617 : Nat := 118140960795 + 2259617 * 2 ^ 59
def prefixEnd_2259617 : Nat := 4983230072969 + 3 ^ 40 * 2259617 * 2
def baseEnd_2259617 : Nat := 1160269616070590971795717

theorem tailTrace_2259617 : CollatzResearch.WordTrace tailWord_2259617 prefixEnd_2259617 1160269616070590971795717 := by
  unfold tailWord_2259617
  simp only [CollatzResearch.WordTrace]
  refine ⟨82415002654800995704697105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54943335103200663803131403 82415002654800995704697105)
  ·
    refine ⟨61811251991100746778522829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82415002654800995704697105 61811251991100746778522829)
    ·
      refine ⟨23179219496662780041946061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61811251991100746778522829 23179219496662780041946061)
      ·
        refine ⟨8692207311248542515729773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23179219496662780041946061 8692207311248542515729773)
        ·
          refine ⟨3259577741718203443398665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8692207311248542515729773 3259577741718203443398665)
          ·
            refine ⟨2444683306288652582548999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3259577741718203443398665 2444683306288652582548999)
            ·
              refine ⟨3667024959432978873823499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444683306288652582548999 3667024959432978873823499)
              ·
                refine ⟨5500537439149468310735249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667024959432978873823499 5500537439149468310735249)
                ·
                  refine ⟨4125403079362101233051437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500537439149468310735249 4125403079362101233051437)
                  ·
                    refine ⟨1547026154760787962394289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4125403079362101233051437 1547026154760787962394289)
                    ·
                      refine ⟨1160269616070590971795717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547026154760787962394289 1160269616070590971795717)
                      ·
                        rfl

theorem cell23_2259617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2259617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259617 prefixEnd_2259617 := by exact prefixLift 2259617
  have htrace : WordTrace (prefixWord ++ tailWord_2259617) baseStart_2259617 baseEnd_2259617 := by
    simpa [prefixWord, tailWord_2259617, baseEnd_2259617] using wordTrace_append hprefix tailTrace_2259617
  have hstable : (prefixWord ++ tailWord_2259617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259617).length < 2 ^ (prefixWord ++ tailWord_2259617).sum := by decide
  have hdescent : baseEnd_2259617 < baseStart_2259617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259647 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 1, 2, 2]
def baseStart_2259647 : Nat := 118140960795 + 2259647 * 2 ^ 59
def prefixEnd_2259647 : Nat := 4983230072969 + 3 ^ 40 * 2259647 * 2
def baseEnd_2259647 : Nat := 1160285020490225854420579

theorem tailTrace_2259647 : CollatzResearch.WordTrace tailWord_2259647 prefixEnd_2259647 1160285020490225854420579 := by
  unfold tailWord_2259647
  simp only [CollatzResearch.WordTrace]
  refine ⟨82416096844692310828289195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54944064563128207218859463 82416096844692310828289195)
  ·
    refine ⟨123624145267038466242433793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82416096844692310828289195 123624145267038466242433793)
    ·
      refine ⟨92718108950278849681825345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123624145267038466242433793 92718108950278849681825345)
      ·
        refine ⟨69538581712709137261369009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92718108950278849681825345 69538581712709137261369009)
        ·
          refine ⟨52153936284531852946026757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69538581712709137261369009 52153936284531852946026757)
          ·
            refine ⟨9778863053349722427380017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52153936284531852946026757 9778863053349722427380017)
            ·
              refine ⟨7334147290012291820535013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778863053349722427380017 7334147290012291820535013)
              ·
                refine ⟨1375152616877304716350315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7334147290012291820535013 1375152616877304716350315)
                ·
                  refine ⟨2062728925315957074525473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375152616877304716350315 2062728925315957074525473)
                  ·
                    refine ⟨1547046693986967805894105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062728925315957074525473 1547046693986967805894105)
                    ·
                      refine ⟨1160285020490225854420579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547046693986967805894105 1160285020490225854420579)
                      ·
                        rfl

theorem cell23_2259647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_2259647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259647 prefixEnd_2259647 := by exact prefixLift 2259647
  have htrace : WordTrace (prefixWord ++ tailWord_2259647) baseStart_2259647 baseEnd_2259647 := by
    simpa [prefixWord, tailWord_2259647, baseEnd_2259647] using wordTrace_append hprefix tailTrace_2259647
  have hstable : (prefixWord ++ tailWord_2259647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259647).length < 2 ^ (prefixWord ++ tailWord_2259647).sum := by decide
  have hdescent : baseEnd_2259647 < baseStart_2259647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259660 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2259660 : Nat := 118140960795 + 2259660 * 2 ^ 59
def prefixEnd_2259660 : Nat := 4983230072969 + 3 ^ 40 * 2259660 * 2
def baseEnd_2259660 : Nat := 1160291695738734303558019

theorem tailTrace_2259660 : CollatzResearch.WordTrace tailWord_2259660 prefixEnd_2259660 1160291695738734303558019 := by
  unfold tailWord_2259660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41208285496822607024256217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54944380662430142699008289 41208285496822607024256217)
  ·
    refine ⟨30906214122616955268192163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41208285496822607024256217 30906214122616955268192163)
    ·
      refine ⟨46359321183925432902288245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30906214122616955268192163 46359321183925432902288245)
      ·
        refine ⟨4346186360993009334589523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46359321183925432902288245 4346186360993009334589523)
        ·
          refine ⟨6519279541489514001884285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346186360993009334589523 6519279541489514001884285)
          ·
            refine ⟨2444729828058567750706607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6519279541489514001884285 2444729828058567750706607)
            ·
              refine ⟨3667094742087851626059911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444729828058567750706607 3667094742087851626059911)
              ·
                refine ⟨5500642113131777439089867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667094742087851626059911 5500642113131777439089867)
                ·
                  refine ⟨8250963169697666158634801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500642113131777439089867 8250963169697666158634801)
                  ·
                    refine ⟨6188222377273249618976101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8250963169697666158634801 6188222377273249618976101)
                    ·
                      refine ⟨1160291695738734303558019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6188222377273249618976101 1160291695738734303558019)
                      ·
                        rfl

theorem cell23_2259660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2259660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259660 prefixEnd_2259660 := by exact prefixLift 2259660
  have htrace : WordTrace (prefixWord ++ tailWord_2259660) baseStart_2259660 baseEnd_2259660 := by
    simpa [prefixWord, tailWord_2259660, baseEnd_2259660] using wordTrace_append hprefix tailTrace_2259660
  have hstable : (prefixWord ++ tailWord_2259660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259660).length < 2 ^ (prefixWord ++ tailWord_2259660).sum := by decide
  have hdescent : baseEnd_2259660 < baseStart_2259660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259714 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2259714 : Nat := 118140960795 + 2259714 * 2 ^ 59
def prefixEnd_2259714 : Nat := 4983230072969 + 3 ^ 40 * 2259714 * 2
def baseEnd_2259714 : Nat := 1160319423694077092282771

theorem tailTrace_2259714 : CollatzResearch.WordTrace tailWord_2259714 prefixEnd_2259714 1160319423694077092282771 := by
  unfold tailWord_2259714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604635133862395317744549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54945693690299720847318797 20604635133862395317744549)
  ·
    refine ⟨3863369087599199122077103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20604635133862395317744549 3863369087599199122077103)
    ·
      refine ⟨5795053631398798683115655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863369087599199122077103 5795053631398798683115655)
      ·
        refine ⟨8692580447098198024673483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795053631398798683115655 8692580447098198024673483)
        ·
          refine ⟨13038870670647297037010225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8692580447098198024673483 13038870670647297037010225)
          ·
            refine ⟨9779153002985472777757669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13038870670647297037010225 9779153002985472777757669)
            ·
              refine ⟨1833591188059776145829563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9779153002985472777757669 1833591188059776145829563)
              ·
                refine ⟨2750386782089664218744345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833591188059776145829563 2750386782089664218744345)
                ·
                  refine ⟨2062790086567248164058259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750386782089664218744345 2062790086567248164058259)
                  ·
                    refine ⟨3094185129850872246087389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2062790086567248164058259 3094185129850872246087389)
                    ·
                      refine ⟨1160319423694077092282771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3094185129850872246087389 1160319423694077092282771)
                      ·
                        rfl

theorem cell23_2259714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2259714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259714 prefixEnd_2259714 := by exact prefixLift 2259714
  have htrace : WordTrace (prefixWord ++ tailWord_2259714) baseStart_2259714 baseEnd_2259714 := by
    simpa [prefixWord, tailWord_2259714, baseEnd_2259714] using wordTrace_append hprefix tailTrace_2259714
  have hstable : (prefixWord ++ tailWord_2259714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259714).length < 2 ^ (prefixWord ++ tailWord_2259714).sum := by decide
  have hdescent : baseEnd_2259714 < baseStart_2259714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259726 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2259726 : Nat := 118140960795 + 2259726 * 2 ^ 59
def prefixEnd_2259726 : Nat := 4983230072969 + 3 ^ 40 * 2259726 * 2
def baseEnd_2259726 : Nat := 128925065051325671703635

theorem tailTrace_2259726 : CollatzResearch.WordTrace tailWord_2259726 prefixEnd_2259726 128925065051325671703635 := by
  unfold tailWord_2259726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10302372276425763415051879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54945985474270738213610021 10302372276425763415051879)
  ·
    refine ⟨15453558414638645122577819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10302372276425763415051879 15453558414638645122577819)
    ·
      refine ⟨23180337621957967683866729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15453558414638645122577819 23180337621957967683866729)
      ·
        refine ⟨17385253216468475762900047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23180337621957967683866729 17385253216468475762900047)
        ·
          refine ⟨26077879824702713644350071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17385253216468475762900047 26077879824702713644350071)
          ·
            refine ⟨39116819737054070466525107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26077879824702713644350071 39116819737054070466525107)
            ·
              refine ⟨58675229605581105699787661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39116819737054070466525107 58675229605581105699787661)
              ·
                refine ⟨22003211102092914637420373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58675229605581105699787661 22003211102092914637420373)
                ·
                  refine ⟨128925065051325671703635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22003211102092914637420373 128925065051325671703635)
                  ·
                    rfl

theorem cell23_2259726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2259726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259726 prefixEnd_2259726 := by exact prefixLift 2259726
  have htrace : WordTrace (prefixWord ++ tailWord_2259726) baseStart_2259726 baseEnd_2259726 := by
    simpa [prefixWord, tailWord_2259726, baseEnd_2259726] using wordTrace_append hprefix tailTrace_2259726
  have hstable : (prefixWord ++ tailWord_2259726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259726).length < 2 ^ (prefixWord ++ tailWord_2259726).sum := by decide
  have hdescent : baseEnd_2259726 < baseStart_2259726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259741 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2259741 : Nat := 118140960795 + 2259741 * 2 ^ 59
def prefixEnd_2259741 : Nat := 4983230072969 + 3 ^ 40 * 2259741 * 2
def baseEnd_2259741 : Nat := 1160333287671748486645147

theorem tailTrace_2259741 : CollatzResearch.WordTrace tailWord_2259741 prefixEnd_2259741 1160333287671748486645147 := by
  unfold tailWord_2259741
  simp only [CollatzResearch.WordTrace]
  refine ⟨82419525306351764882211077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54946350204234509921474051 82419525306351764882211077)
  ·
    refine ⟨15453660994940955915414577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82419525306351764882211077 15453660994940955915414577)
    ·
      refine ⟨11590245746205716936560933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15453660994940955915414577 11590245746205716936560933)
      ·
        refine ⟨2173171077413571925605175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11590245746205716936560933 2173171077413571925605175)
        ·
          refine ⟨3259756616120357888407763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173171077413571925605175 3259756616120357888407763)
          ·
            refine ⟨4889634924180536832611645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259756616120357888407763 4889634924180536832611645)
            ·
              refine ⟨1833613096567701312229367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4889634924180536832611645 1833613096567701312229367)
              ·
                refine ⟨2750419644851551968344051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833613096567701312229367 2750419644851551968344051)
                ·
                  refine ⟨4125629467277327952516077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750419644851551968344051 4125629467277327952516077)
                  ·
                    refine ⟨1547111050228997982193529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4125629467277327952516077 1547111050228997982193529)
                    ·
                      refine ⟨1160333287671748486645147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547111050228997982193529 1160333287671748486645147)
                      ·
                        rfl

theorem cell23_2259741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2259741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259741 prefixEnd_2259741 := by exact prefixLift 2259741
  have htrace : WordTrace (prefixWord ++ tailWord_2259741) baseStart_2259741 baseEnd_2259741 := by
    simpa [prefixWord, tailWord_2259741, baseEnd_2259741] using wordTrace_append hprefix tailTrace_2259741
  have hstable : (prefixWord ++ tailWord_2259741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259741).length < 2 ^ (prefixWord ++ tailWord_2259741).sum := by decide
  have hdescent : baseEnd_2259741 < baseStart_2259741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259770 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_2259770 : Nat := 118140960795 + 2259770 * 2 ^ 59
def prefixEnd_2259770 : Nat := 4983230072969 + 3 ^ 40 * 2259770 * 2
def baseEnd_2259770 : Nat := 1160348178610728873182513

theorem tailTrace_2259770 : CollatzResearch.WordTrace tailWord_2259770 prefixEnd_2259770 1160348178610728873182513 := by
  unfold tailWord_2259770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605145755811675708754191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54947055348831135223344509 20605145755811675708754191)
  ·
    refine ⟨30907718633717513563131287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20605145755811675708754191 30907718633717513563131287)
    ·
      refine ⟨46361577950576270344696931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30907718633717513563131287 46361577950576270344696931)
      ·
        refine ⟨69542366925864405517045397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46361577950576270344696931 69542366925864405517045397)
        ·
          refine ⟨3259798449649894008611503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69542366925864405517045397 3259798449649894008611503)
          ·
            refine ⟨4889697674474841012917255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259798449649894008611503 4889697674474841012917255)
            ·
              refine ⟨7334546511712261519375883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889697674474841012917255 7334546511712261519375883)
              ·
                refine ⟨11001819767568392279063825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7334546511712261519375883 11001819767568392279063825)
                ·
                  refine ⟨8251364825676294209297869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11001819767568392279063825 8251364825676294209297869)
                  ·
                    refine ⟨3094261809628610328486701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8251364825676294209297869 3094261809628610328486701)
                    ·
                      refine ⟨1160348178610728873182513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3094261809628610328486701 1160348178610728873182513)
                      ·
                        rfl

theorem cell23_2259770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_2259770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259770 prefixEnd_2259770 := by exact prefixLift 2259770
  have htrace : WordTrace (prefixWord ++ tailWord_2259770) baseStart_2259770 baseEnd_2259770 := by
    simpa [prefixWord, tailWord_2259770, baseEnd_2259770] using wordTrace_append hprefix tailTrace_2259770
  have hstable : (prefixWord ++ tailWord_2259770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259770).length < 2 ^ (prefixWord ++ tailWord_2259770).sum := by decide
  have hdescent : baseEnd_2259770 < baseStart_2259770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259786 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_2259786 : Nat := 118140960795 + 2259786 * 2 ^ 59
def prefixEnd_2259786 : Nat := 4983230072969 + 3 ^ 40 * 2259786 * 2
def baseEnd_2259786 : Nat := 386785464767066936860813

theorem tailTrace_2259786 : CollatzResearch.WordTrace tailWord_2259786 prefixEnd_2259786 386785464767066936860813 := by
  unfold tailWord_2259786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605291647797184391899803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54947444394125825045066141 20605291647797184391899803)
  ·
    refine ⟨30907937471695776587849705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20605291647797184391899803 30907937471695776587849705)
    ·
      refine ⟨23180953103771832440887279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30907937471695776587849705 23180953103771832440887279)
      ·
        refine ⟨34771429655657748661330919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23180953103771832440887279 34771429655657748661330919)
        ·
          refine ⟨52157144483486622991996379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34771429655657748661330919 52157144483486622991996379)
          ·
            refine ⟨78235716725229934487994569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52157144483486622991996379 78235716725229934487994569)
            ·
              refine ⟨58676787543922450865995927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78235716725229934487994569 58676787543922450865995927)
              ·
                refine ⟨88015181315883676298993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58676787543922450865995927 88015181315883676298993891)
                ·
                  refine ⟨132022771973825514448490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88015181315883676298993891 132022771973825514448490837)
                  ·
                    refine ⟨386785464767066936860813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 132022771973825514448490837 386785464767066936860813)
                    ·
                      rfl

theorem cell23_2259786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_2259786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259786 prefixEnd_2259786 := by exact prefixLift 2259786
  have htrace : WordTrace (prefixWord ++ tailWord_2259786) baseStart_2259786 baseEnd_2259786 := by
    simpa [prefixWord, tailWord_2259786, baseEnd_2259786] using wordTrace_append hprefix tailTrace_2259786
  have hstable : (prefixWord ++ tailWord_2259786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259786).length < 2 ^ (prefixWord ++ tailWord_2259786).sum := by decide
  have hdescent : baseEnd_2259786 < baseStart_2259786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259820 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_2259820 : Nat := 118140960795 + 2259820 * 2 ^ 59
def prefixEnd_2259820 : Nat := 4983230072969 + 3 ^ 40 * 2259820 * 2
def baseEnd_2259820 : Nat := 386791284214484559185761

theorem tailTrace_2259820 : CollatzResearch.WordTrace tailWord_2259820 prefixEnd_2259820 386791284214484559185761 := by
  unfold tailWord_2259820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41211203336532780687168457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54948271115377040916224609 41211203336532780687168457)
  ·
    refine ⟨30908402502399585515376343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41211203336532780687168457 30908402502399585515376343)
    ·
      refine ⟨46362603753599378273064515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30908402502399585515376343 46362603753599378273064515)
      ·
        refine ⟨69543905630399067409596773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46362603753599378273064515 69543905630399067409596773)
        ·
          refine ⟨13039482305699825139299395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69543905630399067409596773 13039482305699825139299395)
          ·
            refine ⟨19559223458549737708949093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13039482305699825139299395 19559223458549737708949093)
            ·
              refine ⟨3667354398478075820427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19559223458549737708949093 3667354398478075820427955)
              ·
                refine ⟨5501031597717113730641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667354398478075820427955 5501031597717113730641933)
                ·
                  refine ⟨2062886849143917648990725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501031597717113730641933 2062886849143917648990725)
                  ·
                    refine ⟨386791284214484559185761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2062886849143917648990725 386791284214484559185761)
                    ·
                      rfl

theorem cell23_2259820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_2259820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259820 prefixEnd_2259820 := by exact prefixLift 2259820
  have htrace : WordTrace (prefixWord ++ tailWord_2259820) baseStart_2259820 baseEnd_2259820 := by
    simpa [prefixWord, tailWord_2259820, baseEnd_2259820] using wordTrace_append hprefix tailTrace_2259820
  have hstable : (prefixWord ++ tailWord_2259820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259820).length < 2 ^ (prefixWord ++ tailWord_2259820).sum := by decide
  have hdescent : baseEnd_2259820 < baseStart_2259820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259843 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3]
def baseStart_2259843 : Nat := 118140960795 + 2259843 * 2 ^ 59
def prefixEnd_2259843 : Nat := 4983230072969 + 3 ^ 40 * 2259843 * 2
def baseEnd_2259843 : Nat := 1160385662698507087569677

theorem tailTrace_2259843 : CollatzResearch.WordTrace tailWord_2259843 prefixEnd_2259843 1160385662698507087569677 := by
  unfold tailWord_2259843
  simp only [CollatzResearch.WordTrace]
  refine ⟨82423245551982236302424183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54948830367988157534949455 82423245551982236302424183)
  ·
    refine ⟨123634868327973354453636275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82423245551982236302424183 123634868327973354453636275)
    ·
      refine ⟨185452302491960031680454413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123634868327973354453636275 185452302491960031680454413)
      ·
        refine ⟨69544613434485011880170405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185452302491960031680454413 69544613434485011880170405)
        ·
          refine ⟨13039615018965939727531951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69544613434485011880170405 13039615018965939727531951)
          ·
            refine ⟨19559422528448909591297927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13039615018965939727531951 19559422528448909591297927)
            ·
              refine ⟨29339133792673364386946891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19559422528448909591297927 29339133792673364386946891)
              ·
                refine ⟨44008700689010046580420337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29339133792673364386946891 44008700689010046580420337)
                ·
                  refine ⟨33006525516757534935315253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44008700689010046580420337 33006525516757534935315253)
                  ·
                    refine ⟨3094361767196018900185805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33006525516757534935315253 3094361767196018900185805)
                    ·
                      refine ⟨1160385662698507087569677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3094361767196018900185805 1160385662698507087569677)
                      ·
                        rfl

theorem cell23_2259843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_2259843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259843 prefixEnd_2259843 := by exact prefixLift 2259843
  have htrace : WordTrace (prefixWord ++ tailWord_2259843) baseStart_2259843 baseEnd_2259843 := by
    simpa [prefixWord, tailWord_2259843, baseEnd_2259843] using wordTrace_append hprefix tailTrace_2259843
  have hstable : (prefixWord ++ tailWord_2259843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259843).length < 2 ^ (prefixWord ++ tailWord_2259843).sum := by decide
  have hdescent : baseEnd_2259843 < baseStart_2259843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259883 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4]
def baseStart_2259883 : Nat := 118140960795 + 2259883 * 2 ^ 59
def prefixEnd_2259883 : Nat := 4983230072969 + 3 ^ 40 * 2259883 * 2
def baseEnd_2259883 : Nat := 1160406201924686931069493

theorem tailTrace_2259883 : CollatzResearch.WordTrace tailWord_2259883 prefixEnd_2259883 1160406201924686931069493 := by
  unfold tailWord_2259883
  simp only [CollatzResearch.WordTrace]
  refine ⟨82424704471837323133880303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54949802981224882089253535 82424704471837323133880303)
  ·
    refine ⟨123637056707755984700820455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82424704471837323133880303 123637056707755984700820455)
    ·
      refine ⟨185455585061633977051230683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123637056707755984700820455 185455585061633977051230683)
      ·
        refine ⟨278183377592450965576846025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185455585061633977051230683 278183377592450965576846025)
        ·
          refine ⟨208637533194338224182634519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278183377592450965576846025 208637533194338224182634519)
          ·
            refine ⟨312956299791507336273951779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208637533194338224182634519 312956299791507336273951779)
            ·
              refine ⟨469434449687261004410927669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312956299791507336273951779 469434449687261004410927669)
              ·
                refine ⟨44009479658180719163524469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 469434449687261004410927669 44009479658180719163524469)
                ·
                  refine ⟨4125888717954442421580419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44009479658180719163524469 4125888717954442421580419)
                  ·
                    refine ⟨6188833076931663632370629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4125888717954442421580419 6188833076931663632370629)
                    ·
                      refine ⟨1160406201924686931069493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6188833076931663632370629 1160406201924686931069493)
                      ·
                        rfl

theorem cell23_2259883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_2259883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259883 prefixEnd_2259883 := by exact prefixLift 2259883
  have htrace : WordTrace (prefixWord ++ tailWord_2259883) baseStart_2259883 baseEnd_2259883 := by
    simpa [prefixWord, tailWord_2259883, baseEnd_2259883] using wordTrace_append hprefix tailTrace_2259883
  have hstable : (prefixWord ++ tailWord_2259883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259883).length < 2 ^ (prefixWord ++ tailWord_2259883).sum := by decide
  have hdescent : baseEnd_2259883 < baseStart_2259883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259897 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_2259897 : Nat := 118140960795 + 2259897 * 2 ^ 59
def prefixEnd_2259897 : Nat := 4983230072969 + 3 ^ 40 * 2259897 * 2
def baseEnd_2259897 : Nat := 386804463551283292098143

theorem tailTrace_2259897 : CollatzResearch.WordTrace tailWord_2259897 prefixEnd_2259897 386804463551283292098143 := by
  unfold tailWord_2259897
  simp only [CollatzResearch.WordTrace]
  refine ⟨82425215093786603524889945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54950143395857735683259963 82425215093786603524889945)
  ·
    refine ⟨61818911320339952643667459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82425215093786603524889945 61818911320339952643667459)
    ·
      refine ⟨92728366980509928965501189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61818911320339952643667459 92728366980509928965501189)
      ·
        refine ⟨17386568808845611681031473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92728366980509928965501189 17386568808845611681031473)
        ·
          refine ⟨13039926606634208760773605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17386568808845611681031473 13039926606634208760773605)
          ·
            refine ⟨2444986238743914142645051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13039926606634208760773605 2444986238743914142645051)
            ·
              refine ⟨3667479358115871213967577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444986238743914142645051 3667479358115871213967577)
              ·
                refine ⟨2750609518586903410475683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3667479358115871213967577 2750609518586903410475683)
                ·
                  refine ⟨4125914277880355115713525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750609518586903410475683 4125914277880355115713525)
                  ·
                    refine ⟨386804463551283292098143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4125914277880355115713525 386804463551283292098143)
                    ·
                      rfl

theorem cell23_2259897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_2259897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259897 prefixEnd_2259897 := by exact prefixLift 2259897
  have htrace : WordTrace (prefixWord ++ tailWord_2259897) baseStart_2259897 baseEnd_2259897 := by
    simpa [prefixWord, tailWord_2259897, baseEnd_2259897] using wordTrace_append hprefix tailTrace_2259897
  have hstable : (prefixWord ++ tailWord_2259897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259897).length < 2 ^ (prefixWord ++ tailWord_2259897).sum := by decide
  have hdescent : baseEnd_2259897 < baseStart_2259897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259963 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_2259963 : Nat := 118140960795 + 2259963 * 2 ^ 59
def prefixEnd_2259963 : Nat := 4983230072969 + 3 ^ 40 * 2259963 * 2
def baseEnd_2259963 : Nat := 1160447280377046618069125

theorem tailTrace_2259963 : CollatzResearch.WordTrace tailWord_2259963 prefixEnd_2259963 1160447280377046618069125 := by
  unfold tailWord_2259963
  simp only [CollatzResearch.WordTrace]
  refine ⟨82427622311547496796792543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54951748207698331197861695 82427622311547496796792543)
  ·
    refine ⟨123641433467321245195188815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82427622311547496796792543 123641433467321245195188815)
    ·
      refine ⟨185462150200981867792783223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123641433467321245195188815 185462150200981867792783223)
      ·
        refine ⟨278193225301472801689174835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185462150200981867792783223 278193225301472801689174835)
        ·
          refine ⟨417289837952209202533762253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278193225301472801689174835 417289837952209202533762253)
          ·
            refine ⟨156483689232078450950160845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417289837952209202533762253 156483689232078450950160845)
            ·
              refine ⟨58681383462029419106310317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156483689232078450950160845 58681383462029419106310317)
              ·
                refine ⟨22005518798261032164866369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58681383462029419106310317 22005518798261032164866369)
                ·
                  refine ⟨16504139098695774123649777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22005518798261032164866369 16504139098695774123649777)
                  ·
                    refine ⟨12378104324021830592737333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16504139098695774123649777 12378104324021830592737333)
                    ·
                      refine ⟨1160447280377046618069125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12378104324021830592737333 1160447280377046618069125)
                      ·
                        rfl

theorem cell23_2259963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_2259963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2259963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2259963 prefixEnd_2259963 := by exact prefixLift 2259963
  have htrace : WordTrace (prefixWord ++ tailWord_2259963) baseStart_2259963 baseEnd_2259963 := by
    simpa [prefixWord, tailWord_2259963, baseEnd_2259963] using wordTrace_append hprefix tailTrace_2259963
  have hstable : (prefixWord ++ tailWord_2259963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259963).length < 2 ^ (prefixWord ++ tailWord_2259963).sum := by decide
  have hdescent : baseEnd_2259963 < baseStart_2259963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260001 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2260001 : Nat := 118140960795 + 2260001 * 2 ^ 59
def prefixEnd_2260001 : Nat := 4983230072969 + 3 ^ 40 * 2260001 * 2
def baseEnd_2260001 : Nat := 1160466792641917469393951

theorem tailTrace_2260001 : CollatzResearch.WordTrace tailWord_2260001 prefixEnd_2260001 1160466792641917469393951 := by
  unfold tailWord_2260001
  simp only [CollatzResearch.WordTrace]
  refine ⟨82429008285409829286675857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54952672190273219524450571 82429008285409829286675857)
  ·
    refine ⟨61821756214057371965006893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82429008285409829286675857 61821756214057371965006893)
    ·
      refine ⟨23183158580271514486877585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61821756214057371965006893 23183158580271514486877585)
      ·
        refine ⟨17387368935203635865158189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23183158580271514486877585 17387368935203635865158189)
        ·
          refine ⟨6520263350701363449434321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17387368935203635865158189 6520263350701363449434321)
          ·
            refine ⟨4890197513026022587075741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6520263350701363449434321 4890197513026022587075741)
            ·
              refine ⟨1833824067384758470153403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4890197513026022587075741 1833824067384758470153403)
              ·
                refine ⟨2750736101077137705230105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833824067384758470153403 2750736101077137705230105)
                ·
                  refine ⟨2063052075807853278922579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750736101077137705230105 2063052075807853278922579)
                  ·
                    refine ⟨3094578113711779918383869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2063052075807853278922579 3094578113711779918383869)
                    ·
                      refine ⟨1160466792641917469393951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3094578113711779918383869 1160466792641917469393951)
                      ·
                        rfl

theorem cell23_2260001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2260001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260001 prefixEnd_2260001 := by exact prefixLift 2260001
  have htrace : WordTrace (prefixWord ++ tailWord_2260001) baseStart_2260001 baseEnd_2260001 := by
    simpa [prefixWord, tailWord_2260001, baseEnd_2260001] using wordTrace_append hprefix tailTrace_2260001
  have hstable : (prefixWord ++ tailWord_2260001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260001).length < 2 ^ (prefixWord ++ tailWord_2260001).sum := by decide
  have hdescent : baseEnd_2260001 < baseStart_2260001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260024 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_2260024 : Nat := 118140960795 + 2260024 * 2 ^ 59
def prefixEnd_2260024 : Nat := 4983230072969 + 3 ^ 40 * 2260024 * 2
def baseEnd_2260024 : Nat := 1160478602696970879406345

theorem tailTrace_2260024 : CollatzResearch.WordTrace tailWord_2260024 prefixEnd_2260024 1160478602696970879406345 := by
  unfold tailWord_2260024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41214923582163252107381563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54953231442884336143175417 41214923582163252107381563)
  ·
    refine ⟨61822385373244878161072345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41214923582163252107381563 61822385373244878161072345)
    ·
      refine ⟨46366789029933658620804259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61822385373244878161072345 46366789029933658620804259)
      ·
        refine ⟨69550183544900487931206389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46366789029933658620804259 69550183544900487931206389)
        ·
          refine ⟨6520329707334420743550599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69550183544900487931206389 6520329707334420743550599)
          ·
            refine ⟨9780494561001631115325899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520329707334420743550599 9780494561001631115325899)
            ·
              refine ⟨14670741841502446672988849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780494561001631115325899 14670741841502446672988849)
              ·
                refine ⟨11003056381126835004741637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14670741841502446672988849 11003056381126835004741637)
                ·
                  refine ⟨2063073071461281563389057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11003056381126835004741637 2063073071461281563389057)
                  ·
                    refine ⟨1547304803595961172541793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2063073071461281563389057 1547304803595961172541793)
                    ·
                      refine ⟨1160478602696970879406345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547304803595961172541793 1160478602696970879406345)
                      ·
                        rfl

theorem cell23_2260024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_2260024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260024 prefixEnd_2260024 := by exact prefixLift 2260024
  have htrace : WordTrace (prefixWord ++ tailWord_2260024) baseStart_2260024 baseEnd_2260024 := by
    simpa [prefixWord, tailWord_2260024, baseEnd_2260024] using wordTrace_append hprefix tailTrace_2260024
  have hstable : (prefixWord ++ tailWord_2260024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260024).length < 2 ^ (prefixWord ++ tailWord_2260024).sum := by decide
  have hdescent : baseEnd_2260024 < baseStart_2260024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260077 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2260077 : Nat := 118140960795 + 2260077 * 2 ^ 59
def prefixEnd_2260077 : Nat := 4983230072969 + 3 ^ 40 * 2260077 * 2
def baseEnd_2260077 : Nat := 386835272390553057347867

theorem tailTrace_2260077 : CollatzResearch.WordTrace tailWord_2260077 prefixEnd_2260077 386835272390553057347867 := by
  unfold tailWord_2260077
  simp only [CollatzResearch.WordTrace]
  refine ⟨82431780233134494266442485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54954520155422996177628323 82431780233134494266442485)
  ·
    refine ⟨7727979396856358837478983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82431780233134494266442485 7727979396856358837478983)
    ·
      refine ⟨11591969095284538256218475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727979396856358837478983 11591969095284538256218475)
      ·
        refine ⟨17387953642926807384327713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11591969095284538256218475 17387953642926807384327713)
        ·
          refine ⟨13040965232195105538245785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17387953642926807384327713 13040965232195105538245785)
          ·
            refine ⟨9780723924146329153684339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13040965232195105538245785 9780723924146329153684339)
            ·
              refine ⟨14671085886219493730526509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780723924146329153684339 14671085886219493730526509)
              ·
                refine ⟨5501657207332310148947441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14671085886219493730526509 5501657207332310148947441)
                ·
                  refine ⟨4126242905499232611710581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501657207332310148947441 4126242905499232611710581)
                  ·
                    refine ⟨386835272390553057347867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4126242905499232611710581 386835272390553057347867)
                    ·
                      rfl

theorem cell23_2260077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2260077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260077 prefixEnd_2260077 := by exact prefixLift 2260077
  have htrace : WordTrace (prefixWord ++ tailWord_2260077) baseStart_2260077 baseEnd_2260077 := by
    simpa [prefixWord, tailWord_2260077, baseEnd_2260077] using wordTrace_append hprefix tailTrace_2260077
  have hstable : (prefixWord ++ tailWord_2260077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260077).length < 2 ^ (prefixWord ++ tailWord_2260077).sum := by decide
  have hdescent : baseEnd_2260077 < baseStart_2260077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260114 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2260114 : Nat := 118140960795 + 2260114 * 2 ^ 59
def prefixEnd_2260114 : Nat := 4983230072969 + 3 ^ 40 * 2260114 * 2
def baseEnd_2260114 : Nat := 1160524815955875527280931

theorem tailTrace_2260114 : CollatzResearch.WordTrace tailWord_2260114 prefixEnd_2260114 1160524815955875527280931 := by
  unfold tailWord_2260114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608282433500112396384849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54955419822666966390359597 20608282433500112396384849)
  ·
    refine ⟨15456211825125084297288637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20608282433500112396384849 15456211825125084297288637)
    ·
      refine ⟨5796079434421906611483239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15456211825125084297288637 5796079434421906611483239)
      ·
        refine ⟨8694119151632859917224859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796079434421906611483239 8694119151632859917224859)
        ·
          refine ⟨13041178727449289875837289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694119151632859917224859 13041178727449289875837289)
          ·
            refine ⟨9780884045586967406877967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13041178727449289875837289 9780884045586967406877967)
            ·
              refine ⟨14671326068380451110316951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780884045586967406877967 14671326068380451110316951)
              ·
                refine ⟨22006989102570676665475427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14671326068380451110316951 22006989102570676665475427)
                ·
                  refine ⟨33010483653856014998213141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22006989102570676665475427 33010483653856014998213141)
                  ·
                    refine ⟨1547366421274500703041241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33010483653856014998213141 1547366421274500703041241)
                    ·
                      refine ⟨1160524815955875527280931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547366421274500703041241 1160524815955875527280931)
                      ·
                        rfl

theorem cell23_2260114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2260114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260114 prefixEnd_2260114 := by exact prefixLift 2260114
  have htrace : WordTrace (prefixWord ++ tailWord_2260114) baseStart_2260114 baseEnd_2260114 := by
    simpa [prefixWord, tailWord_2260114, baseEnd_2260114] using wordTrace_append hprefix tailTrace_2260114
  have hstable : (prefixWord ++ tailWord_2260114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260114).length < 2 ^ (prefixWord ++ tailWord_2260114).sum := by decide
  have hdescent : baseEnd_2260114 < baseStart_2260114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260124 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2260124 : Nat := 118140960795 + 2260124 * 2 ^ 59
def prefixEnd_2260124 : Nat := 4983230072969 + 3 ^ 40 * 2260124 * 2
def baseEnd_2260124 : Nat := 386843316920806829385295

theorem tailTrace_2260124 : CollatzResearch.WordTrace tailWord_2260124 prefixEnd_2260124 386843316920806829385295 := by
  unfold tailWord_2260124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41216747231982110646701713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54955662975976147528935617 41216747231982110646701713)
  ·
    refine ⟨30912560423986582985026285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41216747231982110646701713 30912560423986582985026285)
    ·
      refine ⟨11592210158994968619384857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30912560423986582985026285 11592210158994968619384857)
      ·
        refine ⟨8694157619246226464538643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11592210158994968619384857 8694157619246226464538643)
        ·
          refine ⟨13041236428869339696807965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694157619246226464538643 13041236428869339696807965)
          ·
            refine ⟨4890463660826002386302987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13041236428869339696807965 4890463660826002386302987)
            ·
              refine ⟨7335695491239003579454481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890463660826002386302987 7335695491239003579454481)
              ·
                refine ⟨5501771618429252684590861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335695491239003579454481 5501771618429252684590861)
                ·
                  refine ⟨2063164356910969756721573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501771618429252684590861 2063164356910969756721573)
                  ·
                    refine ⟨386843316920806829385295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2063164356910969756721573 386843316920806829385295)
                    ·
                      rfl

theorem cell23_2260124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2260124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260124 prefixEnd_2260124 := by exact prefixLift 2260124
  have htrace : WordTrace (prefixWord ++ tailWord_2260124) baseStart_2260124 baseEnd_2260124 := by
    simpa [prefixWord, tailWord_2260124, baseEnd_2260124] using wordTrace_append hprefix tailTrace_2260124
  have hstable : (prefixWord ++ tailWord_2260124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260124).length < 2 ^ (prefixWord ++ tailWord_2260124).sum := by decide
  have hdescent : baseEnd_2260124 < baseStart_2260124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260181 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2260181 : Nat := 118140960795 + 2260181 * 2 ^ 59
def prefixEnd_2260181 : Nat := 4983230072969 + 3 ^ 40 * 2260181 * 2
def baseEnd_2260181 : Nat := 1160559219159726765143123

theorem tailTrace_2260181 : CollatzResearch.WordTrace tailWord_2260181 prefixEnd_2260181 1160559219159726765143123 := by
  unfold tailWord_2260181
  simp only [CollatzResearch.WordTrace]
  refine ⟨82435573424757720028228397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54957048949838480018818931 82435573424757720028228397)
  ·
    refine ⟨30913340034284145010585649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82435573424757720028228397 30913340034284145010585649)
    ·
      refine ⟨23185005025713108757939237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30913340034284145010585649 23185005025713108757939237)
      ·
        refine ⟨4347188442321207892113607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23185005025713108757939237 4347188442321207892113607)
        ·
          refine ⟨6520782663481811838170411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347188442321207892113607 6520782663481811838170411)
          ·
            refine ⟨9781173995222717757255617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520782663481811838170411 9781173995222717757255617)
            ·
              refine ⟨7335880496417038317941713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9781173995222717757255617 7335880496417038317941713)
              ·
                refine ⟨5501910372312778738456285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335880496417038317941713 5501910372312778738456285)
                ·
                  refine ⟨2063216389617292026921107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501910372312778738456285 2063216389617292026921107)
                  ·
                    refine ⟨3094824584425938040381661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2063216389617292026921107 3094824584425938040381661)
                    ·
                      refine ⟨1160559219159726765143123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3094824584425938040381661 1160559219159726765143123)
                      ·
                        rfl

theorem cell23_2260181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2260181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260181 prefixEnd_2260181 := by exact prefixLift 2260181
  have htrace : WordTrace (prefixWord ++ tailWord_2260181) baseStart_2260181 baseEnd_2260181 := by
    simpa [prefixWord, tailWord_2260181, baseEnd_2260181] using wordTrace_append hprefix tailTrace_2260181
  have hstable : (prefixWord ++ tailWord_2260181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260181).length < 2 ^ (prefixWord ++ tailWord_2260181).sum := by decide
  have hdescent : baseEnd_2260181 < baseStart_2260181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260204 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_2260204 : Nat := 118140960795 + 2260204 * 2 ^ 59
def prefixEnd_2260204 : Nat := 4983230072969 + 3 ^ 40 * 2260204 * 2
def baseEnd_2260204 : Nat := 1160571029214780175155517

theorem tailTrace_2260204 : CollatzResearch.WordTrace tailWord_2260204 prefixEnd_2260204 1160571029214780175155517 := by
  unfold tailWord_2260204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41218206151837197478157833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54957608202449596637543777 41218206151837197478157833)
  ·
    refine ⟨30913654613877898108618375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41218206151837197478157833 30913654613877898108618375)
    ·
      refine ⟨46370481920816847162927563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30913654613877898108618375 46370481920816847162927563)
      ·
        refine ⟨69555722881225270744391345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46370481920816847162927563 69555722881225270744391345)
        ·
          refine ⟨52166792160918953058293509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69555722881225270744391345 52166792160918953058293509)
          ·
            refine ⟨9781273530172303698430033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52166792160918953058293509 9781273530172303698430033)
            ·
              refine ⟨7335955147629227773822525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9781273530172303698430033 7335955147629227773822525)
              ·
                refine ⟨2750983180360960415183447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7335955147629227773822525 2750983180360960415183447)
                ·
                  refine ⟨4126474770541440622775171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750983180360960415183447 4126474770541440622775171)
                  ·
                    refine ⟨6189712155812160934162757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4126474770541440622775171 6189712155812160934162757)
                    ·
                      refine ⟨1160571029214780175155517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6189712155812160934162757 1160571029214780175155517)
                      ·
                        rfl

theorem cell23_2260204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_2260204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260204 prefixEnd_2260204 := by exact prefixLift 2260204
  have htrace : WordTrace (prefixWord ++ tailWord_2260204) baseStart_2260204 baseEnd_2260204 := by
    simpa [prefixWord, tailWord_2260204, baseEnd_2260204] using wordTrace_append hprefix tailTrace_2260204
  have hstable : (prefixWord ++ tailWord_2260204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260204).length < 2 ^ (prefixWord ++ tailWord_2260204).sum := by decide
  have hdescent : baseEnd_2260204 < baseStart_2260204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260227 : List Nat := [1, 1, 1, 3, 2, 5, 2, 8]
def baseStart_2260227 : Nat := 118140960795 + 2260227 * 2 ^ 59
def prefixEnd_2260227 : Nat := 4983230072969 + 3 ^ 40 * 2260227 * 2
def baseEnd_2260227 : Nat := 42984549602586429080293

theorem tailTrace_2260227 : CollatzResearch.WordTrace tailWord_2260227 prefixEnd_2260227 42984549602586429080293 := by
  unfold tailWord_2260227
  simp only [CollatzResearch.WordTrace]
  refine ⟨82437251182591069884402935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54958167455060713256268623 82437251182591069884402935)
  ·
    refine ⟨123655876773886604826604403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82437251182591069884402935 123655876773886604826604403)
    ·
      refine ⟨185483815160829907239906605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123655876773886604826604403 185483815160829907239906605)
      ·
        refine ⟨69556430685311215214964977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185483815160829907239906605 69556430685311215214964977)
        ·
          refine ⟨52167323013983411411223733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69556430685311215214964977 52167323013983411411223733)
          ·
            refine ⟨4890686532560944819802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52167323013983411411223733 4890686532560944819802225)
            ·
              refine ⟨3668014899420708614851669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890686532560944819802225 3668014899420708614851669)
              ·
                refine ⟨42984549602586429080293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3668014899420708614851669 42984549602586429080293)
                ·
                  rfl

theorem cell23_2260227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 8].length) (baseStart_2260227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260227 prefixEnd_2260227 := by exact prefixLift 2260227
  have htrace : WordTrace (prefixWord ++ tailWord_2260227) baseStart_2260227 baseEnd_2260227 := by
    simpa [prefixWord, tailWord_2260227, baseEnd_2260227] using wordTrace_append hprefix tailTrace_2260227
  have hstable : (prefixWord ++ tailWord_2260227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260227).length < 2 ^ (prefixWord ++ tailWord_2260227).sum := by decide
  have hdescent : baseEnd_2260227 < baseStart_2260227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260258 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2260258 : Nat := 118140960795 + 2260258 * 2 ^ 59
def prefixEnd_2260258 : Nat := 4983230072969 + 3 ^ 40 * 2260258 * 2
def baseEnd_2260258 : Nat := 1160598757170122963880269

theorem tailTrace_2260258 : CollatzResearch.WordTrace tailWord_2260258 prefixEnd_2260258 1160598757170122963880269 := by
  unfold tailWord_2260258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609595461369690544695357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54958921230319174785854285 20609595461369690544695357)
  ·
    refine ⟨7728598298013633954260759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20609595461369690544695357 7728598298013633954260759)
    ·
      refine ⟨11592897447020450931391139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728598298013633954260759 11592897447020450931391139)
      ·
        refine ⟨17389346170530676397086709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11592897447020450931391139 17389346170530676397086709)
        ·
          refine ⟨1630251203487250912226879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17389346170530676397086709 1630251203487250912226879)
          ·
            refine ⟨2445376805230876368340319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630251203487250912226879 2445376805230876368340319)
            ·
              refine ⟨3668065207846314552510479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445376805230876368340319 3668065207846314552510479)
              ·
                refine ⟨5502097811769471828765719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668065207846314552510479 5502097811769471828765719)
                ·
                  refine ⟨8253146717654207743148579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502097811769471828765719 8253146717654207743148579)
                  ·
                    refine ⟨12379720076481311614722869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8253146717654207743148579 12379720076481311614722869)
                    ·
                      refine ⟨1160598757170122963880269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12379720076481311614722869 1160598757170122963880269)
                      ·
                        rfl

theorem cell23_2260258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2260258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260258 prefixEnd_2260258 := by exact prefixLift 2260258
  have htrace : WordTrace (prefixWord ++ tailWord_2260258) baseStart_2260258 baseEnd_2260258 := by
    simpa [prefixWord, tailWord_2260258, baseEnd_2260258] using wordTrace_append hprefix tailTrace_2260258
  have hstable : (prefixWord ++ tailWord_2260258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260258).length < 2 ^ (prefixWord ++ tailWord_2260258).sum := by decide
  have hdescent : baseEnd_2260258 < baseStart_2260258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260278 : List Nat := [5, 1, 2, 3, 1, 2, 1, 8]
def baseStart_2260278 : Nat := 118140960795 + 2260278 * 2 ^ 59
def prefixEnd_2260278 : Nat := 4983230072969 + 3 ^ 40 * 2260278 * 2
def baseEnd_2260278 : Nat := 42985519510489366134451

theorem tailTrace_2260278 : CollatzResearch.WordTrace tailWord_2260278 prefixEnd_2260278 42985519510489366134451 := by
  unfold tailWord_2260278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152444456587894099656843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54959407536937537063006325 5152444456587894099656843)
  ·
    refine ⟨7728666684881841149485265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152444456587894099656843 7728666684881841149485265)
    ·
      refine ⟨5796500013661380862113949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7728666684881841149485265 5796500013661380862113949)
      ·
        refine ⟨2173687505123017823292731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5796500013661380862113949 2173687505123017823292731)
        ·
          refine ⟨3260531257684526734939097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173687505123017823292731 3260531257684526734939097)
          ·
            refine ⟨2445398443263395051204323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260531257684526734939097 2445398443263395051204323)
            ·
              refine ⟨3668097664895092576806485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445398443263395051204323 3668097664895092576806485)
              ·
                refine ⟨42985519510489366134451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3668097664895092576806485 42985519510489366134451)
                ·
                  rfl

theorem cell23_2260278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_2260278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260278 prefixEnd_2260278 := by exact prefixLift 2260278
  have htrace : WordTrace (prefixWord ++ tailWord_2260278) baseStart_2260278 baseEnd_2260278 := by
    simpa [prefixWord, tailWord_2260278, baseEnd_2260278] using wordTrace_append hprefix tailTrace_2260278
  have hstable : (prefixWord ++ tailWord_2260278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260278).length < 2 ^ (prefixWord ++ tailWord_2260278).sum := by decide
  have hdescent : baseEnd_2260278 < baseStart_2260278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260287 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 8]
def baseStart_2260287 : Nat := 118140960795 + 2260287 * 2 ^ 59
def prefixEnd_2260287 : Nat := 4983230072969 + 3 ^ 40 * 2260287 * 2
def baseEnd_2260287 : Nat := 386871216036367783472545

theorem tailTrace_2260287 : CollatzResearch.WordTrace tailWord_2260287 prefixEnd_2260287 386871216036367783472545 := by
  unfold tailWord_2260287
  simp only [CollatzResearch.WordTrace]
  refine ⟨82439439562373700131587115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54959626374915800087724743 82439439562373700131587115)
  ·
    refine ⟨123659159343560550197380673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82439439562373700131587115 123659159343560550197380673)
    ·
      refine ⟨92744369507670412648035505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123659159343560550197380673 92744369507670412648035505)
      ·
        refine ⟨69558277130752809486026629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92744369507670412648035505 69558277130752809486026629)
        ·
          refine ⟨13042176962016151778629993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69558277130752809486026629 13042176962016151778629993)
          ·
            refine ⟨9781632721512113833972495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13042176962016151778629993 9781632721512113833972495)
            ·
              refine ⟨14672449082268170750958743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781632721512113833972495 14672449082268170750958743)
              ·
                refine ⟨22008673623402256126438115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14672449082268170750958743 22008673623402256126438115)
                ·
                  refine ⟨33013010435103384189657173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22008673623402256126438115 33013010435103384189657173)
                  ·
                    refine ⟨386871216036367783472545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33013010435103384189657173 386871216036367783472545)
                    ·
                      rfl

theorem cell23_2260287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_2260287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260287 prefixEnd_2260287 := by exact prefixLift 2260287
  have htrace : WordTrace (prefixWord ++ tailWord_2260287) baseStart_2260287 baseEnd_2260287 := by
    simpa [prefixWord, tailWord_2260287, baseEnd_2260287] using wordTrace_append hprefix tailTrace_2260287
  have hstable : (prefixWord ++ tailWord_2260287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260287).length < 2 ^ (prefixWord ++ tailWord_2260287).sum := by decide
  have hdescent : baseEnd_2260287 < baseStart_2260287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260297 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_2260297 : Nat := 118140960795 + 2260297 * 2 ^ 59
def prefixEnd_2260297 : Nat := 4983230072969 + 3 ^ 40 * 2260297 * 2
def baseEnd_2260297 : Nat := 1160618782915648311292589

theorem tailTrace_2260297 : CollatzResearch.WordTrace tailWord_2260297 prefixEnd_2260297 1160618782915648311292589 := by
  unfold tailWord_2260297
  simp only [CollatzResearch.WordTrace]
  refine ⟨82439804292337471839451145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54959869528224981226300763 82439804292337471839451145)
  ·
    refine ⟨61829853219253103879588359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82439804292337471839451145 61829853219253103879588359)
    ·
      refine ⟨92744779828879655819382539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61829853219253103879588359 92744779828879655819382539)
      ·
        refine ⟨139117169743319483729073809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92744779828879655819382539 139117169743319483729073809)
        ·
          refine ⟨104337877307489612796805357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139117169743319483729073809 104337877307489612796805357)
          ·
            refine ⟨39126703990308604798802009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104337877307489612796805357 39126703990308604798802009)
            ·
              refine ⟨29345027992731453599101507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39126703990308604798802009 29345027992731453599101507)
              ·
                refine ⟨44017541989097180398652261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29345027992731453599101507 44017541989097180398652261)
                ·
                  refine ⟨8253289122955721324747299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44017541989097180398652261 8253289122955721324747299)
                  ·
                    refine ⟨12379933684433581987120949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8253289122955721324747299 12379933684433581987120949)
                    ·
                      refine ⟨1160618782915648311292589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12379933684433581987120949 1160618782915648311292589)
                      ·
                        rfl

theorem cell23_2260297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_2260297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260297 prefixEnd_2260297 := by exact prefixLift 2260297
  have htrace : WordTrace (prefixWord ++ tailWord_2260297) baseStart_2260297 baseEnd_2260297 := by
    simpa [prefixWord, tailWord_2260297, baseEnd_2260297] using wordTrace_append hprefix tailTrace_2260297
  have hstable : (prefixWord ++ tailWord_2260297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260297).length < 2 ^ (prefixWord ++ tailWord_2260297).sum := by decide
  have hdescent : baseEnd_2260297 < baseStart_2260297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260307 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_2260307 : Nat := 118140960795 + 2260307 * 2 ^ 59
def prefixEnd_2260307 : Nat := 4983230072969 + 3 ^ 40 * 2260307 * 2
def baseEnd_2260307 : Nat := 1160623917722193272167543

theorem tailTrace_2260307 : CollatzResearch.WordTrace tailWord_2260307 prefixEnd_2260307 1160623917722193272167543 := by
  unfold tailWord_2260307
  simp only [CollatzResearch.WordTrace]
  refine ⟨82440169022301243547315175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54960112681534162364876783 82440169022301243547315175)
  ·
    refine ⟨123660253533451865320972763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82440169022301243547315175 123660253533451865320972763)
    ·
      refine ⟨185490380300177797981459145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123660253533451865320972763 185490380300177797981459145)
      ·
        refine ⟨139117785225133348486094359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185490380300177797981459145 139117785225133348486094359)
        ·
          refine ⟨208676677837700022729141539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139117785225133348486094359 208676677837700022729141539)
          ·
            refine ⟨313015016756550034093712309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208676677837700022729141539 313015016756550034093712309)
            ·
              refine ⟨29345157820926565696285529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313015016756550034093712309 29345157820926565696285529)
              ·
                refine ⟨22008868365694924272214147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29345157820926565696285529 22008868365694924272214147)
                ·
                  refine ⟨33013302548542386408321221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22008868365694924272214147 33013302548542386408321221)
                  ·
                    refine ⟨6189994227851697451560229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33013302548542386408321221 6189994227851697451560229)
                    ·
                      refine ⟨1160623917722193272167543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6189994227851697451560229 1160623917722193272167543)
                      ·
                        rfl

theorem cell23_2260307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_2260307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260307 prefixEnd_2260307 := by exact prefixLift 2260307
  have htrace : WordTrace (prefixWord ++ tailWord_2260307) baseStart_2260307 baseEnd_2260307 := by
    simpa [prefixWord, tailWord_2260307, baseEnd_2260307] using wordTrace_append hprefix tailTrace_2260307
  have hstable : (prefixWord ++ tailWord_2260307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260307).length < 2 ^ (prefixWord ++ tailWord_2260307).sum := by decide
  have hdescent : baseEnd_2260307 < baseStart_2260307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260311 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_2260311 : Nat := 118140960795 + 2260311 * 2 ^ 59
def prefixEnd_2260311 : Nat := 4983230072969 + 3 ^ 40 * 2260311 * 2
def baseEnd_2260311 : Nat := 1160625971644811256517525

theorem tailTrace_2260311 : CollatzResearch.WordTrace tailWord_2260311 prefixEnd_2260311 1160625971644811256517525 := by
  unfold tailWord_2260311
  simp only [CollatzResearch.WordTrace]
  refine ⟨82440314914286752230460787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54960209942857834820307191 82440314914286752230460787)
  ·
    refine ⟨123660472371430128345691181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82440314914286752230460787 123660472371430128345691181)
    ·
      refine ⟨46372677139286298129634193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123660472371430128345691181 46372677139286298129634193)
      ·
        refine ⟨34779507854464723597225645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46372677139286298129634193 34779507854464723597225645)
        ·
          refine ⟨13042315445424271348959617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34779507854464723597225645 13042315445424271348959617)
          ·
            refine ⟨9781736584068203511719713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13042315445424271348959617 9781736584068203511719713)
            ·
              refine ⟨7336302438051152633789785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9781736584068203511719713 7336302438051152633789785)
              ·
                refine ⟨5502226828538364475342339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336302438051152633789785 5502226828538364475342339)
                ·
                  refine ⟨8253340242807546713013509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502226828538364475342339 8253340242807546713013509)
                  ·
                    refine ⟨1547501295526415008690033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8253340242807546713013509 1547501295526415008690033)
                    ·
                      refine ⟨1160625971644811256517525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547501295526415008690033 1160625971644811256517525)
                      ·
                        rfl

theorem cell23_2260311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_2260311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260311 prefixEnd_2260311 := by exact prefixLift 2260311
  have htrace : WordTrace (prefixWord ++ tailWord_2260311) baseStart_2260311 baseEnd_2260311 := by
    simpa [prefixWord, tailWord_2260311, baseEnd_2260311] using wordTrace_append hprefix tailTrace_2260311
  have hstable : (prefixWord ++ tailWord_2260311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260311).length < 2 ^ (prefixWord ++ tailWord_2260311).sum := by decide
  have hdescent : baseEnd_2260311 < baseStart_2260311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260324 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_2260324 : Nat := 118140960795 + 2260324 * 2 ^ 59
def prefixEnd_2260324 : Nat := 4983230072969 + 3 ^ 40 * 2260324 * 2
def baseEnd_2260324 : Nat := 1160632646893319705654965

theorem tailTrace_2260324 : CollatzResearch.WordTrace tailWord_2260324 prefixEnd_2260324 1160632646893319705654965 := by
  unfold tailWord_2260324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41220394531619827725342013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54960526042159770300456017 41220394531619827725342013)
  ·
    refine ⟨15457647949357435397003255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41220394531619827725342013 15457647949357435397003255)
    ·
      refine ⟨23186471924036153095504883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15457647949357435397003255 23186471924036153095504883)
      ·
        refine ⟨34779707886054229643257325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23186471924036153095504883 34779707886054229643257325)
        ·
          refine ⟨13042390457270336116221497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34779707886054229643257325 13042390457270336116221497)
          ·
            refine ⟨9781792842952752087166123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13042390457270336116221497 9781792842952752087166123)
            ·
              refine ⟨14672689264429128130749185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781792842952752087166123 14672689264429128130749185)
              ·
                refine ⟨11004516948321846098061889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14672689264429128130749185 11004516948321846098061889)
                ·
                  refine ⟨8253387711241384573546417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11004516948321846098061889 8253387711241384573546417)
                  ·
                    refine ⟨6190040783431038430159813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8253387711241384573546417 6190040783431038430159813)
                    ·
                      refine ⟨1160632646893319705654965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6190040783431038430159813 1160632646893319705654965)
                      ·
                        rfl

theorem cell23_2260324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_2260324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260324 prefixEnd_2260324 := by exact prefixLift 2260324
  have htrace : WordTrace (prefixWord ++ tailWord_2260324) baseStart_2260324 baseEnd_2260324 := by
    simpa [prefixWord, tailWord_2260324, baseEnd_2260324] using wordTrace_append hprefix tailTrace_2260324
  have hstable : (prefixWord ++ tailWord_2260324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260324).length < 2 ^ (prefixWord ++ tailWord_2260324).sum := by decide
  have hdescent : baseEnd_2260324 < baseStart_2260324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260347 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 7]
def baseStart_2260347 : Nat := 118140960795 + 2260347 * 2 ^ 59
def prefixEnd_2260347 : Nat := 4983230072969 + 3 ^ 40 * 2260347 * 2
def baseEnd_2260347 : Nat := 386881485649457705222453

theorem tailTrace_2260347 : CollatzResearch.WordTrace tailWord_2260347 prefixEnd_2260347 386881485649457705222453 := by
  unfold tailWord_2260347
  simp only [CollatzResearch.WordTrace]
  refine ⟨82441627942156330378771295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54961085294770886919180863 82441627942156330378771295)
  ·
    refine ⟨123662441913234495568156943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82441627942156330378771295 123662441913234495568156943)
    ·
      refine ⟨185493662869851743352235415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123662441913234495568156943 185493662869851743352235415)
      ·
        refine ⟨278240494304777615028353123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185493662869851743352235415 278240494304777615028353123)
        ·
          refine ⟨417360741457166422542529685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278240494304777615028353123 417360741457166422542529685)
          ·
            refine ⟨19563784755804676056681079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 417360741457166422542529685 19563784755804676056681079)
            ·
              refine ⟨29345677133707014085021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19563784755804676056681079 29345677133707014085021619)
              ·
                refine ⟨44018515700560521127532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29345677133707014085021619 44018515700560521127532429)
                ·
                  refine ⟨16506943387710195422824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44018515700560521127532429 16506943387710195422824661)
                  ·
                    refine ⟨386881485649457705222453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16506943387710195422824661 386881485649457705222453)
                    ·
                      rfl

theorem cell23_2260347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_2260347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260347 prefixEnd_2260347 := by exact prefixLift 2260347
  have htrace : WordTrace (prefixWord ++ tailWord_2260347) baseStart_2260347 baseEnd_2260347 := by
    simpa [prefixWord, tailWord_2260347, baseEnd_2260347] using wordTrace_append hprefix tailTrace_2260347
  have hstable : (prefixWord ++ tailWord_2260347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260347).length < 2 ^ (prefixWord ++ tailWord_2260347).sum := by decide
  have hdescent : baseEnd_2260347 < baseStart_2260347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260364 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_2260364 : Nat := 118140960795 + 2260364 * 2 ^ 59
def prefixEnd_2260364 : Nat := 4983230072969 + 3 ^ 40 * 2260364 * 2
def baseEnd_2260364 : Nat := 386884395373166516384927

theorem tailTrace_2260364 : CollatzResearch.WordTrace tailWord_2260364 prefixEnd_2260364 386884395373166516384927 := by
  unfold tailWord_2260364
  simp only [CollatzResearch.WordTrace]
  refine ⟨41221123991547371141070073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54961498655396494854760097 41221123991547371141070073)
  ·
    refine ⟨30915842993660528355802555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41221123991547371141070073 30915842993660528355802555)
    ·
      refine ⟨46373764490490792533703833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30915842993660528355802555 46373764490490792533703833)
      ·
        refine ⟨34780323367868094400277875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46373764490490792533703833 34780323367868094400277875)
        ·
          refine ⟨52170485051802141600416813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34780323367868094400277875 52170485051802141600416813)
          ·
            refine ⟨19563931894425803100156305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52170485051802141600416813 19563931894425803100156305)
            ·
              refine ⟨14672948920819352325117229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19563931894425803100156305 14672948920819352325117229)
              ·
                refine ⟨5502355845307257121918961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14672948920819352325117229 5502355845307257121918961)
                ·
                  refine ⟨4126766883980442841439221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502355845307257121918961 4126766883980442841439221)
                  ·
                    refine ⟨386884395373166516384927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4126766883980442841439221 386884395373166516384927)
                    ·
                      rfl

theorem cell23_2260364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_2260364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260364 prefixEnd_2260364 := by exact prefixLift 2260364
  have htrace : WordTrace (prefixWord ++ tailWord_2260364) baseStart_2260364 baseEnd_2260364 := by
    simpa [prefixWord, tailWord_2260364, baseEnd_2260364] using wordTrace_append hprefix tailTrace_2260364
  have hstable : (prefixWord ++ tailWord_2260364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260364).length < 2 ^ (prefixWord ++ tailWord_2260364).sum := by decide
  have hdescent : baseEnd_2260364 < baseStart_2260364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260381 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2260381 : Nat := 118140960795 + 2260381 * 2 ^ 59
def prefixEnd_2260381 : Nat := 4983230072969 + 3 ^ 40 * 2260381 * 2
def baseEnd_2260381 : Nat := 386887305096875327547401

theorem tailTrace_2260381 : CollatzResearch.WordTrace tailWord_2260381 prefixEnd_2260381 386887305096875327547401 := by
  unfold tailWord_2260381
  simp only [CollatzResearch.WordTrace]
  refine ⟨82442868024033154185508997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54961912016022102790339331 82442868024033154185508997)
  ·
    refine ⟨15458037754506216409782937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82442868024033154185508997 15458037754506216409782937)
    ·
      refine ⟨11593528315879662307337203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15458037754506216409782937 11593528315879662307337203)
      ·
        refine ⟨17390292473819493461005805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11593528315879662307337203 17390292473819493461005805)
        ·
          refine ⟨6521359677682310047877177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17390292473819493461005805 6521359677682310047877177)
          ·
            refine ⟨4891019758261732535907883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6521359677682310047877177 4891019758261732535907883)
            ·
              refine ⟨7336529637392598803861825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891019758261732535907883 7336529637392598803861825)
              ·
                refine ⟨5502397228044449102896369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336529637392598803861825 5502397228044449102896369)
                ·
                  refine ⟨4126797921033336827172277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502397228044449102896369 4126797921033336827172277)
                  ·
                    refine ⟨386887305096875327547401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4126797921033336827172277 386887305096875327547401)
                    ·
                      rfl

theorem cell23_2260381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2260381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260381 prefixEnd_2260381 := by exact prefixLift 2260381
  have htrace : WordTrace (prefixWord ++ tailWord_2260381) baseStart_2260381 baseEnd_2260381 := by
    simpa [prefixWord, tailWord_2260381, baseEnd_2260381] using wordTrace_append hprefix tailTrace_2260381
  have hstable : (prefixWord ++ tailWord_2260381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260381).length < 2 ^ (prefixWord ++ tailWord_2260381).sum := by decide
  have hdescent : baseEnd_2260381 < baseStart_2260381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260401 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2260401 : Nat := 118140960795 + 2260401 * 2 ^ 59
def prefixEnd_2260401 : Nat := 4983230072969 + 3 ^ 40 * 2260401 * 2
def baseEnd_2260401 : Nat := 1160672184903715904392111

theorem tailTrace_2260401 : CollatzResearch.WordTrace tailWord_2260401 prefixEnd_2260401 1160672184903715904392111 := by
  unfold tailWord_2260401
  simp only [CollatzResearch.WordTrace]
  refine ⟨82443597483960697601237057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54962398322640465067491371 82443597483960697601237057)
  ·
    refine ⟨61832698112970523200927793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82443597483960697601237057 61832698112970523200927793)
    ·
      refine ⟨46374523584727892400695845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61832698112970523200927793 46374523584727892400695845)
      ·
        refine ⟨8695223172136479825130471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46374523584727892400695845 8695223172136479825130471)
        ·
          refine ⟨13042834758204719737695707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695223172136479825130471 13042834758204719737695707)
          ·
            refine ⟨19564252137307079606543561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13042834758204719737695707 19564252137307079606543561)
            ·
              refine ⟨14673189102980309704907671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19564252137307079606543561 14673189102980309704907671)
              ·
                refine ⟨22009783654470464557361507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14673189102980309704907671 22009783654470464557361507)
                ·
                  refine ⟨33014675481705696836042261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22009783654470464557361507 33014675481705696836042261)
                  ·
                    refine ⟨1547562913204954539189481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33014675481705696836042261 1547562913204954539189481)
                    ·
                      refine ⟨1160672184903715904392111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547562913204954539189481 1160672184903715904392111)
                      ·
                        rfl

theorem cell23_2260401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2260401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260401 prefixEnd_2260401 := by exact prefixLift 2260401
  have htrace : WordTrace (prefixWord ++ tailWord_2260401) baseStart_2260401 baseEnd_2260401 := by
    simpa [prefixWord, tailWord_2260401, baseEnd_2260401] using wordTrace_append hprefix tailTrace_2260401
  have hstable : (prefixWord ++ tailWord_2260401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260401).length < 2 ^ (prefixWord ++ tailWord_2260401).sum := by decide
  have hdescent : baseEnd_2260401 < baseStart_2260401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260414 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2260414 : Nat := 118140960795 + 2260414 * 2 ^ 59
def prefixEnd_2260414 : Nat := 4983230072969 + 3 ^ 40 * 2260414 * 2
def baseEnd_2260414 : Nat := 1160678860152224353529551

theorem tailTrace_2260414 : CollatzResearch.WordTrace tailWord_2260414 prefixEnd_2260414 1160678860152224353529551 := by
  unfold tailWord_2260414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305508954114200102682537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54962714421942400547640197 10305508954114200102682537)
  ·
    refine ⟨7729131715585650077011903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10305508954114200102682537 7729131715585650077011903)
    ·
      refine ⟨11593697573378475115517855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729131715585650077011903 11593697573378475115517855)
      ·
        refine ⟨17390546360067712673276783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11593697573378475115517855 17390546360067712673276783)
        ·
          refine ⟨26085819540101569009915175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17390546360067712673276783 26085819540101569009915175)
          ·
            refine ⟨39128729310152353514872763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26085819540101569009915175 39128729310152353514872763)
            ·
              refine ⟨58693093965228530272309145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39128729310152353514872763 58693093965228530272309145)
              ·
                refine ⟨44019820473921397704231859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58693093965228530272309145 44019820473921397704231859)
                ·
                  refine ⟨66029730710882096556347789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44019820473921397704231859 66029730710882096556347789)
                  ·
                    refine ⟨24761149016580786208630421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66029730710882096556347789 24761149016580786208630421)
                    ·
                      refine ⟨1160678860152224353529551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24761149016580786208630421 1160678860152224353529551)
                      ·
                        rfl

theorem cell23_2260414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2260414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260414 prefixEnd_2260414 := by exact prefixLift 2260414
  have htrace : WordTrace (prefixWord ++ tailWord_2260414) baseStart_2260414 baseEnd_2260414 := by
    simpa [prefixWord, tailWord_2260414, baseEnd_2260414] using wordTrace_append hprefix tailTrace_2260414
  have hstable : (prefixWord ++ tailWord_2260414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260414).length < 2 ^ (prefixWord ++ tailWord_2260414).sum := by decide
  have hdescent : baseEnd_2260414 < baseStart_2260414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260441 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 6]
def baseStart_2260441 : Nat := 118140960795 + 2260441 * 2 ^ 59
def prefixEnd_2260441 : Nat := 4983230072969 + 3 ^ 40 * 2260441 * 2
def baseEnd_2260441 : Nat := 128965858236655083099103

theorem tailTrace_2260441 : CollatzResearch.WordTrace tailWord_2260441 prefixEnd_2260441 128965858236655083099103 := by
  unfold tailWord_2260441
  simp only [CollatzResearch.WordTrace]
  refine ⟨82445056403815784432693177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54963370935877189621795451 82445056403815784432693177)
  ·
    refine ⟨61833792302861838324519883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82445056403815784432693177 61833792302861838324519883)
    ·
      refine ⟨92750688454292757486779825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61833792302861838324519883 92750688454292757486779825)
      ·
        refine ⟨69563016340719568115084869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92750688454292757486779825 69563016340719568115084869)
        ·
          refine ⟨13043065563884919021578413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69563016340719568115084869 13043065563884919021578413)
          ·
            refine ⟨4891149586456844633091905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13043065563884919021578413 4891149586456844633091905)
            ·
              refine ⟨3668362189842633474818929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4891149586456844633091905 3668362189842633474818929)
              ·
                refine ⟨2751271642381975106114197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3668362189842633474818929 2751271642381975106114197)
                ·
                  refine ⟨128965858236655083099103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2751271642381975106114197 128965858236655083099103)
                  ·
                    rfl

theorem cell23_2260441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_2260441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260441 prefixEnd_2260441 := by exact prefixLift 2260441
  have htrace : WordTrace (prefixWord ++ tailWord_2260441) baseStart_2260441 baseEnd_2260441 := by
    simpa [prefixWord, tailWord_2260441, baseEnd_2260441] using wordTrace_append hprefix tailTrace_2260441
  have hstable : (prefixWord ++ tailWord_2260441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260441).length < 2 ^ (prefixWord ++ tailWord_2260441).sum := by decide
  have hdescent : baseEnd_2260441 < baseStart_2260441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260445 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2260445 : Nat := 118140960795 + 2260445 * 2 ^ 59
def prefixEnd_2260445 : Nat := 4983230072969 + 3 ^ 40 * 2260445 * 2
def baseEnd_2260445 : Nat := 386898259350837910747303

theorem tailTrace_2260445 : CollatzResearch.WordTrace tailWord_2260445 prefixEnd_2260445 386898259350837910747303 := by
  unfold tailWord_2260445
  simp only [CollatzResearch.WordTrace]
  refine ⟨82445202295801293115838789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54963468197200862077225859 82445202295801293115838789)
  ·
    refine ⟨15458475430462742459219773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82445202295801293115838789 15458475430462742459219773)
    ·
      refine ⟨5796928286423528422207415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15458475430462742459219773 5796928286423528422207415)
      ·
        refine ⟨8695392429635292633311123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796928286423528422207415 8695392429635292633311123)
        ·
          refine ⟨13043088644452938949966685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695392429635292633311123 13043088644452938949966685)
          ·
            refine ⟨4891158241669852106237507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13043088644452938949966685 4891158241669852106237507)
            ·
              refine ⟨7336737362504778159356261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891158241669852106237507 7336737362504778159356261)
              ·
                refine ⟨1375638255469645904879299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7336737362504778159356261 1375638255469645904879299)
                ·
                  refine ⟨2063457383204468857318949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375638255469645904879299 2063457383204468857318949)
                  ·
                    refine ⟨386898259350837910747303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2063457383204468857318949 386898259350837910747303)
                    ·
                      rfl

theorem cell23_2260445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2260445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260445 prefixEnd_2260445 := by exact prefixLift 2260445
  have htrace : WordTrace (prefixWord ++ tailWord_2260445) baseStart_2260445 baseEnd_2260445 := by
    simpa [prefixWord, tailWord_2260445, baseEnd_2260445] using wordTrace_append hprefix tailTrace_2260445
  have hstable : (prefixWord ++ tailWord_2260445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260445).length < 2 ^ (prefixWord ++ tailWord_2260445).sum := by decide
  have hdescent : baseEnd_2260445 < baseStart_2260445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260488 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_2260488 : Nat := 118140960795 + 2260488 * 2 ^ 59
def prefixEnd_2260488 : Nat := 4983230072969 + 3 ^ 40 * 2260488 * 2
def baseEnd_2260488 : Nat := 386905619240219021334737

theorem tailTrace_2260488 : CollatzResearch.WordTrace tailWord_2260488 prefixEnd_2260488 386905619240219021334737 := by
  unfold tailWord_2260488
  simp only [CollatzResearch.WordTrace]
  refine ⟨41223385317322755729827059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54964513756430340973102745 41223385317322755729827059)
  ·
    refine ⟨61835077975984133594740589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41223385317322755729827059 61835077975984133594740589)
    ·
      refine ⟨23188154240994050098027721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61835077975984133594740589 23188154240994050098027721)
      ·
        refine ⟨17391115680745537573520791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23188154240994050098027721 17391115680745537573520791)
        ·
          refine ⟨26086673521118306360281187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17391115680745537573520791 26086673521118306360281187)
          ·
            refine ⟨39130010281677459540421781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26086673521118306360281187 39130010281677459540421781)
            ·
              refine ⟨1834219231953630915957271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39130010281677459540421781 1834219231953630915957271)
              ·
                refine ⟨2751328847930446373935907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834219231953630915957271 2751328847930446373935907)
                ·
                  refine ⟨4126993271895669560903861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751328847930446373935907 4126993271895669560903861)
                  ·
                    refine ⟨386905619240219021334737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4126993271895669560903861 386905619240219021334737)
                    ·
                      rfl

theorem cell23_2260488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_2260488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260488 prefixEnd_2260488 := by exact prefixLift 2260488
  have htrace : WordTrace (prefixWord ++ tailWord_2260488) baseStart_2260488 baseEnd_2260488 := by
    simpa [prefixWord, tailWord_2260488, baseEnd_2260488] using wordTrace_append hprefix tailTrace_2260488
  have hstable : (prefixWord ++ tailWord_2260488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260488).length < 2 ^ (prefixWord ++ tailWord_2260488).sum := by decide
  have hdescent : baseEnd_2260488 < baseStart_2260488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260511 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2260511 : Nat := 118140960795 + 2260511 * 2 ^ 59
def prefixEnd_2260511 : Nat := 4983230072969 + 3 ^ 40 * 2260511 * 2
def baseEnd_2260511 : Nat := 1160728667775710474016605

theorem tailTrace_2260511 : CollatzResearch.WordTrace tailWord_2260511 prefixEnd_2260511 1160728667775710474016605 := by
  unfold tailWord_2260511
  simp only [CollatzResearch.WordTrace]
  refine ⟨82447609513562186387741387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54965073009041457591827591 82447609513562186387741387)
  ·
    refine ⟨123671414270343279581612081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82447609513562186387741387 123671414270343279581612081)
    ·
      refine ⟨92753560702757459686209061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123671414270343279581612081 92753560702757459686209061)
      ·
        refine ⟨17391292631767023691164199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92753560702757459686209061 17391292631767023691164199)
        ·
          refine ⟨26086938947650535536746299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17391292631767023691164199 26086938947650535536746299)
          ·
            refine ⟨39130408421475803305119449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26086938947650535536746299 39130408421475803305119449)
            ·
              refine ⟨29347806316106852478839587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39130408421475803305119449 29347806316106852478839587)
              ·
                refine ⟨44021709474160278718259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29347806316106852478839587 44021709474160278718259381)
                ·
                  refine ⟨4127035263202526129836817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44021709474160278718259381 4127035263202526129836817)
                  ·
                    refine ⟨3095276447401894597377613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4127035263202526129836817 3095276447401894597377613)
                    ·
                      refine ⟨1160728667775710474016605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095276447401894597377613 1160728667775710474016605)
                      ·
                        rfl

theorem cell23_2260511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2260511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260511 prefixEnd_2260511 := by exact prefixLift 2260511
  have htrace : WordTrace (prefixWord ++ tailWord_2260511) baseStart_2260511 baseEnd_2260511 := by
    simpa [prefixWord, tailWord_2260511, baseEnd_2260511] using wordTrace_append hprefix tailTrace_2260511
  have hstable : (prefixWord ++ tailWord_2260511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260511).length < 2 ^ (prefixWord ++ tailWord_2260511).sum := by decide
  have hdescent : baseEnd_2260511 < baseStart_2260511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260531 : List Nat := [1, 1, 1, 2, 4, 3, 4, 7]
def baseStart_2260531 : Nat := 118140960795 + 2260531 * 2 ^ 59
def prefixEnd_2260531 : Nat := 4983230072969 + 3 ^ 40 * 2260531 * 2
def baseEnd_2260531 : Nat := 42990331014400014658019

theorem tailTrace_2260531 : CollatzResearch.WordTrace tailWord_2260531 prefixEnd_2260531 42990331014400014658019 := by
  unfold tailWord_2260531
  simp only [CollatzResearch.WordTrace]
  refine ⟨82448338973489729803469447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54965559315659819868979631 82448338973489729803469447)
  ·
    refine ⟨123672508460234594705204171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82448338973489729803469447 123672508460234594705204171)
    ·
      refine ⟨185508762690351892057806257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123672508460234594705204171 185508762690351892057806257)
      ·
        refine ⟨139131572017763919043354693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185508762690351892057806257 139131572017763919043354693)
        ·
          refine ⟨26087169753330734820629005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139131572017763919043354693 26087169753330734820629005)
          ·
            refine ⟨9782688657499025557735877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26087169753330734820629005 9782688657499025557735877)
            ·
              refine ⟨1834254123281067292075477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9782688657499025557735877 1834254123281067292075477)
              ·
                refine ⟨42990331014400014658019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1834254123281067292075477 42990331014400014658019)
                ·
                  rfl

theorem cell23_2260531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 7].length) (baseStart_2260531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260531 prefixEnd_2260531 := by exact prefixLift 2260531
  have htrace : WordTrace (prefixWord ++ tailWord_2260531) baseStart_2260531 baseEnd_2260531 := by
    simpa [prefixWord, tailWord_2260531, baseEnd_2260531] using wordTrace_append hprefix tailTrace_2260531
  have hstable : (prefixWord ++ tailWord_2260531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260531).length < 2 ^ (prefixWord ++ tailWord_2260531).sum := by decide
  have hdescent : baseEnd_2260531 < baseStart_2260531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260544 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_2260544 : Nat := 118140960795 + 2260544 * 2 ^ 59
def prefixEnd_2260544 : Nat := 4983230072969 + 3 ^ 40 * 2260544 * 2
def baseEnd_2260544 : Nat := 386915204212436281634651

theorem tailTrace_2260544 : CollatzResearch.WordTrace tailWord_2260544 prefixEnd_2260544 386915204212436281634651 := by
  unfold tailWord_2260544
  simp only [CollatzResearch.WordTrace]
  refine ⟨41224406561221316511846343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54965875414961755349128457 41224406561221316511846343)
  ·
    refine ⟨61836609841831974767769515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41224406561221316511846343 61836609841831974767769515)
    ·
      refine ⟨92754914762747962151654273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61836609841831974767769515 92754914762747962151654273)
      ·
        refine ⟨69566186072060971613740705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92754914762747962151654273 69566186072060971613740705)
        ·
          refine ⟨52174639554045728710305529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69566186072060971613740705 52174639554045728710305529)
          ·
            refine ⟨39130979665534296532729147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52174639554045728710305529 39130979665534296532729147)
            ·
              refine ⟨58696469498301444799093721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39130979665534296532729147 58696469498301444799093721)
              ·
                refine ⟨44022352123726083599320291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58696469498301444799093721 44022352123726083599320291)
                ·
                  refine ⟨66033528185589125398980437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44022352123726083599320291 66033528185589125398980437)
                  ·
                    refine ⟨386915204212436281634651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66033528185589125398980437 386915204212436281634651)
                    ·
                      rfl

theorem cell23_2260544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_2260544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260544 prefixEnd_2260544 := by exact prefixLift 2260544
  have htrace : WordTrace (prefixWord ++ tailWord_2260544) baseStart_2260544 baseEnd_2260544 := by
    simpa [prefixWord, tailWord_2260544, baseEnd_2260544] using wordTrace_append hprefix tailTrace_2260544
  have hstable : (prefixWord ++ tailWord_2260544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260544).length < 2 ^ (prefixWord ++ tailWord_2260544).sum := by decide
  have hdescent : baseEnd_2260544 < baseStart_2260544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_2260568 : Nat := 118140960795 + 2260568 * 2 ^ 59
def prefixEnd_2260568 : Nat := 4983230072969 + 3 ^ 40 * 2260568 * 2
def baseEnd_2260568 : Nat := 1160757936173016751003843

theorem tailTrace_2260568 : CollatzResearch.WordTrace tailWord_2260568 prefixEnd_2260568 1160757936173016751003843 := by
  unfold tailWord_2260568
  simp only [CollatzResearch.WordTrace]
  refine ⟨41224844237177842561283179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54966458982903790081710905 41224844237177842561283179)
  ·
    refine ⟨61837266355766763841924769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41224844237177842561283179 61837266355766763841924769)
    ·
      refine ⟨46377949766825072881443577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61837266355766763841924769 46377949766825072881443577)
      ·
        refine ⟨34783462325118804661082683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46377949766825072881443577 34783462325118804661082683)
        ·
          refine ⟨52175193487678206991624025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34783462325118804661082683 52175193487678206991624025)
          ·
            refine ⟨39131395115758655243718019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52175193487678206991624025 39131395115758655243718019)
            ·
              refine ⟨58697092673637982865577029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39131395115758655243718019 58697092673637982865577029)
              ·
                refine ⟨11005704876307121787295693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58697092673637982865577029 11005704876307121787295693)
                ·
                  refine ⟨4127139328615170670235885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11005704876307121787295693 4127139328615170670235885)
                  ·
                    refine ⟨1547677248230689001338457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4127139328615170670235885 1547677248230689001338457)
                    ·
                      refine ⟨1160757936173016751003843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547677248230689001338457 1160757936173016751003843)
                      ·
                        rfl

theorem cell23_2260568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_2260568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260568 prefixEnd_2260568 := by exact prefixLift 2260568
  have htrace : WordTrace (prefixWord ++ tailWord_2260568) baseStart_2260568 baseEnd_2260568 := by
    simpa [prefixWord, tailWord_2260568, baseEnd_2260568] using wordTrace_append hprefix tailTrace_2260568
  have hstable : (prefixWord ++ tailWord_2260568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260568).length < 2 ^ (prefixWord ++ tailWord_2260568).sum := by decide
  have hdescent : baseEnd_2260568 < baseStart_2260568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260585 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 1, 3, 2]
def baseStart_2260585 : Nat := 118140960795 + 2260585 * 2 ^ 59
def prefixEnd_2260585 : Nat := 4983230072969 + 3 ^ 40 * 2260585 * 2
def baseEnd_2260585 : Nat := 1160766665344143184491265

theorem tailTrace_2260585 : CollatzResearch.WordTrace tailWord_2260585 prefixEnd_2260585 1160766665344143184491265 := by
  unfold tailWord_2260585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82450308515294097025935209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54966872343529398017290139 82450308515294097025935209)
  ·
    refine ⟨61837731386470572769451407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82450308515294097025935209 61837731386470572769451407)
    ·
      refine ⟨92756597079705859154177111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61837731386470572769451407 92756597079705859154177111)
      ·
        refine ⟨139134895619558788731265667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92756597079705859154177111 139134895619558788731265667)
        ·
          refine ⟨208702343429338183096898501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139134895619558788731265667 208702343429338183096898501)
          ·
            refine ⟨39131689393000909330668469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208702343429338183096898501 39131689393000909330668469)
            ·
              refine ⟨3668595880593835249750169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39131689393000909330668469 3668595880593835249750169)
              ·
                refine ⟨2751446910445376437312627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3668595880593835249750169 2751446910445376437312627)
                ·
                  refine ⟨4127170365668064655968941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751446910445376437312627 4127170365668064655968941)
                  ·
                    refine ⟨1547688887125524245988353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4127170365668064655968941 1547688887125524245988353)
                    ·
                      refine ⟨1160766665344143184491265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547688887125524245988353 1160766665344143184491265)
                      ·
                        rfl

theorem cell23_2260585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3, 2].length) (baseStart_2260585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260585 prefixEnd_2260585 := by exact prefixLift 2260585
  have htrace : WordTrace (prefixWord ++ tailWord_2260585) baseStart_2260585 baseEnd_2260585 := by
    simpa [prefixWord, tailWord_2260585, baseEnd_2260585] using wordTrace_append hprefix tailTrace_2260585
  have hstable : (prefixWord ++ tailWord_2260585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260585).length < 2 ^ (prefixWord ++ tailWord_2260585).sum := by decide
  have hdescent : baseEnd_2260585 < baseStart_2260585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260601 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2260601 : Nat := 118140960795 + 2260601 * 2 ^ 59
def prefixEnd_2260601 : Nat := 4983230072969 + 3 ^ 40 * 2260601 * 2
def baseEnd_2260601 : Nat := 1160774881034615121891191

theorem tailTrace_2260601 : CollatzResearch.WordTrace tailWord_2260601 prefixEnd_2260601 1160774881034615121891191 := by
  unfold tailWord_2260601
  simp only [CollatzResearch.WordTrace]
  refine ⟨82450892083236131758517657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54967261388824087839011771 82450892083236131758517657)
  ·
    refine ⟨61838169062427098818888243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82450892083236131758517657 61838169062427098818888243)
    ·
      refine ⟨92757253593640648228332365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61838169062427098818888243 92757253593640648228332365)
      ·
        refine ⟨34783970097615243085624637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92757253593640648228332365 34783970097615243085624637)
        ·
          refine ⟨13043988786605716157109239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34783970097615243085624637 13043988786605716157109239)
          ·
            refine ⟨19565983179908574235663859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13043988786605716157109239 19565983179908574235663859)
            ·
              refine ⟨29348974769862861353495789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19565983179908574235663859 29348974769862861353495789)
              ·
                refine ⟨11005865538698573007560921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29348974769862861353495789 11005865538698573007560921)
                ·
                  refine ⟨8254399154023929755670691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11005865538698573007560921 8254399154023929755670691)
                  ·
                    refine ⟨12381598731035894633506037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8254399154023929755670691 12381598731035894633506037)
                    ·
                      refine ⟨1160774881034615121891191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12381598731035894633506037 1160774881034615121891191)
                      ·
                        rfl

theorem cell23_2260601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2260601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260601 prefixEnd_2260601 := by exact prefixLift 2260601
  have htrace : WordTrace (prefixWord ++ tailWord_2260601) baseStart_2260601 baseEnd_2260601 := by
    simpa [prefixWord, tailWord_2260601, baseEnd_2260601] using wordTrace_append hprefix tailTrace_2260601
  have hstable : (prefixWord ++ tailWord_2260601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260601).length < 2 ^ (prefixWord ++ tailWord_2260601).sum := by decide
  have hdescent : baseEnd_2260601 < baseStart_2260601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260611 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2260611 : Nat := 118140960795 + 2260611 * 2 ^ 59
def prefixEnd_2260611 : Nat := 4983230072969 + 3 ^ 40 * 2260611 * 2
def baseEnd_2260611 : Nat := 1160780015841160082766145

theorem tailTrace_2260611 : CollatzResearch.WordTrace tailWord_2260611 prefixEnd_2260611 1160780015841160082766145 := by
  unfold tailWord_2260611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82451256813199903466381687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54967504542133268977587791 82451256813199903466381687)
  ·
    refine ⟨123676885219799855199572531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82451256813199903466381687 123676885219799855199572531)
    ·
      refine ⟨185515327829699782799358797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123676885219799855199572531 185515327829699782799358797)
      ·
        refine ⟨69568247936137418549759549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185515327829699782799358797 69568247936137418549759549)
        ·
          refine ⟨26088092976051531956159831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69568247936137418549759549 26088092976051531956159831)
          ·
            refine ⟨39132139464077297934239747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26088092976051531956159831 39132139464077297934239747)
            ·
              refine ⟨58698209196115946901359621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39132139464077297934239747 58698209196115946901359621)
              ·
                refine ⟨11005914224271740044004929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58698209196115946901359621 11005914224271740044004929)
                ·
                  refine ⟨8254435668203805033003697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11005914224271740044004929 8254435668203805033003697)
                  ·
                    refine ⟨6190826751152853774752773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8254435668203805033003697 6190826751152853774752773)
                    ·
                      refine ⟨1160780015841160082766145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6190826751152853774752773 1160780015841160082766145)
                      ·
                        rfl

theorem cell23_2260611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2260611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260611 prefixEnd_2260611 := by exact prefixLift 2260611
  have htrace : WordTrace (prefixWord ++ tailWord_2260611) baseStart_2260611 baseEnd_2260611 := by
    simpa [prefixWord, tailWord_2260611, baseEnd_2260611] using wordTrace_append hprefix tailTrace_2260611
  have hstable : (prefixWord ++ tailWord_2260611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260611).length < 2 ^ (prefixWord ++ tailWord_2260611).sum := by decide
  have hdescent : baseEnd_2260611 < baseStart_2260611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260618 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2260618 : Nat := 118140960795 + 2260618 * 2 ^ 59
def prefixEnd_2260618 : Nat := 4983230072969 + 3 ^ 40 * 2260618 * 2
def baseEnd_2260618 : Nat := 1160783610205741555378613

theorem tailTrace_2260618 : CollatzResearch.WordTrace tailWord_2260618 prefixEnd_2260618 1160783610205741555378613 := by
  unfold tailWord_2260618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612878031043635915471627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54967674749449695774591005 20612878031043635915471627)
  ·
    refine ⟨30919317046565453873207441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20612878031043635915471627 30919317046565453873207441)
    ·
      refine ⟨23189487784924090404905581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30919317046565453873207441 23189487784924090404905581)
      ·
        refine ⟨8696057919346533901839593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23189487784924090404905581 8696057919346533901839593)
        ·
          refine ⟨6522043439509900426379695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8696057919346533901839593 6522043439509900426379695)
          ·
            refine ⟨9783065159264850639569543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522043439509900426379695 9783065159264850639569543)
            ·
              refine ⟨14674597738897275959354315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9783065159264850639569543 14674597738897275959354315)
              ·
                refine ⟨22011896608345913939031473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14674597738897275959354315 22011896608345913939031473)
                ·
                  refine ⟨16508922456259435454273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22011896608345913939031473 16508922456259435454273605)
                  ·
                    refine ⟨3095422960548644147676301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16508922456259435454273605 3095422960548644147676301)
                    ·
                      refine ⟨1160783610205741555378613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095422960548644147676301 1160783610205741555378613)
                      ·
                        rfl

theorem cell23_2260618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2260618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260618 prefixEnd_2260618 := by exact prefixLift 2260618
  have htrace : WordTrace (prefixWord ++ tailWord_2260618) baseStart_2260618 baseEnd_2260618 := by
    simpa [prefixWord, tailWord_2260618, baseEnd_2260618] using wordTrace_append hprefix tailTrace_2260618
  have hstable : (prefixWord ++ tailWord_2260618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260618).length < 2 ^ (prefixWord ++ tailWord_2260618).sum := by decide
  have hdescent : baseEnd_2260618 < baseStart_2260618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260632 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2260632 : Nat := 118140960795 + 2260632 * 2 ^ 59
def prefixEnd_2260632 : Nat := 4983230072969 + 3 ^ 40 * 2260632 * 2
def baseEnd_2260632 : Nat := 1160790798934904500603549

theorem tailTrace_2260632 : CollatzResearch.WordTrace tailWord_2260632 prefixEnd_2260632 1160790798934904500603549 := by
  unfold tailWord_2260632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41226011373061912026448075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54968015164082549368597433 41226011373061912026448075)
  ·
    refine ⟨61839017059592868039672113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41226011373061912026448075 61839017059592868039672113)
    ·
      refine ⟨46379262794694651029754085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61839017059592868039672113 46379262794694651029754085)
      ·
        refine ⟨8696111774005247068078891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46379262794694651029754085 8696111774005247068078891)
        ·
          refine ⟨13044167661007870602118337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8696111774005247068078891 13044167661007870602118337)
          ·
            refine ⟨9783125745755902951588753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13044167661007870602118337 9783125745755902951588753)
            ·
              refine ⟨7337344309316927213691565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783125745755902951588753 7337344309316927213691565)
              ·
                refine ⟨2751504115993847705134337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7337344309316927213691565 2751504115993847705134337)
                ·
                  refine ⟨2063628086995385778850753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751504115993847705134337 2063628086995385778850753)
                  ·
                    refine ⟨1547721065246539334138065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2063628086995385778850753 1547721065246539334138065)
                    ·
                      refine ⟨1160790798934904500603549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547721065246539334138065 1160790798934904500603549)
                      ·
                        rfl

theorem cell23_2260632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2260632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260632 prefixEnd_2260632 := by exact prefixLift 2260632
  have htrace : WordTrace (prefixWord ++ tailWord_2260632) baseStart_2260632 baseEnd_2260632 := by
    simpa [prefixWord, tailWord_2260632, baseEnd_2260632] using wordTrace_append hprefix tailTrace_2260632
  have hstable : (prefixWord ++ tailWord_2260632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260632).length < 2 ^ (prefixWord ++ tailWord_2260632).sum := by decide
  have hdescent : baseEnd_2260632 < baseStart_2260632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260638 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2260638 : Nat := 118140960795 + 2260638 * 2 ^ 59
def prefixEnd_2260638 : Nat := 4983230072969 + 3 ^ 40 * 2260638 * 2
def baseEnd_2260638 : Nat := 128977097757647941903169

theorem tailTrace_2260638 : CollatzResearch.WordTrace tailWord_2260638 prefixEnd_2260638 128977097757647941903169 := by
  unfold tailWord_2260638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306530198012760884701821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54968161056068058051743045 10306530198012760884701821)
  ·
    refine ⟨3864948824254785331763183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10306530198012760884701821 3864948824254785331763183)
    ·
      refine ⟨5797423236382177997644775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3864948824254785331763183 5797423236382177997644775)
      ·
        refine ⟨8696134854573266996467163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797423236382177997644775 8696134854573266996467163)
        ·
          refine ⟨13044202281859900494700745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8696134854573266996467163 13044202281859900494700745)
          ·
            refine ⟨9783151711394925371025559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13044202281859900494700745 9783151711394925371025559)
            ·
              refine ⟨14674727567092388056538339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9783151711394925371025559 14674727567092388056538339)
              ·
                refine ⟨22012091350638582084807509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14674727567092388056538339 22012091350638582084807509)
                ·
                  refine ⟨128977097757647941903169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22012091350638582084807509 128977097757647941903169)
                  ·
                    rfl

theorem cell23_2260638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2260638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260638 prefixEnd_2260638 := by exact prefixLift 2260638
  have htrace : WordTrace (prefixWord ++ tailWord_2260638) baseStart_2260638 baseEnd_2260638 := by
    simpa [prefixWord, tailWord_2260638, baseEnd_2260638] using wordTrace_append hprefix tailTrace_2260638
  have hstable : (prefixWord ++ tailWord_2260638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260638).length < 2 ^ (prefixWord ++ tailWord_2260638).sum := by decide
  have hdescent : baseEnd_2260638 < baseStart_2260638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260685 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2260685 : Nat := 118140960795 + 2260685 * 2 ^ 59
def prefixEnd_2260685 : Nat := 4983230072969 + 3 ^ 40 * 2260685 * 2
def baseEnd_2260685 : Nat := 386939337803197597746935

theorem tailTrace_2260685 : CollatzResearch.WordTrace tailWord_2260685 prefixEnd_2260685 386939337803197597746935 := by
  unfold tailWord_2260685
  simp only [CollatzResearch.WordTrace]
  refine ⟨82453955814931814104575509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54969303876621209403050339 82453955814931814104575509)
  ·
    refine ⟨3865029178824928786151977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82453955814931814104575509 3865029178824928786151977)
    ·
      refine ⟨2898771884118696589613983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3865029178824928786151977 2898771884118696589613983)
      ·
        refine ⟨4348157826178044884420975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898771884118696589613983 4348157826178044884420975)
        ·
          refine ⟨6522236739267067326631463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348157826178044884420975 6522236739267067326631463)
          ·
            refine ⟨9783355108900600989947195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522236739267067326631463 9783355108900600989947195)
            ·
              refine ⟨14675032663350901484920793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9783355108900600989947195 14675032663350901484920793)
              ·
                refine ⟨11006274497513176113690595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14675032663350901484920793 11006274497513176113690595)
                ·
                  refine ⟨16509411746269764170535893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006274497513176113690595 16509411746269764170535893)
                  ·
                    refine ⟨386939337803197597746935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16509411746269764170535893 386939337803197597746935)
                    ·
                      rfl

theorem cell23_2260685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2260685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260685 prefixEnd_2260685 := by exact prefixLift 2260685
  have htrace : WordTrace (prefixWord ++ tailWord_2260685) baseStart_2260685 baseEnd_2260685 := by
    simpa [prefixWord, tailWord_2260685, baseEnd_2260685] using wordTrace_append hprefix tailTrace_2260685
  have hstable : (prefixWord ++ tailWord_2260685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260685).length < 2 ^ (prefixWord ++ tailWord_2260685).sum := by decide
  have hdescent : baseEnd_2260685 < baseStart_2260685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260688 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2]
def baseStart_2260688 : Nat := 118140960795 + 2260688 * 2 ^ 59
def prefixEnd_2260688 : Nat := 4983230072969 + 3 ^ 40 * 2260688 * 2
def baseEnd_2260688 : Nat := 1160819553851556281503291

theorem tailTrace_2260688 : CollatzResearch.WordTrace tailWord_2260688 prefixEnd_2260688 1160819553851556281503291 := by
  unfold tailWord_2260688
  simp only [CollatzResearch.WordTrace]
  refine ⟨41227032616960472808467359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54969376822613963744623145 41227032616960472808467359)
  ·
    refine ⟨61840548925440709212701039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41227032616960472808467359 61840548925440709212701039)
    ·
      refine ⟨92760823388161063819051559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61840548925440709212701039 92760823388161063819051559)
      ·
        refine ⟨139141235082241595728577339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92760823388161063819051559 139141235082241595728577339)
        ·
          refine ⟨208711852623362393592866009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139141235082241595728577339 208711852623362393592866009)
          ·
            refine ⟨156533889467521795194649507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208711852623362393592866009 156533889467521795194649507)
            ·
              refine ⟨234800834201282692791974261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156533889467521795194649507 234800834201282692791974261)
              ·
                refine ⟨22012578206370252449247587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234800834201282692791974261 22012578206370252449247587)
                ·
                  refine ⟨33018867309555378673871381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22012578206370252449247587 33018867309555378673871381)
                  ·
                    refine ⟨1547759405135408375337721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33018867309555378673871381 1547759405135408375337721)
                    ·
                      refine ⟨1160819553851556281503291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547759405135408375337721 1160819553851556281503291)
                      ·
                        rfl

theorem cell23_2260688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2].length) (baseStart_2260688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260688 prefixEnd_2260688 := by exact prefixLift 2260688
  have htrace : WordTrace (prefixWord ++ tailWord_2260688) baseStart_2260688 baseEnd_2260688 := by
    simpa [prefixWord, tailWord_2260688, baseEnd_2260688] using wordTrace_append hprefix tailTrace_2260688
  have hstable : (prefixWord ++ tailWord_2260688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260688).length < 2 ^ (prefixWord ++ tailWord_2260688).sum := by decide
  have hdescent : baseEnd_2260688 < baseStart_2260688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260708 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_2260708 : Nat := 118140960795 + 2260708 * 2 ^ 59
def prefixEnd_2260708 : Nat := 4983230072969 + 3 ^ 40 * 2260708 * 2
def baseEnd_2260708 : Nat := 1160829823464646203253199

theorem tailTrace_2260708 : CollatzResearch.WordTrace tailWord_2260708 prefixEnd_2260708 1160829823464646203253199 := by
  unfold tailWord_2260708
  simp only [CollatzResearch.WordTrace]
  refine ⟨41227397346924244516331389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54969863129232326021775185 41227397346924244516331389)
  ·
    refine ⟨15460274005096591693624271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41227397346924244516331389 15460274005096591693624271)
    ·
      refine ⟨23190411007644887540436407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15460274005096591693624271 23190411007644887540436407)
      ·
        refine ⟨34785616511467331310654611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23190411007644887540436407 34785616511467331310654611)
        ·
          refine ⟨52178424767200996965981917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34785616511467331310654611 52178424767200996965981917)
          ·
            refine ⟨19566909287700373862243219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52178424767200996965981917 19566909287700373862243219)
            ·
              refine ⟨29350363931550560793364829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19566909287700373862243219 29350363931550560793364829)
              ·
                refine ⟨11006386474331460297511811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29350363931550560793364829 11006386474331460297511811)
                ·
                  refine ⟨16509579711497190446267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11006386474331460297511811 16509579711497190446267717)
                  ·
                    refine ⟨3095546195905723208675197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16509579711497190446267717 3095546195905723208675197)
                    ·
                      refine ⟨1160829823464646203253199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095546195905723208675197 1160829823464646203253199)
                      ·
                        rfl

theorem cell23_2260708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_2260708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260708 prefixEnd_2260708 := by exact prefixLift 2260708
  have htrace : WordTrace (prefixWord ++ tailWord_2260708) baseStart_2260708 baseEnd_2260708 := by
    simpa [prefixWord, tailWord_2260708, baseEnd_2260708] using wordTrace_append hprefix tailTrace_2260708
  have hstable : (prefixWord ++ tailWord_2260708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260708).length < 2 ^ (prefixWord ++ tailWord_2260708).sum := by decide
  have hdescent : baseEnd_2260708 < baseStart_2260708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260731 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_2260731 : Nat := 118140960795 + 2260731 * 2 ^ 59
def prefixEnd_2260731 : Nat := 4983230072969 + 3 ^ 40 * 2260731 * 2
def baseEnd_2260731 : Nat := 1160841633519699613265593

theorem tailTrace_2260731 : CollatzResearch.WordTrace tailWord_2260731 prefixEnd_2260731 1160841633519699613265593 := by
  unfold tailWord_2260731
  simp only [CollatzResearch.WordTrace]
  refine ⟨82455633572765163960750047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54970422381843442640500031 82455633572765163960750047)
  ·
    refine ⟨123683450359147745941125071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82455633572765163960750047 123683450359147745941125071)
    ·
      refine ⟨185525175538721618911687607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123683450359147745941125071 185525175538721618911687607)
      ·
        refine ⟨278287763308082428367531411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185525175538721618911687607 278287763308082428367531411)
        ·
          refine ⟨417431644962123642551297117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278287763308082428367531411 417431644962123642551297117)
          ·
            refine ⟨156536866860796365956736419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417431644962123642551297117 156536866860796365956736419)
            ·
              refine ⟨234805300291194548935104629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156536866860796365956736419 234805300291194548935104629)
              ·
                refine ⟨22012996902299488962666059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234805300291194548935104629 22012996902299488962666059)
                ·
                  refine ⟨33019495353449233443999089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22012996902299488962666059 33019495353449233443999089)
                  ·
                    refine ⟨24764621515086925082999317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33019495353449233443999089 24764621515086925082999317)
                    ·
                      refine ⟨1160841633519699613265593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24764621515086925082999317 1160841633519699613265593)
                      ·
                        rfl

theorem cell23_2260731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_2260731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260731 prefixEnd_2260731 := by exact prefixLift 2260731
  have htrace : WordTrace (prefixWord ++ tailWord_2260731) baseStart_2260731 baseEnd_2260731 := by
    simpa [prefixWord, tailWord_2260731, baseEnd_2260731] using wordTrace_append hprefix tailTrace_2260731
  have hstable : (prefixWord ++ tailWord_2260731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260731).length < 2 ^ (prefixWord ++ tailWord_2260731).sum := by decide
  have hdescent : baseEnd_2260731 < baseStart_2260731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260741 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2260741 : Nat := 118140960795 + 2260741 * 2 ^ 59
def prefixEnd_2260741 : Nat := 4983230072969 + 3 ^ 40 * 2260741 * 2
def baseEnd_2260741 : Nat := 386948922775414858046849

theorem tailTrace_2260741 : CollatzResearch.WordTrace tailWord_2260741 prefixEnd_2260741 386948922775414858046849 := by
  unfold tailWord_2260741
  simp only [CollatzResearch.WordTrace]
  refine ⟨82455998302728935668614077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54970665535152623779076051 82455998302728935668614077)
  ·
    refine ⟨30920999363523350875730279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82455998302728935668614077 30920999363523350875730279)
    ·
      refine ⟨46381499045285026313595419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30920999363523350875730279 46381499045285026313595419)
      ·
        refine ⟨69572248567927539470393129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46381499045285026313595419 69572248567927539470393129)
        ·
          refine ⟨52179186425945654602794847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69572248567927539470393129 52179186425945654602794847)
          ·
            refine ⟨78268779638918481904192271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52179186425945654602794847 78268779638918481904192271)
            ·
              refine ⟨117403169458377722856288407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78268779638918481904192271 117403169458377722856288407)
              ·
                refine ⟨176104754187566584284432611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117403169458377722856288407 176104754187566584284432611)
                ·
                  refine ⟨264157131281349876426648917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176104754187566584284432611 264157131281349876426648917)
                  ·
                    refine ⟨386948922775414858046849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 264157131281349876426648917 386948922775414858046849)
                    ·
                      rfl

theorem cell23_2260741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2260741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260741 prefixEnd_2260741 := by exact prefixLift 2260741
  have htrace : WordTrace (prefixWord ++ tailWord_2260741) baseStart_2260741 baseEnd_2260741 := by
    simpa [prefixWord, tailWord_2260741, baseEnd_2260741] using wordTrace_append hprefix tailTrace_2260741
  have hstable : (prefixWord ++ tailWord_2260741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260741).length < 2 ^ (prefixWord ++ tailWord_2260741).sum := by decide
  have hdescent : baseEnd_2260741 < baseStart_2260741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260751 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_2260751 : Nat := 118140960795 + 2260751 * 2 ^ 59
def prefixEnd_2260751 : Nat := 4983230072969 + 3 ^ 40 * 2260751 * 2
def baseEnd_2260751 : Nat := 1160851903132789535015501

theorem tailTrace_2260751 : CollatzResearch.WordTrace tailWord_2260751 prefixEnd_2260751 1160851903132789535015501 := by
  unfold tailWord_2260751
  simp only [CollatzResearch.WordTrace]
  refine ⟨82456363032692707376478107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54970908688461804917652071 82456363032692707376478107)
  ·
    refine ⟨123684544549039061064717161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82456363032692707376478107 123684544549039061064717161)
    ·
      refine ⟨92763408411779295798537871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123684544549039061064717161 92763408411779295798537871)
      ·
        refine ⟨139145112617668943697806807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92763408411779295798537871 139145112617668943697806807)
        ·
          refine ⟨208717668926503415546710211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139145112617668943697806807 208717668926503415546710211)
          ·
            refine ⟨313076503389755123320065317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208717668926503415546710211 313076503389755123320065317)
            ·
              refine ⟨58701844385579085622512247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313076503389755123320065317 58701844385579085622512247)
              ·
                refine ⟨88052766578368628433768371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58701844385579085622512247 88052766578368628433768371)
                ·
                  refine ⟨132079149867552942650652557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88052766578368628433768371 132079149867552942650652557)
                  ·
                    refine ⟨49529681200332353493994709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132079149867552942650652557 49529681200332353493994709)
                    ·
                      refine ⟨1160851903132789535015501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49529681200332353493994709 1160851903132789535015501)
                      ·
                        rfl

theorem cell23_2260751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_2260751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260751 prefixEnd_2260751 := by exact prefixLift 2260751
  have htrace : WordTrace (prefixWord ++ tailWord_2260751) baseStart_2260751 baseEnd_2260751 := by
    simpa [prefixWord, tailWord_2260751, baseEnd_2260751] using wordTrace_append hprefix tailTrace_2260751
  have hstable : (prefixWord ++ tailWord_2260751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260751).length < 2 ^ (prefixWord ++ tailWord_2260751).sum := by decide
  have hdescent : baseEnd_2260751 < baseStart_2260751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260756 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2260756 : Nat := 118140960795 + 2260756 * 2 ^ 59
def prefixEnd_2260756 : Nat := 4983230072969 + 3 ^ 40 * 2260756 * 2
def baseEnd_2260756 : Nat := 1160854470536062015452979

theorem tailTrace_2260756 : CollatzResearch.WordTrace tailWord_2260756 prefixEnd_2260756 1160854470536062015452979 := by
  unfold tailWord_2260756
  simp only [CollatzResearch.WordTrace]
  refine ⟨41228272698837296615205061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54971030265116395486940081 41228272698837296615205061)
  ·
    refine ⟨7730301131031993115350949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41228272698837296615205061 7730301131031993115350949)
    ·
      refine ⟨1449431462068498709128303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7730301131031993115350949 1449431462068498709128303)
      ·
        refine ⟨2174147193102748063692455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449431462068498709128303 2174147193102748063692455)
        ·
          refine ⟨3261220789654122095538683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174147193102748063692455 3261220789654122095538683)
          ·
            refine ⟨4891831184481183143308025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261220789654122095538683 4891831184481183143308025)
            ·
              refine ⟨3668873388360887357481019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4891831184481183143308025 3668873388360887357481019)
              ·
                refine ⟨5503310082541331036221529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668873388360887357481019 5503310082541331036221529)
                ·
                  refine ⟨4127482561905998277166147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503310082541331036221529 4127482561905998277166147)
                  ·
                    refine ⟨6191223842858997415749221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4127482561905998277166147 6191223842858997415749221)
                    ·
                      refine ⟨1160854470536062015452979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6191223842858997415749221 1160854470536062015452979)
                      ·
                        rfl

theorem cell23_2260756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2260756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260756 prefixEnd_2260756 := by exact prefixLift 2260756
  have htrace : WordTrace (prefixWord ++ tailWord_2260756) baseStart_2260756 baseEnd_2260756 := by
    simpa [prefixWord, tailWord_2260756, baseEnd_2260756] using wordTrace_append hprefix tailTrace_2260756
  have hstable : (prefixWord ++ tailWord_2260756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260756).length < 2 ^ (prefixWord ++ tailWord_2260756).sum := by decide
  have hdescent : baseEnd_2260756 < baseStart_2260756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260805 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2260805 : Nat := 118140960795 + 2260805 * 2 ^ 59
def prefixEnd_2260805 : Nat := 4983230072969 + 3 ^ 40 * 2260805 * 2
def baseEnd_2260805 : Nat := 386959877029377441246751

theorem tailTrace_2260805 : CollatzResearch.WordTrace tailWord_2260805 prefixEnd_2260805 386959877029377441246751 := by
  unfold tailWord_2260805
  simp only [CollatzResearch.WordTrace]
  refine ⟨82458332574497074598943869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54972221716331383065962579 82458332574497074598943869)
  ·
    refine ⟨30921874715436402974603951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82458332574497074598943869 30921874715436402974603951)
    ·
      refine ⟨46382812073154604461905927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30921874715436402974603951 46382812073154604461905927)
      ·
        refine ⟨69574218109731906692858891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46382812073154604461905927 69574218109731906692858891)
        ·
          refine ⟨104361327164597860039288337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69574218109731906692858891 104361327164597860039288337)
          ·
            refine ⟨78270995373448395029466253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104361327164597860039288337 78270995373448395029466253)
            ·
              refine ⟨29351623265043148136049845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78270995373448395029466253 29351623265043148136049845)
              ·
                refine ⟨2751714681097795137754673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29351623265043148136049845 2751714681097795137754673)
                ·
                  refine ⟨2063786010823346353316005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751714681097795137754673 2063786010823346353316005)
                  ·
                    refine ⟨386959877029377441246751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2063786010823346353316005 386959877029377441246751)
                    ·
                      rfl

theorem cell23_2260805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2260805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260805 prefixEnd_2260805 := by exact prefixLift 2260805
  have htrace : WordTrace (prefixWord ++ tailWord_2260805) baseStart_2260805 baseEnd_2260805 := by
    simpa [prefixWord, tailWord_2260805, baseEnd_2260805] using wordTrace_append hprefix tailTrace_2260805
  have hstable : (prefixWord ++ tailWord_2260805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260805).length < 2 ^ (prefixWord ++ tailWord_2260805).sum := by decide
  have hdescent : baseEnd_2260805 < baseStart_2260805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260806 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2260806 : Nat := 118140960795 + 2260806 * 2 ^ 59
def prefixEnd_2260806 : Nat := 4983230072969 + 3 ^ 40 * 2260806 * 2
def baseEnd_2260806 : Nat := 1160880144568786819827749

theorem tailTrace_2260806 : CollatzResearch.WordTrace tailWord_2260806 prefixEnd_2260806 1160880144568786819827749 := by
  unfold tailWord_2260806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576824032734170367804071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54972246031662301179820181 2576824032734170367804071)
  ·
    refine ⟨3865236049101255551706107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2576824032734170367804071 3865236049101255551706107)
    ·
      refine ⟨5797854073651883327559161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865236049101255551706107 5797854073651883327559161)
      ·
        refine ⟨4348390555238912495669371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5797854073651883327559161 4348390555238912495669371)
        ·
          refine ⟨6522585832858368743504057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348390555238912495669371 6522585832858368743504057)
          ·
            refine ⟨4891939374643776557628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6522585832858368743504057 4891939374643776557628043)
            ·
              refine ⟨7337909061965664836442065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891939374643776557628043 7337909061965664836442065)
              ·
                refine ⟨5503431796474248627331549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7337909061965664836442065 5503431796474248627331549)
                ·
                  refine ⟨2063786923677843235249331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5503431796474248627331549 2063786923677843235249331)
                  ·
                    refine ⟨3095680385516764852873997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2063786923677843235249331 3095680385516764852873997)
                    ·
                      refine ⟨1160880144568786819827749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095680385516764852873997 1160880144568786819827749)
                      ·
                        rfl

theorem cell23_2260806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2260806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260806 prefixEnd_2260806 := by exact prefixLift 2260806
  have htrace : WordTrace (prefixWord ++ tailWord_2260806) baseStart_2260806 baseEnd_2260806 := by
    simpa [prefixWord, tailWord_2260806, baseEnd_2260806] using wordTrace_append hprefix tailTrace_2260806
  have hstable : (prefixWord ++ tailWord_2260806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260806).length < 2 ^ (prefixWord ++ tailWord_2260806).sum := by decide
  have hdescent : baseEnd_2260806 < baseStart_2260806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260832 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2260832 : Nat := 118140960795 + 2260832 * 2 ^ 59
def prefixEnd_2260832 : Nat := 4983230072969 + 3 ^ 40 * 2260832 * 2
def baseEnd_2260832 : Nat := 1160893495065803718102629

theorem tailTrace_2260832 : CollatzResearch.WordTrace tailWord_2260832 prefixEnd_2260832 1160893495065803718102629 := by
  unfold tailWord_2260832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41229658672699629105088375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54972878230266172140117833 41229658672699629105088375)
  ·
    refine ⟨61844488009049443657632563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41229658672699629105088375 61844488009049443657632563)
    ·
      refine ⟨92766732013574165486448845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61844488009049443657632563 92766732013574165486448845)
      ·
        refine ⟨34787524505090312057418317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92766732013574165486448845 34787524505090312057418317)
        ·
          refine ⟨13045321689408867021531869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34787524505090312057418317 13045321689408867021531869)
          ·
            refine ⟨4891995633528325133074451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13045321689408867021531869 4891995633528325133074451)
            ·
              refine ⟨7337993450292487699611677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891995633528325133074451 7337993450292487699611677)
              ·
                refine ⟨2751747543859682887354379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7337993450292487699611677 2751747543859682887354379)
                ·
                  refine ⟨4127621315789524331031569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751747543859682887354379 4127621315789524331031569)
                  ·
                    refine ⟨3095715986842143248273677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4127621315789524331031569 3095715986842143248273677)
                    ·
                      refine ⟨1160893495065803718102629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095715986842143248273677 1160893495065803718102629)
                      ·
                        rfl

theorem cell23_2260832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2260832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260832 prefixEnd_2260832 := by exact prefixLift 2260832
  have htrace : WordTrace (prefixWord ++ tailWord_2260832) baseStart_2260832 baseEnd_2260832 := by
    simpa [prefixWord, tailWord_2260832, baseEnd_2260832] using wordTrace_append hprefix tailTrace_2260832
  have hstable : (prefixWord ++ tailWord_2260832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260832).length < 2 ^ (prefixWord ++ tailWord_2260832).sum := by decide
  have hdescent : baseEnd_2260832 < baseStart_2260832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260845 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2260845 : Nat := 118140960795 + 2260845 * 2 ^ 59
def prefixEnd_2260845 : Nat := 4983230072969 + 3 ^ 40 * 2260845 * 2
def baseEnd_2260845 : Nat := 1160900170314312167240069

theorem tailTrace_2260845 : CollatzResearch.WordTrace tailWord_2260845 prefixEnd_2260845 1160900170314312167240069 := by
  unfold tailWord_2260845
  simp only [CollatzResearch.WordTrace]
  refine ⟨82459791494352161430399989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54973194329568107620266659 82459791494352161430399989)
  ·
    refine ⟨7730605452595515134099999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82459791494352161430399989 7730605452595515134099999)
    ·
      refine ⟨11595908178893272701149999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7730605452595515134099999 11595908178893272701149999)
      ·
        refine ⟨17393862268339909051724999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11595908178893272701149999 17393862268339909051724999)
        ·
          refine ⟨26090793402509863577587499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17393862268339909051724999 26090793402509863577587499)
          ·
            refine ⟨39136190103764795366381249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26090793402509863577587499 39136190103764795366381249)
            ·
              refine ⟨29352142577823596524785937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39136190103764795366381249 29352142577823596524785937)
              ·
                refine ⟨22014106933367697393589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29352142577823596524785937 22014106933367697393589453)
                ·
                  refine ⟨8255290100012886522596045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22014106933367697393589453 8255290100012886522596045)
                  ·
                    refine ⟨3095733787504832445973517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8255290100012886522596045 3095733787504832445973517)
                    ·
                      refine ⟨1160900170314312167240069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095733787504832445973517 1160900170314312167240069)
                      ·
                        rfl

theorem cell23_2260845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2260845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260845 prefixEnd_2260845 := by exact prefixLift 2260845
  have htrace : WordTrace (prefixWord ++ tailWord_2260845) baseStart_2260845 baseEnd_2260845 := by
    simpa [prefixWord, tailWord_2260845, baseEnd_2260845] using wordTrace_append hprefix tailTrace_2260845
  have hstable : (prefixWord ++ tailWord_2260845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260845).length < 2 ^ (prefixWord ++ tailWord_2260845).sum := by decide
  have hdescent : baseEnd_2260845 < baseStart_2260845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260846 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2260846 : Nat := 118140960795 + 2260846 * 2 ^ 59
def prefixEnd_2260846 : Nat := 4983230072969 + 3 ^ 40 * 2260846 * 2
def baseEnd_2260846 : Nat := 1160900683794966663327565

theorem tailTrace_2260846 : CollatzResearch.WordTrace tailWord_2260846 prefixEnd_2260846 1160900683794966663327565 := by
  unfold tailWord_2260846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307478495918567325148299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54973218644899025734124261 10307478495918567325148299)
  ·
    refine ⟨15461217743877850987722449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10307478495918567325148299 15461217743877850987722449)
    ·
      refine ⟨11595913307908388240791837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15461217743877850987722449 11595913307908388240791837)
      ·
        refine ⟨4348467490465645590296939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11595913307908388240791837 4348467490465645590296939)
        ·
          refine ⟨6522701235698468385445409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348467490465645590296939 6522701235698468385445409)
          ·
            refine ⟨4892025926773851289084057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6522701235698468385445409 4892025926773851289084057)
            ·
              refine ⟨3669019445080388466813043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892025926773851289084057 3669019445080388466813043)
              ·
                refine ⟨5503529167620582700219565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669019445080388466813043 5503529167620582700219565)
                ·
                  refine ⟨2063823437857718512582337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5503529167620582700219565 2063823437857718512582337)
                  ·
                    refine ⟨1547867578393288884436753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2063823437857718512582337 1547867578393288884436753)
                    ·
                      refine ⟨1160900683794966663327565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1547867578393288884436753 1160900683794966663327565)
                      ·
                        rfl

theorem cell23_2260846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2260846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260846 prefixEnd_2260846 := by exact prefixLift 2260846
  have htrace : WordTrace (prefixWord ++ tailWord_2260846) baseStart_2260846 baseEnd_2260846 := by
    simpa [prefixWord, tailWord_2260846, baseEnd_2260846] using wordTrace_append hprefix tailTrace_2260846
  have hstable : (prefixWord ++ tailWord_2260846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260846).length < 2 ^ (prefixWord ++ tailWord_2260846).sum := by decide
  have hdescent : baseEnd_2260846 < baseStart_2260846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260886 : List Nat := [5, 3, 1, 1, 3, 1, 9]
def baseStart_2260886 : Nat := 118140960795 + 2260886 * 2 ^ 59
def prefixEnd_2260886 : Nat := 4983230072969 + 3 ^ 40 * 2260886 * 2
def baseEnd_2260886 : Nat := 14332360778038845763301

theorem tailTrace_2260886 : CollatzResearch.WordTrace tailWord_2260886 prefixEnd_2260886 14332360778038845763301 := by
  unfold tailWord_2260886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153830430450226589540157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54974191258135750288428341 5153830430450226589540157)
  ·
    refine ⟨1932686411418834971077559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5153830430450226589540157 1932686411418834971077559)
    ·
      refine ⟨2899029617128252456616339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932686411418834971077559 2899029617128252456616339)
      ·
        refine ⟨4348544425692378684924509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899029617128252456616339 4348544425692378684924509)
        ·
          refine ⟨1630704159634642006846691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4348544425692378684924509 1630704159634642006846691)
          ·
            refine ⟨2446056239451963010270037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630704159634642006846691 2446056239451963010270037)
            ·
              refine ⟨14332360778038845763301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2446056239451963010270037 14332360778038845763301)
              ·
                rfl

theorem cell23_2260886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 9].length) (baseStart_2260886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260886 prefixEnd_2260886 := by exact prefixLift 2260886
  have htrace : WordTrace (prefixWord ++ tailWord_2260886) baseStart_2260886 baseEnd_2260886 := by
    simpa [prefixWord, tailWord_2260886, baseEnd_2260886] using wordTrace_append hprefix tailTrace_2260886
  have hstable : (prefixWord ++ tailWord_2260886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260886).length < 2 ^ (prefixWord ++ tailWord_2260886).sum := by decide
  have hdescent : baseEnd_2260886 < baseStart_2260886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260935 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_2260935 : Nat := 118140960795 + 2260935 * 2 ^ 59
def prefixEnd_2260935 : Nat := 4983230072969 + 3 ^ 40 * 2260935 * 2
def baseEnd_2260935 : Nat := 1160946383573216815114655

theorem tailTrace_2260935 : CollatzResearch.WordTrace tailWord_2260935 prefixEnd_2260935 1160946383573216815114655 := by
  unfold tailWord_2260935
  simp only [CollatzResearch.WordTrace]
  refine ⟨82463074064026106801176259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54975382709350737867450839 82463074064026106801176259)
  ·
    refine ⟨123694611096039160201764389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82463074064026106801176259 123694611096039160201764389)
    ·
      refine ⟨23192739580507342537830823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123694611096039160201764389 23192739580507342537830823)
      ·
        refine ⟨34789109370761013806746235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23192739580507342537830823 34789109370761013806746235)
        ·
          refine ⟨52183664056141520710119353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34789109370761013806746235 52183664056141520710119353)
          ·
            refine ⟨39137748042106140532589515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52183664056141520710119353 39137748042106140532589515)
            ·
              refine ⟨58706622063159210798884273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39137748042106140532589515 58706622063159210798884273)
              ·
                refine ⟨44029966547369408099163205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58706622063159210798884273 44029966547369408099163205)
                ·
                  refine ⟨8255618727631764018593101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44029966547369408099163205 8255618727631764018593101)
                  ·
                    refine ⟨3095857022861911506972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8255618727631764018593101 3095857022861911506972413)
                    ·
                      refine ⟨1160946383573216815114655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3095857022861911506972413 1160946383573216815114655)
                      ·
                        rfl

theorem cell23_2260935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_2260935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260935 prefixEnd_2260935 := by exact prefixLift 2260935
  have htrace : WordTrace (prefixWord ++ tailWord_2260935) baseStart_2260935 baseEnd_2260935 := by
    simpa [prefixWord, tailWord_2260935, baseEnd_2260935] using wordTrace_append hprefix tailTrace_2260935
  have hstable : (prefixWord ++ tailWord_2260935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260935).length < 2 ^ (prefixWord ++ tailWord_2260935).sum := by decide
  have hdescent : baseEnd_2260935 < baseStart_2260935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260942 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_2260942 : Nat := 118140960795 + 2260942 * 2 ^ 59
def prefixEnd_2260942 : Nat := 4983230072969 + 3 ^ 40 * 2260942 * 2
def baseEnd_2260942 : Nat := 128994441993088698636347

theorem tailTrace_2260942 : CollatzResearch.WordTrace tailWord_2260942 prefixEnd_2260942 128994441993088698636347 := by
  unfold tailWord_2260942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307916171875093374585135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54975552916667164664454053 10307916171875093374585135)
  ·
    refine ⟨15461874257812640061877703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10307916171875093374585135 15461874257812640061877703)
    ·
      refine ⟨23192811386718960092816555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15461874257812640061877703 23192811386718960092816555)
      ·
        refine ⟨34789217080078440139224833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23192811386718960092816555 34789217080078440139224833)
        ·
          refine ⟨26091912810058830104418625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34789217080078440139224833 26091912810058830104418625)
          ·
            refine ⟨19568934607544122578313969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26091912810058830104418625 19568934607544122578313969)
            ·
              refine ⟨14676700955658091933735477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19568934607544122578313969 14676700955658091933735477)
              ·
                refine ⟨1375940714592946118787701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14676700955658091933735477 1375940714592946118787701)
                ·
                  refine ⟨128994441993088698636347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1375940714592946118787701 128994441993088698636347)
                  ·
                    rfl

theorem cell23_2260942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_2260942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260942 prefixEnd_2260942 := by exact prefixLift 2260942
  have htrace : WordTrace (prefixWord ++ tailWord_2260942) baseStart_2260942 baseEnd_2260942 := by
    simpa [prefixWord, tailWord_2260942, baseEnd_2260942] using wordTrace_append hprefix tailTrace_2260942
  have hstable : (prefixWord ++ tailWord_2260942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260942).length < 2 ^ (prefixWord ++ tailWord_2260942).sum := by decide
  have hdescent : baseEnd_2260942 < baseStart_2260942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260959 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 5]
def baseStart_2260959 : Nat := 118140960795 + 2260959 * 2 ^ 59
def prefixEnd_2260959 : Nat := 4983230072969 + 3 ^ 40 * 2260959 * 2
def baseEnd_2260959 : Nat := 128995411900991635690505

theorem tailTrace_2260959 : CollatzResearch.WordTrace tailWord_2260959 prefixEnd_2260959 128995411900991635690505 := by
  unfold tailWord_2260959
  simp only [CollatzResearch.WordTrace]
  refine ⟨82463949415939158900049931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54975966277292772600033287 82463949415939158900049931)
  ·
    refine ⟨123695924123908738350074897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82463949415939158900049931 123695924123908738350074897)
    ·
      refine ⟨92771943092931553762556173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123695924123908738350074897 92771943092931553762556173)
      ·
        refine ⟨34789478659849332660958565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92771943092931553762556173 34789478659849332660958565)
        ·
          refine ⟨6523027248721749873929731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34789478659849332660958565 6523027248721749873929731)
          ·
            refine ⟨9784540873082624810894597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523027248721749873929731 9784540873082624810894597)
            ·
              refine ⟨1834601413702992152042737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9784540873082624810894597 1834601413702992152042737)
              ·
                refine ⟨1375951060277244114032053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834601413702992152042737 1375951060277244114032053)
                ·
                  refine ⟨128995411900991635690505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1375951060277244114032053 128995411900991635690505)
                  ·
                    rfl

theorem cell23_2260959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 5].length) (baseStart_2260959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260959 prefixEnd_2260959 := by exact prefixLift 2260959
  have htrace : WordTrace (prefixWord ++ tailWord_2260959) baseStart_2260959 baseEnd_2260959 := by
    simpa [prefixWord, tailWord_2260959, baseEnd_2260959] using wordTrace_append hprefix tailTrace_2260959
  have hstable : (prefixWord ++ tailWord_2260959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260959).length < 2 ^ (prefixWord ++ tailWord_2260959).sum := by decide
  have hdescent : baseEnd_2260959 < baseStart_2260959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260975 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_2260975 : Nat := 118140960795 + 2260975 * 2 ^ 59
def prefixEnd_2260975 : Nat := 4983230072969 + 3 ^ 40 * 2260975 * 2
def baseEnd_2260975 : Nat := 1160966922799396658614471

theorem tailTrace_2260975 : CollatzResearch.WordTrace tailWord_2260975 prefixEnd_2260975 1160966922799396658614471 := by
  unfold tailWord_2260975
  simp only [CollatzResearch.WordTrace]
  refine ⟨82464532983881193632632379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54976355322587462421754919 82464532983881193632632379)
  ·
    refine ⟨123696799475821790448948569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82464532983881193632632379 123696799475821790448948569)
    ·
      refine ⟨92772599606866342836711427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123696799475821790448948569 92772599606866342836711427)
      ·
        refine ⟨139158899410299514255067141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92772599606866342836711427 139158899410299514255067141)
        ·
          refine ⟨26092293639431158922825089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139158899410299514255067141 26092293639431158922825089)
          ·
            refine ⟨19569220229573369192118817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26092293639431158922825089 19569220229573369192118817)
            ·
              refine ⟨14676915172180026894089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19569220229573369192118817 14676915172180026894089113)
              ·
                refine ⟨11007686379135020170566835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14676915172180026894089113 11007686379135020170566835)
                ·
                  refine ⟨16511529568702530255850253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11007686379135020170566835 16511529568702530255850253)
                  ·
                    refine ⟨6191823588263448845943845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16511529568702530255850253 6191823588263448845943845)
                    ·
                      refine ⟨1160966922799396658614471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6191823588263448845943845 1160966922799396658614471)
                      ·
                        rfl

theorem cell23_2260975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_2260975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2260975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2260975 prefixEnd_2260975 := by exact prefixLift 2260975
  have htrace : WordTrace (prefixWord ++ tailWord_2260975) baseStart_2260975 baseEnd_2260975 := by
    simpa [prefixWord, tailWord_2260975, baseEnd_2260975] using wordTrace_append hprefix tailTrace_2260975
  have hstable : (prefixWord ++ tailWord_2260975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260975).length < 2 ^ (prefixWord ++ tailWord_2260975).sum := by decide
  have hdescent : baseEnd_2260975 < baseStart_2260975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261082 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2261082 : Nat := 118140960795 + 2261082 * 2 ^ 59
def prefixEnd_2261082 : Nat := 4983230072969 + 3 ^ 40 * 2261082 * 2
def baseEnd_2261082 : Nat := 1161021865229427739976479

theorem tailTrace_2261082 : CollatzResearch.WordTrace tailWord_2261082 prefixEnd_2261082 1161021865229427739976479 := by
  unfold tailWord_2261082
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617108898623387726694375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54978957062995700604518333 20617108898623387726694375)
  ·
    refine ⟨30925663347935081590041563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20617108898623387726694375 30925663347935081590041563)
    ·
      refine ⟨46388495021902622385062345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30925663347935081590041563 46388495021902622385062345)
      ·
        refine ⟨34791371266426966788796759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46388495021902622385062345 34791371266426966788796759)
        ·
          refine ⟨52187056899640450183195139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34791371266426966788796759 52187056899640450183195139)
          ·
            refine ⟨78280585349460675274792709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52187056899640450183195139 78280585349460675274792709)
            ·
              refine ⟨14677609753023876614023633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78280585349460675274792709 14677609753023876614023633)
              ·
                refine ⟨11008207314767907460517725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14677609753023876614023633 11008207314767907460517725)
                ·
                  refine ⟨4128077743037965297694147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11008207314767907460517725 4128077743037965297694147)
                  ·
                    refine ⟨6192116614556947946541221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128077743037965297694147 6192116614556947946541221)
                    ·
                      refine ⟨1161021865229427739976479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6192116614556947946541221 1161021865229427739976479)
                      ·
                        rfl

theorem cell23_2261082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2261082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261082 prefixEnd_2261082 := by exact prefixLift 2261082
  have htrace : WordTrace (prefixWord ++ tailWord_2261082) baseStart_2261082 baseEnd_2261082 := by
    simpa [prefixWord, tailWord_2261082, baseEnd_2261082] using wordTrace_append hprefix tailTrace_2261082
  have hstable : (prefixWord ++ tailWord_2261082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261082).length < 2 ^ (prefixWord ++ tailWord_2261082).sum := by decide
  have hdescent : baseEnd_2261082 < baseStart_2261082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261105 : List Nat := [1, 2, 2, 2, 1, 1, 3, 11]
def baseStart_2261105 : Nat := 118140960795 + 2261105 * 2 ^ 59
def prefixEnd_2261105 : Nat := 4983230072969 + 3 ^ 40 * 2261105 * 2
def baseEnd_2261105 : Nat := 43001247232758561110699

theorem tailTrace_2261105 : CollatzResearch.WordTrace tailWord_2261105 prefixEnd_2261105 43001247232758561110699 := by
  unfold tailWord_2261105
  simp only [CollatzResearch.WordTrace]
  refine ⟨82469274473410225834864769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54979516315606817223243179 82469274473410225834864769)
  ·
    refine ⟨61851955855057669376148577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82469274473410225834864769 61851955855057669376148577)
    ·
      refine ⟨46388966891293252032111433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61851955855057669376148577 46388966891293252032111433)
      ·
        refine ⟨34791725168469939024083575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46388966891293252032111433 34791725168469939024083575)
        ·
          refine ⟨52187587752704908536125363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34791725168469939024083575 52187587752704908536125363)
          ·
            refine ⟨78281381629057362804188045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52187587752704908536125363 78281381629057362804188045)
            ·
              refine ⟨29355518110896511051570517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78281381629057362804188045 29355518110896511051570517)
              ·
                refine ⟨43001247232758561110699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29355518110896511051570517 43001247232758561110699)
                ·
                  rfl

theorem cell23_2261105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 11].length) (baseStart_2261105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261105 prefixEnd_2261105 := by exact prefixLift 2261105
  have htrace : WordTrace (prefixWord ++ tailWord_2261105) baseStart_2261105 baseEnd_2261105 := by
    simpa [prefixWord, tailWord_2261105, baseEnd_2261105] using wordTrace_append hprefix tailTrace_2261105
  have hstable : (prefixWord ++ tailWord_2261105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261105).length < 2 ^ (prefixWord ++ tailWord_2261105).sum := by decide
  have hdescent : baseEnd_2261105 < baseStart_2261105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261116 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_2261116 : Nat := 118140960795 + 2261116 * 2 ^ 59
def prefixEnd_2261116 : Nat := 4983230072969 + 3 ^ 40 * 2261116 * 2
def baseEnd_2261116 : Nat := 1161039323571680606951323

theorem tailTrace_2261116 : CollatzResearch.WordTrace tailWord_2261116 prefixEnd_2261116 1161039323571680606951323 := by
  unfold tailWord_2261116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41234837838185187356757601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54979783784246916475676801 41234837838185187356757601)
  ·
    refine ⟨30926128378638890517568201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41234837838185187356757601 30926128378638890517568201)
    ·
      refine ⟨23194596283979167888176151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30926128378638890517568201 23194596283979167888176151)
      ·
        refine ⟨34791894425968751832264227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23194596283979167888176151 34791894425968751832264227)
        ·
          refine ⟨52187841638953127748396341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34791894425968751832264227 52187841638953127748396341)
          ·
            refine ⟨4892610153651855726412157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52187841638953127748396341 4892610153651855726412157)
            ·
              refine ⟨1834728807619445897404559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4892610153651855726412157 1834728807619445897404559)
              ·
                refine ⟨2752093211429168846106839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834728807619445897404559 2752093211429168846106839)
                ·
                  refine ⟨4128139817143753269160259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752093211429168846106839 4128139817143753269160259)
                  ·
                    refine ⟨6192209725715629903740389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4128139817143753269160259 6192209725715629903740389)
                    ·
                      refine ⟨1161039323571680606951323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6192209725715629903740389 1161039323571680606951323)
                      ·
                        rfl

theorem cell23_2261116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_2261116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261116 prefixEnd_2261116 := by exact prefixLift 2261116
  have htrace : WordTrace (prefixWord ++ tailWord_2261116) baseStart_2261116 baseEnd_2261116 := by
    simpa [prefixWord, tailWord_2261116, baseEnd_2261116] using wordTrace_append hprefix tailTrace_2261116
  have hstable : (prefixWord ++ tailWord_2261116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261116).length < 2 ^ (prefixWord ++ tailWord_2261116).sum := by decide
  have hdescent : baseEnd_2261116 < baseStart_2261116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261146 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2261146 : Nat := 118140960795 + 2261146 * 2 ^ 59
def prefixEnd_2261146 : Nat := 4983230072969 + 3 ^ 40 * 2261146 * 2
def baseEnd_2261146 : Nat := 1161054727991315489576185

theorem tailTrace_2261146 : CollatzResearch.WordTrace tailWord_2261146 prefixEnd_2261146 1161054727991315489576185 := by
  unfold tailWord_2261146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617692466565422459276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54980513244174459891404861 20617692466565422459276823)
  ·
    refine ⟨30926538699848133688915235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20617692466565422459276823 30926538699848133688915235)
    ·
      refine ⟨46389808049772200533372853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30926538699848133688915235 46389808049772200533372853)
      ·
        refine ⟨4349044504666143800003705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46389808049772200533372853 4349044504666143800003705)
        ·
          refine ⟨3261783378499607850002779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4349044504666143800003705 3261783378499607850002779)
          ·
            refine ⟨4892675067749411775004169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261783378499607850002779 4892675067749411775004169)
            ·
              refine ⟨3669506300812058831253127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892675067749411775004169 3669506300812058831253127)
              ·
                refine ⟨5504259451218088246879691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669506300812058831253127 5504259451218088246879691)
                ·
                  refine ⟨8256389176827132370319537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5504259451218088246879691 8256389176827132370319537)
                  ·
                    refine ⟨6192291882620349277739653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8256389176827132370319537 6192291882620349277739653)
                    ·
                      refine ⟨1161054727991315489576185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6192291882620349277739653 1161054727991315489576185)
                      ·
                        rfl

theorem cell23_2261146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2261146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261146 prefixEnd_2261146 := by exact prefixLift 2261146
  have htrace : WordTrace (prefixWord ++ tailWord_2261146) baseStart_2261146 baseEnd_2261146 := by
    simpa [prefixWord, tailWord_2261146, baseEnd_2261146] using wordTrace_append hprefix tailTrace_2261146
  have hstable : (prefixWord ++ tailWord_2261146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261146).length < 2 ^ (prefixWord ++ tailWord_2261146).sum := by decide
  have hdescent : baseEnd_2261146 < baseStart_2261146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261149 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2261149 : Nat := 118140960795 + 2261149 * 2 ^ 59
def prefixEnd_2261149 : Nat := 4983230072969 + 3 ^ 40 * 2261149 * 2
def baseEnd_2261149 : Nat := 1161056268433278977838671

theorem tailTrace_2261149 : CollatzResearch.WordTrace tailWord_2261149 prefixEnd_2261149 1161056268433278977838671 := by
  unfold tailWord_2261149
  simp only [CollatzResearch.WordTrace]
  refine ⟨82470879285250821349466501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54980586190167214232977667 82470879285250821349466501)
  ·
    refine ⟨15463289865984529003024969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82470879285250821349466501 15463289865984529003024969)
    ·
      refine ⟨11597467399488396752268727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15463289865984529003024969 11597467399488396752268727)
      ·
        refine ⟨17396201099232595128403091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597467399488396752268727 17396201099232595128403091)
        ·
          refine ⟨26094301648848892692604637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17396201099232595128403091 26094301648848892692604637)
          ·
            refine ⟨9785363118318334759726739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26094301648848892692604637 9785363118318334759726739)
            ·
              refine ⟨14678044677477502139590109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785363118318334759726739 14678044677477502139590109)
              ·
                refine ⟨5504266754054063302346291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14678044677477502139590109 5504266754054063302346291)
                ·
                  refine ⟨8256400131081094953519437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5504266754054063302346291 8256400131081094953519437)
                  ·
                    refine ⟨3096150049155410607569789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8256400131081094953519437 3096150049155410607569789)
                    ·
                      refine ⟨1161056268433278977838671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096150049155410607569789 1161056268433278977838671)
                      ·
                        rfl

theorem cell23_2261149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2261149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261149 prefixEnd_2261149 := by exact prefixLift 2261149
  have htrace : WordTrace (prefixWord ++ tailWord_2261149) baseStart_2261149 baseEnd_2261149 := by
    simpa [prefixWord, tailWord_2261149, baseEnd_2261149] using wordTrace_append hprefix tailTrace_2261149
  have hstable : (prefixWord ++ tailWord_2261149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261149).length < 2 ^ (prefixWord ++ tailWord_2261149).sum := by decide
  have hdescent : baseEnd_2261149 < baseStart_2261149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261150 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2261150 : Nat := 118140960795 + 2261150 * 2 ^ 59
def prefixEnd_2261150 : Nat := 4983230072969 + 3 ^ 40 * 2261150 * 2
def baseEnd_2261150 : Nat := 1161056781913933473926167

theorem tailTrace_2261150 : CollatzResearch.WordTrace tailWord_2261150 prefixEnd_2261150 1161056781913933473926167 := by
  unfold tailWord_2261150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308864469780899815031613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54980610505498132346835269 10308864469780899815031613)
  ·
    refine ⟨3865824176167837430636855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10308864469780899815031613 3865824176167837430636855)
    ·
      refine ⟨5798736264251756145955283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865824176167837430636855 5798736264251756145955283)
      ·
        refine ⟨8698104396377634218932925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798736264251756145955283 8698104396377634218932925)
        ·
          refine ⟨3261789148641612832099847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8698104396377634218932925 3261789148641612832099847)
          ·
            refine ⟨4892683722962419248149771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261789148641612832099847 4892683722962419248149771)
            ·
              refine ⟨7339025584443628872224657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892683722962419248149771 7339025584443628872224657)
              ·
                refine ⟨5504269188332721654168493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7339025584443628872224657 5504269188332721654168493)
                ·
                  refine ⟨2064100945624770620313185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5504269188332721654168493 2064100945624770620313185)
                  ·
                    refine ⟨1548075709218577965234889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064100945624770620313185 1548075709218577965234889)
                    ·
                      refine ⟨1161056781913933473926167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548075709218577965234889 1161056781913933473926167)
                      ·
                        rfl

theorem cell23_2261150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2261150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261150 prefixEnd_2261150 := by exact prefixLift 2261150
  have htrace : WordTrace (prefixWord ++ tailWord_2261150) baseStart_2261150 baseEnd_2261150 := by
    simpa [prefixWord, tailWord_2261150, baseEnd_2261150] using wordTrace_append hprefix tailTrace_2261150
  have hstable : (prefixWord ++ tailWord_2261150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261150).length < 2 ^ (prefixWord ++ tailWord_2261150).sum := by decide
  have hdescent : baseEnd_2261150 < baseStart_2261150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261176 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_2261176 : Nat := 118140960795 + 2261176 * 2 ^ 59
def prefixEnd_2261176 : Nat := 4983230072969 + 3 ^ 40 * 2261176 * 2
def baseEnd_2261176 : Nat := 1161070132410950372201047

theorem tailTrace_2261176 : CollatzResearch.WordTrace tailWord_2261176 prefixEnd_2261176 1161070132410950372201047 := by
  unfold tailWord_2261176
  simp only [CollatzResearch.WordTrace]
  refine ⟨41235932028076502480349691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54981242704102003307132921 41235932028076502480349691)
  ·
    refine ⟨61853898042114753720524537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41235932028076502480349691 61853898042114753720524537)
    ·
      refine ⟨46390423531586065290393403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61853898042114753720524537 46390423531586065290393403)
      ·
        refine ⟨69585635297379097935590105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46390423531586065290393403 69585635297379097935590105)
        ·
          refine ⟨52189226473034323451692579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69585635297379097935590105 52189226473034323451692579)
          ·
            refine ⟨78283839709551485177538869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52189226473034323451692579 78283839709551485177538869)
            ·
              refine ⟨7339109972770451735394269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78283839709551485177538869 7339109972770451735394269)
              ·
                refine ⟨2752166239788919400772851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7339109972770451735394269 2752166239788919400772851)
                ·
                  refine ⟨4128249359683379101159277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752166239788919400772851 4128249359683379101159277)
                  ·
                    refine ⟨1548093509881267162934729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4128249359683379101159277 1548093509881267162934729)
                    ·
                      refine ⟨1161070132410950372201047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548093509881267162934729 1161070132410950372201047)
                      ·
                        rfl

theorem cell23_2261176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_2261176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261176 prefixEnd_2261176 := by exact prefixLift 2261176
  have htrace : WordTrace (prefixWord ++ tailWord_2261176) baseStart_2261176 baseEnd_2261176 := by
    simpa [prefixWord, tailWord_2261176, baseEnd_2261176] using wordTrace_append hprefix tailTrace_2261176
  have hstable : (prefixWord ++ tailWord_2261176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261176).length < 2 ^ (prefixWord ++ tailWord_2261176).sum := by decide
  have hdescent : baseEnd_2261176 < baseStart_2261176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261189 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_2261189 : Nat := 118140960795 + 2261189 * 2 ^ 59
def prefixEnd_2261189 : Nat := 4983230072969 + 3 ^ 40 * 2261189 * 2
def baseEnd_2261189 : Nat := 1161076807659458821338487

theorem tailTrace_2261189 : CollatzResearch.WordTrace tailWord_2261189 prefixEnd_2261189 1161076807659458821338487 := by
  unfold tailWord_2261189
  simp only [CollatzResearch.WordTrace]
  refine ⟨82472338205105908180922621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54981558803403938787281747 82472338205105908180922621)
  ·
    refine ⟨30927126826914715567845983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82472338205105908180922621 30927126826914715567845983)
    ·
      refine ⟨46390690240372073351768975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30927126826914715567845983 46390690240372073351768975)
      ·
        refine ⟨69586035360558110027653463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46390690240372073351768975 69586035360558110027653463)
        ·
          refine ⟨104379053040837165041480195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69586035360558110027653463 104379053040837165041480195)
          ·
            refine ⟨156568579561255747562220293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104379053040837165041480195 156568579561255747562220293)
            ·
              refine ⟨29356608667735452667916305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156568579561255747562220293 29356608667735452667916305)
              ·
                refine ⟨22017456500801589500937229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29356608667735452667916305 22017456500801589500937229)
                ·
                  refine ⟨8256546187800596062851461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22017456500801589500937229 8256546187800596062851461)
                  ·
                    refine ⟨1548102410212611761784649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8256546187800596062851461 1548102410212611761784649)
                    ·
                      refine ⟨1161076807659458821338487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548102410212611761784649 1161076807659458821338487)
                      ·
                        rfl

theorem cell23_2261189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_2261189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261189 prefixEnd_2261189 := by exact prefixLift 2261189
  have htrace : WordTrace (prefixWord ++ tailWord_2261189) baseStart_2261189 baseEnd_2261189 := by
    simpa [prefixWord, tailWord_2261189, baseEnd_2261189] using wordTrace_append hprefix tailTrace_2261189
  have hstable : (prefixWord ++ tailWord_2261189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261189).length < 2 ^ (prefixWord ++ tailWord_2261189).sum := by decide
  have hdescent : baseEnd_2261189 < baseStart_2261189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261192 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2261192 : Nat := 118140960795 + 2261192 * 2 ^ 59
def prefixEnd_2261192 : Nat := 4983230072969 + 3 ^ 40 * 2261192 * 2
def baseEnd_2261192 : Nat := 1161078348101422309600973

theorem tailTrace_2261192 : CollatzResearch.WordTrace tailWord_2261192 prefixEnd_2261192 1161078348101422309600973 := by
  unfold tailWord_2261192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41236223812047519846640915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54981631749396693128854553 41236223812047519846640915)
  ·
    refine ⟨61854335718071279769961373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41236223812047519846640915 61854335718071279769961373)
    ·
      refine ⟨23195375894276729913735515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61854335718071279769961373 23195375894276729913735515)
      ·
        refine ⟨34793063841415094870603273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23195375894276729913735515 34793063841415094870603273)
        ·
          refine ⟨26094797881061321152952455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34793063841415094870603273 26094797881061321152952455)
          ·
            refine ⟨39142196821591981729428683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26094797881061321152952455 39142196821591981729428683)
            ·
              refine ⟨58713295232387972594143025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39142196821591981729428683 58713295232387972594143025)
              ·
                refine ⟨44034971424290979445607269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58713295232387972594143025 44034971424290979445607269)
                ·
                  refine ⟨8256557142054558646051363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44034971424290979445607269 8256557142054558646051363)
                  ·
                    refine ⟨12384835713081837969077045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8256557142054558646051363 12384835713081837969077045)
                    ·
                      refine ⟨1161078348101422309600973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12384835713081837969077045 1161078348101422309600973)
                      ·
                        rfl

theorem cell23_2261192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2261192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261192 prefixEnd_2261192 := by exact prefixLift 2261192
  have htrace : WordTrace (prefixWord ++ tailWord_2261192) baseStart_2261192 baseEnd_2261192 := by
    simpa [prefixWord, tailWord_2261192, baseEnd_2261192] using wordTrace_append hprefix tailTrace_2261192
  have hstable : (prefixWord ++ tailWord_2261192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261192).length < 2 ^ (prefixWord ++ tailWord_2261192).sum := by decide
  have hdescent : baseEnd_2261192 < baseStart_2261192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261218 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2261218 : Nat := 118140960795 + 2261218 * 2 ^ 59
def prefixEnd_2261218 : Nat := 4983230072969 + 3 ^ 40 * 2261218 * 2
def baseEnd_2261218 : Nat := 1161091698598439207875855

theorem tailTrace_2261218 : CollatzResearch.WordTrace tailWord_2261218 prefixEnd_2261218 1161091698598439207875855 := by
  unfold tailWord_2261218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20618348980500211533432077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54982263948000564089152205 20618348980500211533432077)
  ·
    refine ⟨7731880867687579325037029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20618348980500211533432077 7731880867687579325037029)
    ·
      refine ⟨1449727662691421123444443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7731880867687579325037029 1449727662691421123444443)
      ·
        refine ⟨2174591494037131685166665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449727662691421123444443 2174591494037131685166665)
        ·
          refine ⟨1630943620527848763874999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2174591494037131685166665 1630943620527848763874999)
          ·
            refine ⟨2446415430791773145812499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630943620527848763874999 2446415430791773145812499)
            ·
              refine ⟨3669623146187659718718749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446415430791773145812499 3669623146187659718718749)
              ·
                refine ⟨1376108679820372394519531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3669623146187659718718749 1376108679820372394519531)
                ·
                  refine ⟨2064163019730558591779297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376108679820372394519531 2064163019730558591779297)
                  ·
                    refine ⟨1548122264797918943834473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064163019730558591779297 1548122264797918943834473)
                    ·
                      refine ⟨1161091698598439207875855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548122264797918943834473 1161091698598439207875855)
                      ·
                        rfl

theorem cell23_2261218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2261218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261218 prefixEnd_2261218 := by exact prefixLift 2261218
  have htrace : WordTrace (prefixWord ++ tailWord_2261218) baseStart_2261218 baseEnd_2261218 := by
    simpa [prefixWord, tailWord_2261218, baseEnd_2261218] using wordTrace_append hprefix tailTrace_2261218
  have hstable : (prefixWord ++ tailWord_2261218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261218).length < 2 ^ (prefixWord ++ tailWord_2261218).sum := by decide
  have hdescent : baseEnd_2261218 < baseStart_2261218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261223 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2261223 : Nat := 118140960795 + 2261223 * 2 ^ 59
def prefixEnd_2261223 : Nat := 4983230072969 + 3 ^ 40 * 2261223 * 2
def baseEnd_2261223 : Nat := 1161094266001711688313331

theorem tailTrace_2261223 : CollatzResearch.WordTrace tailWord_2261223 prefixEnd_2261223 1161094266001711688313331 := by
  unfold tailWord_2261223
  simp only [CollatzResearch.WordTrace]
  refine ⟨82473578286982731987660323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54982385524655154658440215 82473578286982731987660323)
  ·
    refine ⟨123710367430474097981490485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82473578286982731987660323 123710367430474097981490485)
    ·
      refine ⟨11597846946606946685764733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123710367430474097981490485 11597846946606946685764733)
      ·
        refine ⟨4349192604977605007161775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11597846946606946685764733 4349192604977605007161775)
        ·
          refine ⟨6523788907466407510742663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349192604977605007161775 6523788907466407510742663)
          ·
            refine ⟨9785683361199611266113995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523788907466407510742663 9785683361199611266113995)
            ·
              refine ⟨14678525041799416899170993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785683361199611266113995 14678525041799416899170993)
              ·
                refine ⟨11008893781349562674378245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14678525041799416899170993 11008893781349562674378245)
                ·
                  refine ⟨2064167584003043001445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11008893781349562674378245 2064167584003043001445921)
                  ·
                    refine ⟨1548125688002282251084441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064167584003043001445921 1548125688002282251084441)
                    ·
                      refine ⟨1161094266001711688313331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548125688002282251084441 1161094266001711688313331)
                      ·
                        rfl

theorem cell23_2261223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2261223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261223 prefixEnd_2261223 := by exact prefixLift 2261223
  have htrace : WordTrace (prefixWord ++ tailWord_2261223) baseStart_2261223 baseEnd_2261223 := by
    simpa [prefixWord, tailWord_2261223, baseEnd_2261223] using wordTrace_append hprefix tailTrace_2261223
  have hstable : (prefixWord ++ tailWord_2261223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261223).length < 2 ^ (prefixWord ++ tailWord_2261223).sum := by decide
  have hdescent : baseEnd_2261223 < baseStart_2261223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261319 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 6]
def baseStart_2261319 : Nat := 118140960795 + 2261319 * 2 ^ 59
def prefixEnd_2261319 : Nat := 4983230072969 + 3 ^ 40 * 2261319 * 2
def baseEnd_2261319 : Nat := 129015951127171479190321

theorem tailTrace_2261319 : CollatzResearch.WordTrace tailWord_2261319 prefixEnd_2261319 129015951127171479190321 := by
  unfold tailWord_2261319
  simp only [CollatzResearch.WordTrace]
  refine ⟨82477079694634940383155011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54984719796423293588770007 82477079694634940383155011)
  ·
    refine ⟨123715619541952410574732517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82477079694634940383155011 123715619541952410574732517)
    ·
      refine ⟨23196678664116076982762347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123715619541952410574732517 23196678664116076982762347)
      ·
        refine ⟨34795017996174115474143521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23196678664116076982762347 34795017996174115474143521)
        ·
          refine ⟨26096263497130586605607641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34795017996174115474143521 26096263497130586605607641)
          ·
            refine ⟨19572197622847939954205731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26096263497130586605607641 19572197622847939954205731)
            ·
              refine ⟨29358296434271909931308597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19572197622847939954205731 29358296434271909931308597)
              ·
                refine ⟨2752340290712991556060181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29358296434271909931308597 2752340290712991556060181)
                ·
                  refine ⟨129015951127171479190321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2752340290712991556060181 129015951127171479190321)
                  ·
                    rfl

theorem cell23_2261319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 6].length) (baseStart_2261319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261319 prefixEnd_2261319 := by exact prefixLift 2261319
  have htrace : WordTrace (prefixWord ++ tailWord_2261319) baseStart_2261319 baseEnd_2261319 := by
    simpa [prefixWord, tailWord_2261319, baseEnd_2261319] using wordTrace_append hprefix tailTrace_2261319
  have hstable : (prefixWord ++ tailWord_2261319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261319).length < 2 ^ (prefixWord ++ tailWord_2261319).sum := by decide
  have hdescent : baseEnd_2261319 < baseStart_2261319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261449 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_2261449 : Nat := 118140960795 + 2261449 * 2 ^ 59
def prefixEnd_2261449 : Nat := 4983230072969 + 3 ^ 40 * 2261449 * 2
def baseEnd_2261449 : Nat := 1161210312629627804087291

theorem tailTrace_2261449 : CollatzResearch.WordTrace tailWord_2261449 prefixEnd_2261449 1161210312629627804087291 := by
  unfold tailWord_2261449
  simp only [CollatzResearch.WordTrace]
  refine ⟨82481821184163972585387401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54987880789442648390258267 82481821184163972585387401)
  ·
    refine ⟨61861365888122979439040551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82481821184163972585387401 61861365888122979439040551)
    ·
      refine ⟨92792048832184469158560827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61861365888122979439040551 92792048832184469158560827)
      ·
        refine ⟨139188073248276703737841241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92792048832184469158560827 139188073248276703737841241)
        ·
          refine ⟨104391054936207527803380931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139188073248276703737841241 104391054936207527803380931)
          ·
            refine ⟨156586582404311291705071397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104391054936207527803380931 156586582404311291705071397)
            ·
              refine ⟨29359984200808367194700887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156586582404311291705071397 29359984200808367194700887)
              ·
                refine ⟨44039976301212550792051331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29359984200808367194700887 44039976301212550792051331)
                ·
                  refine ⟨66059964451818826188076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44039976301212550792051331 66059964451818826188076997)
                  ·
                    refine ⟨12386243334716029910264437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66059964451818826188076997 12386243334716029910264437)
                    ·
                      refine ⟨1161210312629627804087291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12386243334716029910264437 1161210312629627804087291)
                      ·
                        rfl

theorem cell23_2261449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_2261449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261449 prefixEnd_2261449 := by exact prefixLift 2261449
  have htrace : WordTrace (prefixWord ++ tailWord_2261449) baseStart_2261449 baseEnd_2261449 := by
    simpa [prefixWord, tailWord_2261449, baseEnd_2261449] using wordTrace_append hprefix tailTrace_2261449
  have hstable : (prefixWord ++ tailWord_2261449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261449).length < 2 ^ (prefixWord ++ tailWord_2261449).sum := by decide
  have hdescent : baseEnd_2261449 < baseStart_2261449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261486 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2261486 : Nat := 118140960795 + 2261486 * 2 ^ 59
def prefixEnd_2261486 : Nat := 4983230072969 + 3 ^ 40 * 2261486 * 2
def baseEnd_2261486 : Nat := 387076437137948053108207

theorem tailTrace_2261486 : CollatzResearch.WordTrace tailWord_2261486 prefixEnd_2261486 387076437137948053108207 := by
  unfold tailWord_2261486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10310396335628740988060539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54988780456686618602989541 10310396335628740988060539)
  ·
    refine ⟨15465594503443111482090809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10310396335628740988060539 15465594503443111482090809)
    ·
      refine ⟨11599195877582333611568107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15465594503443111482090809 11599195877582333611568107)
      ·
        refine ⟨17398793816373500417352161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11599195877582333611568107 17398793816373500417352161)
        ·
          refine ⟨13049095362280125313014121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17398793816373500417352161 13049095362280125313014121)
          ·
            refine ⟨9786821521710093984760591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13049095362280125313014121 9786821521710093984760591)
            ·
              refine ⟨14680232282565140977140887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9786821521710093984760591 14680232282565140977140887)
              ·
                refine ⟨22020348423847711465711331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14680232282565140977140887 22020348423847711465711331)
                ·
                  refine ⟨33030522635771567198566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22020348423847711465711331 33030522635771567198566997)
                  ·
                    refine ⟨387076437137948053108207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33030522635771567198566997 387076437137948053108207)
                    ·
                      rfl

theorem cell23_2261486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2261486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261486 prefixEnd_2261486 := by exact prefixLift 2261486
  have htrace : WordTrace (prefixWord ++ tailWord_2261486) baseStart_2261486 baseEnd_2261486 := by
    simpa [prefixWord, tailWord_2261486, baseEnd_2261486] using wordTrace_append hprefix tailTrace_2261486
  have hstable : (prefixWord ++ tailWord_2261486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261486).length < 2 ^ (prefixWord ++ tailWord_2261486).sum := by decide
  have hdescent : baseEnd_2261486 < baseStart_2261486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261496 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2261496 : Nat := 118140960795 + 2261496 * 2 ^ 59
def prefixEnd_2261496 : Nat := 4983230072969 + 3 ^ 40 * 2261496 * 2
def baseEnd_2261496 : Nat := 1161234446220389120199575

theorem tailTrace_2261496 : CollatzResearch.WordTrace tailWord_2261496 prefixEnd_2261496 1161234446220389120199575 := by
  unfold tailWord_2261496
  simp only [CollatzResearch.WordTrace]
  refine ⟨41241767707496849806174171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54989023609995799741565561 41241767707496849806174171)
  ·
    refine ⟨61862651561245274709261257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41241767707496849806174171 61862651561245274709261257)
    ·
      refine ⟨46396988670933956031945943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61862651561245274709261257 46396988670933956031945943)
      ·
        refine ⟨69595483006400934047918915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46396988670933956031945943 69595483006400934047918915)
        ·
          refine ⟨104393224509601401071878373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69595483006400934047918915 104393224509601401071878373)
          ·
            refine ⟨19573729595550262700977195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104393224509601401071878373 19573729595550262700977195)
            ·
              refine ⟨29360594393325394051465793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19573729595550262700977195 29360594393325394051465793)
              ·
                refine ⟨22020445794994045538599345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29360594393325394051465793 22020445794994045538599345)
                ·
                  refine ⟨16515334346245534153949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22020445794994045538599345 16515334346245534153949509)
                  ·
                    refine ⟨3096625189921037653865533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16515334346245534153949509 3096625189921037653865533)
                    ·
                      refine ⟨1161234446220389120199575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096625189921037653865533 1161234446220389120199575)
                      ·
                        rfl

theorem cell23_2261496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2261496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261496 prefixEnd_2261496 := by exact prefixLift 2261496
  have htrace : WordTrace (prefixWord ++ tailWord_2261496) baseStart_2261496 baseEnd_2261496 := by
    simpa [prefixWord, tailWord_2261496, baseEnd_2261496] using wordTrace_append hprefix tailTrace_2261496
  have hstable : (prefixWord ++ tailWord_2261496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261496).length < 2 ^ (prefixWord ++ tailWord_2261496).sum := by decide
  have hdescent : baseEnd_2261496 < baseStart_2261496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261533 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 7]
def baseStart_2261533 : Nat := 118140960795 + 2261533 * 2 ^ 59
def prefixEnd_2261533 : Nat := 4983230072969 + 3 ^ 40 * 2261533 * 2
def baseEnd_2261533 : Nat := 129028160556067275048545

theorem tailTrace_2261533 : CollatzResearch.WordTrace tailWord_2261533 prefixEnd_2261533 129028160556067275048545 := by
  unfold tailWord_2261533
  simp only [CollatzResearch.WordTrace]
  refine ⟨82484884915859654931445253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54989923277239769954296835 82484884915859654931445253)
  ·
    refine ⟨15465915921723685299645985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82484884915859654931445253 15465915921723685299645985)
    ·
      refine ⟨11599436941292763974734489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15465915921723685299645985 11599436941292763974734489)
      ·
        refine ⟨8699577705969572981050867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11599436941292763974734489 8699577705969572981050867)
        ·
          refine ⟨13049366558954359471576301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8699577705969572981050867 13049366558954359471576301)
          ·
            refine ⟨4893512459607884801841113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13049366558954359471576301 4893512459607884801841113)
            ·
              refine ⟨3670134344705913601380835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4893512459607884801841113 3670134344705913601380835)
              ·
                refine ⟨5505201517058870402071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670134344705913601380835 5505201517058870402071253)
                ·
                  refine ⟨129028160556067275048545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5505201517058870402071253 129028160556067275048545)
                  ·
                    rfl

theorem cell23_2261533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_2261533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261533 prefixEnd_2261533 := by exact prefixLift 2261533
  have htrace : WordTrace (prefixWord ++ tailWord_2261533) baseStart_2261533 baseEnd_2261533 := by
    simpa [prefixWord, tailWord_2261533, baseEnd_2261533] using wordTrace_append hprefix tailTrace_2261533
  have hstable : (prefixWord ++ tailWord_2261533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261533).length < 2 ^ (prefixWord ++ tailWord_2261533).sum := by decide
  have hdescent : baseEnd_2261533 < baseStart_2261533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261553 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_2261553 : Nat := 118140960795 + 2261553 * 2 ^ 59
def prefixEnd_2261553 : Nat := 4983230072969 + 3 ^ 40 * 2261553 * 2
def baseEnd_2261553 : Nat := 1161263714617695397186813

theorem tailTrace_2261553 : CollatzResearch.WordTrace tailWord_2261553 prefixEnd_2261553 1161263714617695397186813 := by
  unfold tailWord_2261553
  simp only [CollatzResearch.WordTrace]
  refine ⟨82485614375787198347173313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54990409583858132231448875 82485614375787198347173313)
  ·
    refine ⟨61864210781840398760379985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82485614375787198347173313 61864210781840398760379985)
    ·
      refine ⟨46398158086380299070284989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61864210781840398760379985 46398158086380299070284989)
      ·
        refine ⟨17399309282392612151356871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46398158086380299070284989 17399309282392612151356871)
        ·
          refine ⟨26098963923588918227035307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17399309282392612151356871 26098963923588918227035307)
          ·
            refine ⟨39148445885383377340552961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26098963923588918227035307 39148445885383377340552961)
            ·
              refine ⟨29361334414037533005414721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39148445885383377340552961 29361334414037533005414721)
              ·
                refine ⟨22021000810528149754061041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29361334414037533005414721 22021000810528149754061041)
                ·
                  refine ⟨16515750607896112315545781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22021000810528149754061041 16515750607896112315545781)
                  ·
                    refine ⟨1548351619490260529582417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16515750607896112315545781 1548351619490260529582417)
                    ·
                      refine ⟨1161263714617695397186813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548351619490260529582417 1161263714617695397186813)
                      ·
                        rfl

theorem cell23_2261553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_2261553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261553 prefixEnd_2261553 := by exact prefixLift 2261553
  have htrace : WordTrace (prefixWord ++ tailWord_2261553) baseStart_2261553 baseEnd_2261553 := by
    simpa [prefixWord, tailWord_2261553, baseEnd_2261553] using wordTrace_append hprefix tailTrace_2261553
  have hstable : (prefixWord ++ tailWord_2261553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261553).length < 2 ^ (prefixWord ++ tailWord_2261553).sum := by decide
  have hdescent : baseEnd_2261553 < baseStart_2261553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261583 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 4, 2]
def baseStart_2261583 : Nat := 118140960795 + 2261583 * 2 ^ 59
def prefixEnd_2261583 : Nat := 4983230072969 + 3 ^ 40 * 2261583 * 2
def baseEnd_2261583 : Nat := 1161279119037330279811675

theorem tailTrace_2261583 : CollatzResearch.WordTrace tailWord_2261583 prefixEnd_2261583 1161279119037330279811675 := by
  unfold tailWord_2261583
  simp only [CollatzResearch.WordTrace]
  refine ⟨82486708565678513470765403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54991139043785675647176935 82486708565678513470765403)
  ·
    refine ⟨123730062848517770206148105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82486708565678513470765403 123730062848517770206148105)
    ·
      refine ⟨92797547136388327654611079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123730062848517770206148105 92797547136388327654611079)
      ·
        refine ⟨139196320704582491481916619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92797547136388327654611079 139196320704582491481916619)
        ·
          refine ⟨208794481056873737222874929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139196320704582491481916619 208794481056873737222874929)
          ·
            refine ⟨156595860792655302917156197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208794481056873737222874929 156595860792655302917156197)
            ·
              refine ⟨29361723898622869296966787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156595860792655302917156197 29361723898622869296966787)
              ·
                refine ⟨44042585847934303945450181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29361723898622869296966787 44042585847934303945450181)
                ·
                  refine ⟨8257984846487681989771909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44042585847934303945450181 8257984846487681989771909)
                  ·
                    refine ⟨1548372158716440373082233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8257984846487681989771909 1548372158716440373082233)
                    ·
                      refine ⟨1161279119037330279811675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548372158716440373082233 1161279119037330279811675)
                      ·
                        rfl

theorem cell23_2261583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4, 2].length) (baseStart_2261583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261583 prefixEnd_2261583 := by exact prefixLift 2261583
  have htrace : WordTrace (prefixWord ++ tailWord_2261583) baseStart_2261583 baseEnd_2261583 := by
    simpa [prefixWord, tailWord_2261583, baseEnd_2261583] using wordTrace_append hprefix tailTrace_2261583
  have hstable : (prefixWord ++ tailWord_2261583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261583).length < 2 ^ (prefixWord ++ tailWord_2261583).sum := by decide
  have hdescent : baseEnd_2261583 < baseStart_2261583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261603 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2261603 : Nat := 118140960795 + 2261603 * 2 ^ 59
def prefixEnd_2261603 : Nat := 4983230072969 + 3 ^ 40 * 2261603 * 2
def baseEnd_2261603 : Nat := 1161289388650420201561583

theorem tailTrace_2261603 : CollatzResearch.WordTrace tailWord_2261603 prefixEnd_2261603 1161289388650420201561583 := by
  unfold tailWord_2261603
  simp only [CollatzResearch.WordTrace]
  refine ⟨82487438025606056886493463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54991625350404037924328975 82487438025606056886493463)
  ·
    refine ⟨123731157038409085329740195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82487438025606056886493463 123731157038409085329740195)
    ·
      refine ⟨185596735557613627994610293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123731157038409085329740195 185596735557613627994610293)
      ·
        refine ⟨17399693958526277624494715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185596735557613627994610293 17399693958526277624494715)
        ·
          refine ⟨26099540937789416436742073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17399693958526277624494715 26099540937789416436742073)
          ·
            refine ⟨19574655703342062327556555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26099540937789416436742073 19574655703342062327556555)
            ·
              refine ⟨29361983555013093491334833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19574655703342062327556555 29361983555013093491334833)
              ·
                refine ⟨22021487666259820118501125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29361983555013093491334833 22021487666259820118501125)
                ·
                  refine ⟨4129028937423716272218961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22021487666259820118501125 4129028937423716272218961)
                  ·
                    refine ⟨3096771703067787204164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129028937423716272218961 3096771703067787204164221)
                    ·
                      refine ⟨1161289388650420201561583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096771703067787204164221 1161289388650420201561583)
                      ·
                        rfl

theorem cell23_2261603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2261603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261603 prefixEnd_2261603 := by exact prefixLift 2261603
  have htrace : WordTrace (prefixWord ++ tailWord_2261603) baseStart_2261603 baseEnd_2261603 := by
    simpa [prefixWord, tailWord_2261603, baseEnd_2261603] using wordTrace_append hprefix tailTrace_2261603
  have hstable : (prefixWord ++ tailWord_2261603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261603).length < 2 ^ (prefixWord ++ tailWord_2261603).sum := by decide
  have hdescent : baseEnd_2261603 < baseStart_2261603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261671 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2261671 : Nat := 118140960795 + 2261671 * 2 ^ 59
def prefixEnd_2261671 : Nat := 4983230072969 + 3 ^ 40 * 2261671 * 2
def baseEnd_2261671 : Nat := 1161324305334925935511271

theorem tailTrace_2261671 : CollatzResearch.WordTrace tailWord_2261671 prefixEnd_2261671 1161324305334925935511271 := by
  unfold tailWord_2261671
  simp only [CollatzResearch.WordTrace]
  refine ⟨82489918189359704499968867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54993278792906469666645911 82489918189359704499968867)
  ·
    refine ⟨123734877284039556749953301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82489918189359704499968867 123734877284039556749953301)
    ·
      refine ⟨5800072372689354222654061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123734877284039556749953301 5800072372689354222654061)
      ·
        refine ⟨2175027139758507833495273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5800072372689354222654061 2175027139758507833495273)
        ·
          refine ⟨1631270354818880875121455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175027139758507833495273 1631270354818880875121455)
          ·
            refine ⟨2446905532228321312682183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631270354818880875121455 2446905532228321312682183)
            ·
              refine ⟨3670358298342481969023275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446905532228321312682183 3670358298342481969023275)
              ·
                refine ⟨5505537447513722953534913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670358298342481969023275 5505537447513722953534913)
                ·
                  refine ⟨4129153085635292215151185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505537447513722953534913 4129153085635292215151185)
                  ·
                    refine ⟨3096864814226469161363389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129153085635292215151185 3096864814226469161363389)
                    ·
                      refine ⟨1161324305334925935511271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096864814226469161363389 1161324305334925935511271)
                      ·
                        rfl

theorem cell23_2261671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2261671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261671 prefixEnd_2261671 := by exact prefixLift 2261671
  have htrace : WordTrace (prefixWord ++ tailWord_2261671) baseStart_2261671 baseEnd_2261671 := by
    simpa [prefixWord, tailWord_2261671, baseEnd_2261671] using wordTrace_append hprefix tailTrace_2261671
  have hstable : (prefixWord ++ tailWord_2261671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261671).length < 2 ^ (prefixWord ++ tailWord_2261671).sum := by decide
  have hdescent : baseEnd_2261671 < baseStart_2261671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261677 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_2261677 : Nat := 118140960795 + 2261677 * 2 ^ 59
def prefixEnd_2261677 : Nat := 4983230072969 + 3 ^ 40 * 2261677 * 2
def baseEnd_2261677 : Nat := 1161327386218852912036243

theorem tailTrace_2261677 : CollatzResearch.WordTrace tailWord_2261677 prefixEnd_2261677 1161327386218852912036243 := by
  unfold tailWord_2261677
  simp only [CollatzResearch.WordTrace]
  refine ⟨82490137027337967524687285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54993424684891978349791523 82490137027337967524687285)
  ·
    refine ⟨7733450346312934455439433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82490137027337967524687285 7733450346312934455439433)
    ·
      refine ⟨5800087759734700841579575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7733450346312934455439433 5800087759734700841579575)
      ·
        refine ⟨8700131639602051262369363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800087759734700841579575 8700131639602051262369363)
        ·
          refine ⟨13050197459403076893554045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700131639602051262369363 13050197459403076893554045)
          ·
            refine ⟨4893824047276153835082767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13050197459403076893554045 4893824047276153835082767)
            ·
              refine ⟨7340736070914230752624151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893824047276153835082767 7340736070914230752624151)
              ·
                refine ⟨11011104106371346128936227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340736070914230752624151 11011104106371346128936227)
                ·
                  refine ⟨16516656159557019193404341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11011104106371346128936227 16516656159557019193404341)
                  ·
                    refine ⟨1548436514958470549381657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16516656159557019193404341 1548436514958470549381657)
                    ·
                      refine ⟨1161327386218852912036243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548436514958470549381657 1161327386218852912036243)
                      ·
                        rfl

theorem cell23_2261677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_2261677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261677 prefixEnd_2261677 := by exact prefixLift 2261677
  have htrace : WordTrace (prefixWord ++ tailWord_2261677) baseStart_2261677 baseEnd_2261677 := by
    simpa [prefixWord, tailWord_2261677, baseEnd_2261677] using wordTrace_append hprefix tailTrace_2261677
  have hstable : (prefixWord ++ tailWord_2261677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261677).length < 2 ^ (prefixWord ++ tailWord_2261677).sum := by decide
  have hdescent : baseEnd_2261677 < baseStart_2261677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261683 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 6]
def baseStart_2261683 : Nat := 118140960795 + 2261683 * 2 ^ 59
def prefixEnd_2261683 : Nat := 4983230072969 + 3 ^ 40 * 2261683 * 2
def baseEnd_2261683 : Nat := 387110155700926629520405

theorem tailTrace_2261683 : CollatzResearch.WordTrace tailWord_2261683 prefixEnd_2261683 387110155700926629520405 := by
  unfold tailWord_2261683
  simp only [CollatzResearch.WordTrace]
  refine ⟨82490355865316230549405703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54993570576877487032937135 82490355865316230549405703)
  ·
    refine ⟨123735533797974345824108555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82490355865316230549405703 123735533797974345824108555)
    ·
      refine ⟨185603300696961518736162833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123735533797974345824108555 185603300696961518736162833)
      ·
        refine ⟨139202475522721139052122125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185603300696961518736162833 139202475522721139052122125)
        ·
          refine ⟨52200928321020427144545797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139202475522721139052122125 52200928321020427144545797)
          ·
            refine ⟨9787674060191330089602337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52200928321020427144545797 9787674060191330089602337)
            ·
              refine ⟨7340755545143497567201753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9787674060191330089602337 7340755545143497567201753)
              ·
                refine ⟨5505566658857623175401315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7340755545143497567201753 5505566658857623175401315)
                ·
                  refine ⟨8258349988286434763101973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505566658857623175401315 8258349988286434763101973)
                  ·
                    refine ⟨387110155700926629520405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8258349988286434763101973 387110155700926629520405)
                    ·
                      rfl

theorem cell23_2261683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_2261683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261683 prefixEnd_2261683 := by exact prefixLift 2261683
  have htrace : WordTrace (prefixWord ++ tailWord_2261683) baseStart_2261683 baseEnd_2261683 := by
    simpa [prefixWord, tailWord_2261683, baseEnd_2261683] using wordTrace_append hprefix tailTrace_2261683
  have hstable : (prefixWord ++ tailWord_2261683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261683).length < 2 ^ (prefixWord ++ tailWord_2261683).sum := by decide
  have hdescent : baseEnd_2261683 < baseStart_2261683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261690 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_2261690 : Nat := 118140960795 + 2261690 * 2 ^ 59
def prefixEnd_2261690 : Nat := 4983230072969 + 3 ^ 40 * 2261690 * 2
def baseEnd_2261690 : Nat := 1161334061467361361173683

theorem tailTrace_2261690 : CollatzResearch.WordTrace tailWord_2261690 prefixEnd_2261690 1161334061467361361173683 := by
  unfold tailWord_2261690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20622652794072717686227631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54993740784193913829940349 20622652794072717686227631)
  ·
    refine ⟨30933979191109076529341447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20622652794072717686227631 30933979191109076529341447)
    ·
      refine ⟨46400968786663614794012171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30933979191109076529341447 46400968786663614794012171)
      ·
        refine ⟨69601453179995422191018257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46400968786663614794012171 69601453179995422191018257)
        ·
          refine ⟨52201089884996566643263693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69601453179995422191018257 52201089884996566643263693)
          ·
            refine ⟨19575408706873712491223885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52201089884996566643263693 19575408706873712491223885)
            ·
              refine ⟨7340778265077642184208957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19575408706873712491223885 7340778265077642184208957)
              ·
                refine ⟨2752791849404115819078359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7340778265077642184208957 2752791849404115819078359)
                ·
                  refine ⟨4129187774106173728617539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752791849404115819078359 4129187774106173728617539)
                  ·
                    refine ⟨6193781661159260592926309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4129187774106173728617539 6193781661159260592926309)
                    ·
                      refine ⟨1161334061467361361173683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6193781661159260592926309 1161334061467361361173683)
                      ·
                        rfl

theorem cell23_2261690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_2261690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261690 prefixEnd_2261690 := by exact prefixLift 2261690
  have htrace : WordTrace (prefixWord ++ tailWord_2261690) baseStart_2261690 baseEnd_2261690 := by
    simpa [prefixWord, tailWord_2261690, baseEnd_2261690] using wordTrace_append hprefix tailTrace_2261690
  have hstable : (prefixWord ++ tailWord_2261690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261690).length < 2 ^ (prefixWord ++ tailWord_2261690).sum := by decide
  have hdescent : baseEnd_2261690 < baseStart_2261690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261710 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2261710 : Nat := 118140960795 + 2261710 * 2 ^ 59
def prefixEnd_2261710 : Nat := 4983230072969 + 3 ^ 40 * 2261710 * 2
def baseEnd_2261710 : Nat := 1161344331080451282923591

theorem tailTrace_2261710 : CollatzResearch.WordTrace tailWord_2261710 prefixEnd_2261710 1161344331080451282923591 := by
  unfold tailWord_2261710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311417579527301770079823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54994227090812276107092389 10311417579527301770079823)
  ·
    refine ⟨15467126369290952655119735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311417579527301770079823 15467126369290952655119735)
    ·
      refine ⟨23200689553936428982679603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467126369290952655119735 23200689553936428982679603)
      ·
        refine ⟨34801034330904643474019405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23200689553936428982679603 34801034330904643474019405)
        ·
          refine ⟨13050387874089241302757277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34801034330904643474019405 13050387874089241302757277)
          ·
            refine ⟨4893895452783465488533979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13050387874089241302757277 4893895452783465488533979)
            ·
              refine ⟨7340843179175198232800969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893895452783465488533979 7340843179175198232800969)
              ·
                refine ⟨5505632384381398674600727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7340843179175198232800969 5505632384381398674600727)
                ·
                  refine ⟨8258448576572098011901091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505632384381398674600727 8258448576572098011901091)
                  ·
                    refine ⟨12387672864858147017851637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8258448576572098011901091 12387672864858147017851637)
                    ·
                      refine ⟨1161344331080451282923591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12387672864858147017851637 1161344331080451282923591)
                      ·
                        rfl

theorem cell23_2261710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2261710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261710 prefixEnd_2261710 := by exact prefixLift 2261710
  have htrace : WordTrace (prefixWord ++ tailWord_2261710) baseStart_2261710 baseEnd_2261710 := by
    simpa [prefixWord, tailWord_2261710, baseEnd_2261710] using wordTrace_append hprefix tailTrace_2261710
  have hstable : (prefixWord ++ tailWord_2261710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261710).length < 2 ^ (prefixWord ++ tailWord_2261710).sum := by decide
  have hdescent : baseEnd_2261710 < baseStart_2261710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261720 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2261720 : Nat := 118140960795 + 2261720 * 2 ^ 59
def prefixEnd_2261720 : Nat := 4983230072969 + 3 ^ 40 * 2261720 * 2
def baseEnd_2261720 : Nat := 1161349465886996243798545

theorem tailTrace_2261720 : CollatzResearch.WordTrace tailWord_2261720 prefixEnd_2261720 1161349465886996243798545 := by
  unfold tailWord_2261720
  simp only [CollatzResearch.WordTrace]
  refine ⟨41245852683091092934251307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54994470244121457245668409 41245852683091092934251307)
  ·
    refine ⟨61868779024636639401376961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41245852683091092934251307 61868779024636639401376961)
    ·
      refine ⟨46401584268477479551032721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61868779024636639401376961 46401584268477479551032721)
      ·
        refine ⟨34801188201358109663274541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46401584268477479551032721 34801188201358109663274541)
        ·
          refine ⟨13050445575509291123727953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34801188201358109663274541 13050445575509291123727953)
          ·
            refine ⟨9787834181631968342795965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13050445575509291123727953 9787834181631968342795965)
            ·
              refine ⟨3670437818111988128548487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9787834181631968342795965 3670437818111988128548487)
              ·
                refine ⟨5505656727167982192822731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670437818111988128548487 5505656727167982192822731)
                ·
                  refine ⟨8258485090751973289234097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505656727167982192822731 8258485090751973289234097)
                  ·
                    refine ⟨6193863818063979966925573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8258485090751973289234097 6193863818063979966925573)
                    ·
                      refine ⟨1161349465886996243798545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6193863818063979966925573 1161349465886996243798545)
                      ·
                        rfl

theorem cell23_2261720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2261720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261720 prefixEnd_2261720 := by exact prefixLift 2261720
  have htrace : WordTrace (prefixWord ++ tailWord_2261720) baseStart_2261720 baseEnd_2261720 := by
    simpa [prefixWord, tailWord_2261720, baseEnd_2261720] using wordTrace_append hprefix tailTrace_2261720
  have hstable : (prefixWord ++ tailWord_2261720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261720).length < 2 ^ (prefixWord ++ tailWord_2261720).sum := by decide
  have hdescent : baseEnd_2261720 < baseStart_2261720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261723 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3]
def baseStart_2261723 : Nat := 118140960795 + 2261723 * 2 ^ 59
def prefixEnd_2261723 : Nat := 4983230072969 + 3 ^ 40 * 2261723 * 2
def baseEnd_2261723 : Nat := 1161351006328959732061031

theorem tailTrace_2261723 : CollatzResearch.WordTrace tailWord_2261723 prefixEnd_2261723 1161351006328959732061031 := by
  unfold tailWord_2261723
  simp only [CollatzResearch.WordTrace]
  refine ⟨82491814785171317380861823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54994543190114211587241215 82491814785171317380861823)
  ·
    refine ⟨123737722177756976071292735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82491814785171317380861823 123737722177756976071292735)
    ·
      refine ⟨185606583266635464106939103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123737722177756976071292735 185606583266635464106939103)
      ·
        refine ⟨278409874899953196160408655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185606583266635464106939103 278409874899953196160408655)
        ·
          refine ⟨417614812349929794240612983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278409874899953196160408655 417614812349929794240612983)
          ·
            refine ⟨626422218524894691360919475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417614812349929794240612983 626422218524894691360919475)
            ·
              refine ⟨939633327787342037041379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626422218524894691360919475 939633327787342037041379213)
              ·
                refine ⟨352362497920253263890517205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939633327787342037041379213 352362497920253263890517205)
                ·
                  refine ⟨8258496045005935872433997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 352362497920253263890517205 8258496045005935872433997)
                  ·
                    refine ⟨3096936016877225952162749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8258496045005935872433997 3096936016877225952162749)
                    ·
                      refine ⟨1161351006328959732061031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096936016877225952162749 1161351006328959732061031)
                      ·
                        rfl

theorem cell23_2261723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].length) (baseStart_2261723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261723 prefixEnd_2261723 := by exact prefixLift 2261723
  have htrace : WordTrace (prefixWord ++ tailWord_2261723) baseStart_2261723 baseEnd_2261723 := by
    simpa [prefixWord, tailWord_2261723, baseEnd_2261723] using wordTrace_append hprefix tailTrace_2261723
  have hstable : (prefixWord ++ tailWord_2261723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261723).length < 2 ^ (prefixWord ++ tailWord_2261723).sum := by decide
  have hdescent : baseEnd_2261723 < baseStart_2261723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261724 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2261724 : Nat := 118140960795 + 2261724 * 2 ^ 59
def prefixEnd_2261724 : Nat := 4983230072969 + 3 ^ 40 * 2261724 * 2
def baseEnd_2261724 : Nat := 1161351519809614228148527

theorem tailTrace_2261724 : CollatzResearch.WordTrace tailWord_2261724 prefixEnd_2261724 1161351519809614228148527 := by
  unfold tailWord_2261724
  simp only [CollatzResearch.WordTrace]
  refine ⟨41245925629083847275824113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54994567505445129701098817 41245925629083847275824113)
  ·
    refine ⟨30934444221812885456868085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41245925629083847275824113 30934444221812885456868085)
    ·
      refine ⟨2900104145794958011581383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30934444221812885456868085 2900104145794958011581383)
      ·
        refine ⟨4350156218692437017372075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900104145794958011581383 4350156218692437017372075)
        ·
          refine ⟨6525234328038655526058113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350156218692437017372075 6525234328038655526058113)
          ·
            refine ⟨4893925746028991644543585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6525234328038655526058113 4893925746028991644543585)
            ·
              refine ⟨3670444309521743733407689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4893925746028991644543585 3670444309521743733407689)
              ·
                refine ⟨2752833232141307800055767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670444309521743733407689 2752833232141307800055767)
                ·
                  refine ⟨4129249848211961700083651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752833232141307800055767 4129249848211961700083651)
                  ·
                    refine ⟨6193874772317942550125477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4129249848211961700083651 6193874772317942550125477)
                    ·
                      refine ⟨1161351519809614228148527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6193874772317942550125477 1161351519809614228148527)
                      ·
                        rfl

theorem cell23_2261724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2261724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261724 prefixEnd_2261724 := by exact prefixLift 2261724
  have htrace : WordTrace (prefixWord ++ tailWord_2261724) baseStart_2261724 baseEnd_2261724 := by
    simpa [prefixWord, tailWord_2261724, baseEnd_2261724] using wordTrace_append hprefix tailTrace_2261724
  have hstable : (prefixWord ++ tailWord_2261724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261724).length < 2 ^ (prefixWord ++ tailWord_2261724).sum := by decide
  have hdescent : baseEnd_2261724 < baseStart_2261724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261727 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2261727 : Nat := 118140960795 + 2261727 * 2 ^ 59
def prefixEnd_2261727 : Nat := 4983230072969 + 3 ^ 40 * 2261727 * 2
def baseEnd_2261727 : Nat := 1161353060251577716411013

theorem tailTrace_2261727 : CollatzResearch.WordTrace tailWord_2261727 prefixEnd_2261727 1161353060251577716411013 := by
  unfold tailWord_2261727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82491960677156826064007435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54994640451437884042671623 82491960677156826064007435)
  ·
    refine ⟨123737941015735239096011153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82491960677156826064007435 123737941015735239096011153)
    ·
      refine ⟨92803455761801429322008365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123737941015735239096011153 92803455761801429322008365)
      ·
        refine ⟨34801295910675535995753137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92803455761801429322008365 34801295910675535995753137)
        ·
          refine ⟨26100971933006651996814853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34801295910675535995753137 26100971933006651996814853)
          ·
            refine ⟨4893932237438747249402785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26100971933006651996814853 4893932237438747249402785)
            ·
              refine ⟨3670449178079060437052089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4893932237438747249402785 3670449178079060437052089)
              ·
                refine ⟨2752836883559295327789067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670449178079060437052089 2752836883559295327789067)
                ·
                  refine ⟨4129255325338942991683601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752836883559295327789067 4129255325338942991683601)
                  ·
                    refine ⟨3096941494004207243762701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129255325338942991683601 3096941494004207243762701)
                    ·
                      refine ⟨1161353060251577716411013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096941494004207243762701 1161353060251577716411013)
                      ·
                        rfl

theorem cell23_2261727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2261727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261727 prefixEnd_2261727 := by exact prefixLift 2261727
  have htrace : WordTrace (prefixWord ++ tailWord_2261727) baseStart_2261727 baseEnd_2261727 := by
    simpa [prefixWord, tailWord_2261727, baseEnd_2261727] using wordTrace_append hprefix tailTrace_2261727
  have hstable : (prefixWord ++ tailWord_2261727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261727).length < 2 ^ (prefixWord ++ tailWord_2261727).sum := by decide
  have hdescent : baseEnd_2261727 < baseStart_2261727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261757 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2261757 : Nat := 118140960795 + 2261757 * 2 ^ 59
def prefixEnd_2261757 : Nat := 4983230072969 + 3 ^ 40 * 2261757 * 2
def baseEnd_2261757 : Nat := 1161368464671212599035875

theorem tailTrace_2261757 : CollatzResearch.WordTrace tailWord_2261757 prefixEnd_2261757 1161368464671212599035875 := by
  unfold tailWord_2261757
  simp only [CollatzResearch.WordTrace]
  refine ⟨82493054867048141187599525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54995369911365427458399683 82493054867048141187599525)
  ·
    refine ⟨15467447787571526472674911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82493054867048141187599525 15467447787571526472674911)
    ·
      refine ⟨23201171681357289709012367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467447787571526472674911 23201171681357289709012367)
      ·
        refine ⟨34801757522035934563518551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23201171681357289709012367 34801757522035934563518551)
        ·
          refine ⟨52202636283053901845277827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34801757522035934563518551 52202636283053901845277827)
          ·
            refine ⟨78303954424580852767916741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52202636283053901845277827 78303954424580852767916741)
            ·
              refine ⟨14681991454608909893984389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78303954424580852767916741 14681991454608909893984389)
              ·
                refine ⟨2752873397739170605122073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14681991454608909893984389 2752873397739170605122073)
                ·
                  refine ⟨2064655048304377953841555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2752873397739170605122073 2064655048304377953841555)
                  ·
                    refine ⟨3096982572456566930762333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2064655048304377953841555 3096982572456566930762333)
                    ·
                      refine ⟨1161368464671212599035875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3096982572456566930762333 1161368464671212599035875)
                      ·
                        rfl

theorem cell23_2261757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2261757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261757 prefixEnd_2261757 := by exact prefixLift 2261757
  have htrace : WordTrace (prefixWord ++ tailWord_2261757) baseStart_2261757 baseEnd_2261757 := by
    simpa [prefixWord, tailWord_2261757, baseEnd_2261757] using wordTrace_append hprefix tailTrace_2261757
  have hstable : (prefixWord ++ tailWord_2261757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261757).length < 2 ^ (prefixWord ++ tailWord_2261757).sum := by decide
  have hdescent : baseEnd_2261757 < baseStart_2261757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261763 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2261763 : Nat := 118140960795 + 2261763 * 2 ^ 59
def prefixEnd_2261763 : Nat := 4983230072969 + 3 ^ 40 * 2261763 * 2
def baseEnd_2261763 : Nat := 1161371545555139575560847

theorem tailTrace_2261763 : CollatzResearch.WordTrace tailWord_2261763 prefixEnd_2261763 1161371545555139575560847 := by
  unfold tailWord_2261763
  simp only [CollatzResearch.WordTrace]
  refine ⟨82493273705026404212317943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54995515803350936141545295 82493273705026404212317943)
  ·
    refine ⟨123739910557539606318476915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82493273705026404212317943 123739910557539606318476915)
    ·
      refine ⟨185609865836309409477715373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123739910557539606318476915 185609865836309409477715373)
      ·
        refine ⟨69603699688616028554143265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185609865836309409477715373 69603699688616028554143265)
        ·
          refine ⟨52202774766462021415607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69603699688616028554143265 52202774766462021415607449)
          ·
            refine ⟨39152081074846516061705587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52202774766462021415607449 39152081074846516061705587)
            ·
              refine ⟨58728121612269774092558381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39152081074846516061705587 58728121612269774092558381)
              ·
                refine ⟨22023045604601165284709393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58728121612269774092558381 22023045604601165284709393)
                ·
                  refine ⟨16517284203450873963532045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22023045604601165284709393 16517284203450873963532045)
                  ·
                    refine ⟨6193981576294077736324517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16517284203450873963532045 6193981576294077736324517)
                    ·
                      refine ⟨1161371545555139575560847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6193981576294077736324517 1161371545555139575560847)
                      ·
                        rfl

theorem cell23_2261763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2261763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261763 prefixEnd_2261763 := by exact prefixLift 2261763
  have htrace : WordTrace (prefixWord ++ tailWord_2261763) baseStart_2261763 baseEnd_2261763 := by
    simpa [prefixWord, tailWord_2261763, baseEnd_2261763] using wordTrace_append hprefix tailTrace_2261763
  have hstable : (prefixWord ++ tailWord_2261763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261763).length < 2 ^ (prefixWord ++ tailWord_2261763).sum := by decide
  have hdescent : baseEnd_2261763 < baseStart_2261763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261778 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2261778 : Nat := 118140960795 + 2261778 * 2 ^ 59
def prefixEnd_2261778 : Nat := 4983230072969 + 3 ^ 40 * 2261778 * 2
def baseEnd_2261778 : Nat := 1161379247764957016873279

theorem tailTrace_2261778 : CollatzResearch.WordTrace tailWord_2261778 prefixEnd_2261778 1161379247764957016873279 := by
  unfold tailWord_2261778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623455199993015443528497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54995880533314707849409325 20623455199993015443528497)
  ·
    refine ⟨15467591399994761582646373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623455199993015443528497 15467591399994761582646373)
    ·
      refine ⟨2900173387499017796746195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15467591399994761582646373 2900173387499017796746195)
      ·
        refine ⟨4350260081248526695119293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900173387499017796746195 4350260081248526695119293)
        ·
          refine ⟨1631347530468197510669735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4350260081248526695119293 1631347530468197510669735)
          ·
            refine ⟨2447021295702296266004603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631347530468197510669735 2447021295702296266004603)
            ·
              refine ⟨3670531943553444399006905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447021295702296266004603 3670531943553444399006905)
              ·
                refine ⟨2752898957665083299255179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670531943553444399006905 2752898957665083299255179)
                ·
                  refine ⟨4129348436497624948882769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752898957665083299255179 4129348436497624948882769)
                  ·
                    refine ⟨3097011327373218711662077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129348436497624948882769 3097011327373218711662077)
                    ·
                      refine ⟨1161379247764957016873279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3097011327373218711662077 1161379247764957016873279)
                      ·
                        rfl

theorem cell23_2261778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2261778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261778 prefixEnd_2261778 := by exact prefixLift 2261778
  have htrace : WordTrace (prefixWord ++ tailWord_2261778) baseStart_2261778 baseEnd_2261778 := by
    simpa [prefixWord, tailWord_2261778, baseEnd_2261778] using wordTrace_append hprefix tailTrace_2261778
  have hstable : (prefixWord ++ tailWord_2261778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261778).length < 2 ^ (prefixWord ++ tailWord_2261778).sum := by decide
  have hdescent : baseEnd_2261778 < baseStart_2261778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261797 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_2261797 : Nat := 118140960795 + 2261797 * 2 ^ 59
def prefixEnd_2261797 : Nat := 4983230072969 + 3 ^ 40 * 2261797 * 2
def baseEnd_2261797 : Nat := 1161389003897392442535691

theorem tailTrace_2261797 : CollatzResearch.WordTrace tailWord_2261797 prefixEnd_2261797 1161389003897392442535691 := by
  unfold tailWord_2261797
  simp only [CollatzResearch.WordTrace]
  refine ⟨82494513786903228019055645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54996342524602152012703763 82494513786903228019055645)
  ·
    refine ⟨30935442670088710507145867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82494513786903228019055645 30935442670088710507145867)
    ·
      refine ⟨46403164005133065760718801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30935442670088710507145867 46403164005133065760718801)
      ·
        refine ⟨34802373003849799320539101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46403164005133065760718801 34802373003849799320539101)
        ·
          refine ⟨13050889876443674745202163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34802373003849799320539101 13050889876443674745202163)
          ·
            refine ⟨19576334814665512117803245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050889876443674745202163 19576334814665512117803245)
            ·
              refine ⟨7341125555499567044176217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19576334814665512117803245 7341125555499567044176217)
              ·
                refine ⟨5505844166624675283132163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341125555499567044176217 5505844166624675283132163)
                ·
                  refine ⟨8258766249937012924698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505844166624675283132163 8258766249937012924698245)
                  ·
                    refine ⟨1548518671863189923380921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8258766249937012924698245 1548518671863189923380921)
                    ·
                      refine ⟨1161389003897392442535691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548518671863189923380921 1161389003897392442535691)
                      ·
                        rfl

theorem cell23_2261797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_2261797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261797 prefixEnd_2261797 := by exact prefixLift 2261797
  have htrace : WordTrace (prefixWord ++ tailWord_2261797) baseStart_2261797 baseEnd_2261797 := by
    simpa [prefixWord, tailWord_2261797, baseEnd_2261797] using wordTrace_append hprefix tailTrace_2261797
  have hstable : (prefixWord ++ tailWord_2261797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261797).length < 2 ^ (prefixWord ++ tailWord_2261797).sum := by decide
  have hdescent : baseEnd_2261797 < baseStart_2261797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261800 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2261800 : Nat := 118140960795 + 2261800 * 2 ^ 59
def prefixEnd_2261800 : Nat := 4983230072969 + 3 ^ 40 * 2261800 * 2
def baseEnd_2261800 : Nat := 1161390544339355930798177

theorem tailTrace_2261800 : CollatzResearch.WordTrace tailWord_2261800 prefixEnd_2261800 1161390544339355930798177 := by
  unfold tailWord_2261800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41247311602946179765707427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54996415470594906354276569 41247311602946179765707427)
  ·
    refine ⟨61870967404419269648561141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41247311602946179765707427 61870967404419269648561141)
    ·
      refine ⟨5800403194164306529552607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61870967404419269648561141 5800403194164306529552607)
      ·
        refine ⟨8700604791246459794328911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800403194164306529552607 8700604791246459794328911)
        ·
          refine ⟨13050907186869689691493367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700604791246459794328911 13050907186869689691493367)
          ·
            refine ⟨19576360780304534537240051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050907186869689691493367 19576360780304534537240051)
            ·
              refine ⟨29364541170456801805860077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19576360780304534537240051 29364541170456801805860077)
              ·
                refine ⟨11011702938921300677197529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29364541170456801805860077 11011702938921300677197529)
                ·
                  refine ⟨8258777204190975507898147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11011702938921300677197529 8258777204190975507898147)
                  ·
                    refine ⟨12388165806286463261847221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8258777204190975507898147 12388165806286463261847221)
                    ·
                      refine ⟨1161390544339355930798177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12388165806286463261847221 1161390544339355930798177)
                      ·
                        rfl

theorem cell23_2261800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2261800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261800 prefixEnd_2261800 := by exact prefixLift 2261800
  have htrace : WordTrace (prefixWord ++ tailWord_2261800) baseStart_2261800 baseEnd_2261800 := by
    simpa [prefixWord, tailWord_2261800, baseEnd_2261800] using wordTrace_append hprefix tailTrace_2261800
  have hstable : (prefixWord ++ tailWord_2261800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261800).length < 2 ^ (prefixWord ++ tailWord_2261800).sum := by decide
  have hdescent : baseEnd_2261800 < baseStart_2261800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261810 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2261810 : Nat := 118140960795 + 2261810 * 2 ^ 59
def prefixEnd_2261810 : Nat := 4983230072969 + 3 ^ 40 * 2261810 * 2
def baseEnd_2261810 : Nat := 1161395679145900891673131

theorem tailTrace_2261810 : CollatzResearch.WordTrace tailWord_2261810 prefixEnd_2261810 1161395679145900891673131 := by
  unfold tailWord_2261810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623746983964032809819721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54996658623904087492852589 20623746983964032809819721)
  ·
    refine ⟨15467810237973024607364791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623746983964032809819721 15467810237973024607364791)
    ·
      refine ⟨23201715356959536911047187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467810237973024607364791 23201715356959536911047187)
      ·
        refine ⟨34802573035439305366570781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23201715356959536911047187 34802573035439305366570781)
        ·
          refine ⟨13050964888289739512464043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34802573035439305366570781 13050964888289739512464043)
          ·
            refine ⟨19576447332434609268696065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050964888289739512464043 19576447332434609268696065)
            ·
              refine ⟨14682335499325956951522049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19576447332434609268696065 14682335499325956951522049)
              ·
                refine ⟨11011751624494467713641537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14682335499325956951522049 11011751624494467713641537)
                ·
                  refine ⟨8258813718370850785231153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11011751624494467713641537 8258813718370850785231153)
                  ·
                    refine ⟨6194110288778138088923365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8258813718370850785231153 6194110288778138088923365)
                    ·
                      refine ⟨1161395679145900891673131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6194110288778138088923365 1161395679145900891673131)
                      ·
                        rfl

theorem cell23_2261810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2261810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261810 prefixEnd_2261810 := by exact prefixLift 2261810
  have htrace : WordTrace (prefixWord ++ tailWord_2261810) baseStart_2261810 baseEnd_2261810 := by
    simpa [prefixWord, tailWord_2261810, baseEnd_2261810] using wordTrace_append hprefix tailTrace_2261810
  have hstable : (prefixWord ++ tailWord_2261810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261810).length < 2 ^ (prefixWord ++ tailWord_2261810).sum := by decide
  have hdescent : baseEnd_2261810 < baseStart_2261810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261843 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_2261843 : Nat := 118140960795 + 2261843 * 2 ^ 59
def prefixEnd_2261843 : Nat := 4983230072969 + 3 ^ 40 * 2261843 * 2
def baseEnd_2261843 : Nat := 1161412624007499262560479

theorem tailTrace_2261843 : CollatzResearch.WordTrace tailWord_2261843 prefixEnd_2261843 1161412624007499262560479 := by
  unfold tailWord_2261843
  simp only [CollatzResearch.WordTrace]
  refine ⟨82496191544736577875230183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54997461029824385250153455 82496191544736577875230183)
  ·
    refine ⟨123744287317104866812845275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82496191544736577875230183 123744287317104866812845275)
    ·
      refine ⟨185616430975657300219267913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123744287317104866812845275 185616430975657300219267913)
      ·
        refine ⟨139212323231742975164450935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185616430975657300219267913 139212323231742975164450935)
        ·
          refine ⟨208818484847614462746676403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139212323231742975164450935 208818484847614462746676403)
          ·
            refine ⟨313227727271421694120014605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208818484847614462746676403 313227727271421694120014605)
            ·
              refine ⟨117460397726783135295005477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313227727271421694120014605 117460397726783135295005477)
              ·
                refine ⟨22023824573771837867813527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117460397726783135295005477 22023824573771837867813527)
                ·
                  refine ⟨33035736860657756801720291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22023824573771837867813527 33035736860657756801720291)
                  ·
                    refine ⟨49553605290986635202580437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33035736860657756801720291 49553605290986635202580437)
                    ·
                      refine ⟨1161412624007499262560479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49553605290986635202580437 1161412624007499262560479)
                      ·
                        rfl

theorem cell23_2261843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_2261843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261843 prefixEnd_2261843 := by exact prefixLift 2261843
  have htrace : WordTrace (prefixWord ++ tailWord_2261843) baseStart_2261843 baseEnd_2261843 := by
    simpa [prefixWord, tailWord_2261843, baseEnd_2261843] using wordTrace_append hprefix tailTrace_2261843
  have hstable : (prefixWord ++ tailWord_2261843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261843).length < 2 ^ (prefixWord ++ tailWord_2261843).sum := by decide
  have hdescent : baseEnd_2261843 < baseStart_2261843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261850 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_2261850 : Nat := 118140960795 + 2261850 * 2 ^ 59
def prefixEnd_2261850 : Nat := 4983230072969 + 3 ^ 40 * 2261850 * 2
def baseEnd_2261850 : Nat := 387138739457360245057649

theorem tailTrace_2261850 : CollatzResearch.WordTrace tailWord_2261850 prefixEnd_2261850 387138739457360245057649 := by
  unfold tailWord_2261850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20624111713927804517683751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54997631237140812047156669 20624111713927804517683751)
  ·
    refine ⟨30936167570891706776525627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20624111713927804517683751 30936167570891706776525627)
    ·
      refine ⟨46404251356337560164788441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30936167570891706776525627 46404251356337560164788441)
      ·
        refine ⟨34803188517253170123591331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46404251356337560164788441 34803188517253170123591331)
        ·
          refine ⟨52204782775879755185386997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34803188517253170123591331 52204782775879755185386997)
          ·
            refine ⟨4894198385238727048630031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52204782775879755185386997 4894198385238727048630031)
            ·
              refine ⟨7341297577858090572945047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894198385238727048630031 7341297577858090572945047)
              ·
                refine ⟨11011946366787135859417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7341297577858090572945047 11011946366787135859417571)
                ·
                  refine ⟨16517919550180703789126357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11011946366787135859417571 16517919550180703789126357)
                  ·
                    refine ⟨387138739457360245057649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16517919550180703789126357 387138739457360245057649)
                    ·
                      rfl

theorem cell23_2261850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_2261850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261850 prefixEnd_2261850 := by exact prefixLift 2261850
  have htrace : WordTrace (prefixWord ++ tailWord_2261850) baseStart_2261850 baseEnd_2261850 := by
    simpa [prefixWord, tailWord_2261850, baseEnd_2261850] using wordTrace_append hprefix tailTrace_2261850
  have hstable : (prefixWord ++ tailWord_2261850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261850).length < 2 ^ (prefixWord ++ tailWord_2261850).sum := by decide
  have hdescent : baseEnd_2261850 < baseStart_2261850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261887 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 4, 2]
def baseStart_2261887 : Nat := 118140960795 + 2261887 * 2 ^ 59
def prefixEnd_2261887 : Nat := 4983230072969 + 3 ^ 40 * 2261887 * 2
def baseEnd_2261887 : Nat := 1161435217156297090410277

theorem tailTrace_2261887 : CollatzResearch.WordTrace tailWord_2261887 prefixEnd_2261887 1161435217156297090410277 := by
  unfold tailWord_2261887
  simp only [CollatzResearch.WordTrace]
  refine ⟨82497796356577173389831915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54998530904384782259887943 82497796356577173389831915)
  ·
    refine ⟨123746694534865760084747873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82497796356577173389831915 123746694534865760084747873)
    ·
      refine ⟨92810020901149320063560905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123746694534865760084747873 92810020901149320063560905)
      ·
        refine ⟨69607515675861990047670679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92810020901149320063560905 69607515675861990047670679)
        ·
          refine ⟨104411273513792985071506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69607515675861990047670679 104411273513792985071506019)
          ·
            refine ⟨156616910270689477607259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104411273513792985071506019 156616910270689477607259029)
            ·
              refine ⟨7341417668938569262840267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156616910270689477607259029 7341417668938569262840267)
              ·
                refine ⟨11012126503407853894260401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7341417668938569262840267 11012126503407853894260401)
                ·
                  refine ⟨8259094877555890420695301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11012126503407853894260401 8259094877555890420695301)
                  ·
                    refine ⟨1548580289541729453880369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8259094877555890420695301 1548580289541729453880369)
                    ·
                      refine ⟨1161435217156297090410277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548580289541729453880369 1161435217156297090410277)
                      ·
                        rfl

theorem cell23_2261887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_2261887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261887 prefixEnd_2261887 := by exact prefixLift 2261887
  have htrace : WordTrace (prefixWord ++ tailWord_2261887) baseStart_2261887 baseEnd_2261887 := by
    simpa [prefixWord, tailWord_2261887, baseEnd_2261887] using wordTrace_append hprefix tailTrace_2261887
  have hstable : (prefixWord ++ tailWord_2261887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261887).length < 2 ^ (prefixWord ++ tailWord_2261887).sum := by decide
  have hdescent : baseEnd_2261887 < baseStart_2261887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261897 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_2261897 : Nat := 118140960795 + 2261897 * 2 ^ 59
def prefixEnd_2261897 : Nat := 4983230072969 + 3 ^ 40 * 2261897 * 2
def baseEnd_2261897 : Nat := 387146783987614017095077

theorem tailTrace_2261897 : CollatzResearch.WordTrace tailWord_2261897 prefixEnd_2261897 387146783987614017095077 := by
  unfold tailWord_2261897
  simp only [CollatzResearch.WordTrace]
  refine ⟨82498161086540945097695945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54998774057693963398463963 82498161086540945097695945)
  ·
    refine ⟨61873620814905708823271959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82498161086540945097695945 61873620814905708823271959)
    ·
      refine ⟨92810431222358563234907939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61873620814905708823271959 92810431222358563234907939)
      ·
        refine ⟨139215646833537844852361909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92810431222358563234907939 139215646833537844852361909)
        ·
          refine ⟨13051466890644172954908929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139215646833537844852361909 13051466890644172954908929)
          ·
            refine ⟨9788600167983129716181697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051466890644172954908929 9788600167983129716181697)
            ·
              refine ⟨7341450125987347287136273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9788600167983129716181697 7341450125987347287136273)
              ·
                refine ⟨5506087594490510465352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341450125987347287136273 5506087594490510465352205)
                ·
                  refine ⟨2064782847933941424507077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5506087594490510465352205 2064782847933941424507077)
                  ·
                    refine ⟨387146783987614017095077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2064782847933941424507077 387146783987614017095077)
                    ·
                      rfl

theorem cell23_2261897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_2261897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261897 prefixEnd_2261897 := by exact prefixLift 2261897
  have htrace : WordTrace (prefixWord ++ tailWord_2261897) baseStart_2261897 baseEnd_2261897 := by
    simpa [prefixWord, tailWord_2261897, baseEnd_2261897] using wordTrace_append hprefix tailTrace_2261897
  have hstable : (prefixWord ++ tailWord_2261897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261897).length < 2 ^ (prefixWord ++ tailWord_2261897).sum := by decide
  have hdescent : baseEnd_2261897 < baseStart_2261897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261944 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 6]
def baseStart_2261944 : Nat := 118140960795 + 2261944 * 2 ^ 59
def prefixEnd_2261944 : Nat := 4983230072969 + 3 ^ 40 * 2261944 * 2
def baseEnd_2261944 : Nat := 129051609505955929710835

theorem tailTrace_2261944 : CollatzResearch.WordTrace tailWord_2261944 prefixEnd_2261944 129051609505955929710835 := by
  unfold tailWord_2261944
  simp only [CollatzResearch.WordTrace]
  refine ⟨41249937658685336062328443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54999916878247114749771257 41249937658685336062328443)
  ·
    refine ⟨61874906488028004093492665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41249937658685336062328443 61874906488028004093492665)
    ·
      refine ⟨46406179866021003070119499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61874906488028004093492665 46406179866021003070119499)
      ·
        refine ⟨69609269799031504605179249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46406179866021003070119499 69609269799031504605179249)
        ·
          refine ⟨52206952349273628453884437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69609269799031504605179249 52206952349273628453884437)
          ·
            refine ⟨2447200891372201333775833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52206952349273628453884437 2447200891372201333775833)
            ·
              refine ⟨1835400668529151000331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447200891372201333775833 1835400668529151000331875)
              ·
                refine ⟨2753101002793726500497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835400668529151000331875 2753101002793726500497813)
                ·
                  refine ⟨129051609505955929710835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2753101002793726500497813 129051609505955929710835)
                  ·
                    rfl

theorem cell23_2261944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_2261944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261944 prefixEnd_2261944 := by exact prefixLift 2261944
  have htrace : WordTrace (prefixWord ++ tailWord_2261944) baseStart_2261944 baseEnd_2261944 := by
    simpa [prefixWord, tailWord_2261944, baseEnd_2261944] using wordTrace_append hprefix tailTrace_2261944
  have hstable : (prefixWord ++ tailWord_2261944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261944).length < 2 ^ (prefixWord ++ tailWord_2261944).sum := by decide
  have hdescent : baseEnd_2261944 < baseStart_2261944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261981 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_2261981 : Nat := 118140960795 + 2261981 * 2 ^ 59
def prefixEnd_2261981 : Nat := 4983230072969 + 3 ^ 40 * 2261981 * 2
def baseEnd_2261981 : Nat := 1161483484337819722634845

theorem tailTrace_2261981 : CollatzResearch.WordTrace tailWord_2261981 prefixEnd_2261981 1161483484337819722634845 := by
  unfold tailWord_2261981
  simp only [CollatzResearch.WordTrace]
  refine ⟨82501224818236627443753797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55000816545491084962502531 82501224818236627443753797)
  ·
    refine ⟨15468979653419367645703837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82501224818236627443753797 15468979653419367645703837)
    ·
      refine ⟨5800867370032262867138939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15468979653419367645703837 5800867370032262867138939)
      ·
        refine ⟨8701301055048394300708409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800867370032262867138939 8701301055048394300708409)
        ·
          refine ⟨6525975791286295725531307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701301055048394300708409 6525975791286295725531307)
          ·
            refine ⟨9788963686929443588296961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525975791286295725531307 9788963686929443588296961)
            ·
              refine ⟨7341722765197082691222721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9788963686929443588296961 7341722765197082691222721)
              ·
                refine ⟨5506292073897812018417041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341722765197082691222721 5506292073897812018417041)
                ·
                  refine ⟨4129719055423359013812781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506292073897812018417041 4129719055423359013812781)
                  ·
                    refine ⟨1548644645783759630179793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4129719055423359013812781 1548644645783759630179793)
                    ·
                      refine ⟨1161483484337819722634845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548644645783759630179793 1161483484337819722634845)
                      ·
                        rfl

theorem cell23_2261981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_2261981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2261981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2261981 prefixEnd_2261981 := by exact prefixLift 2261981
  have htrace : WordTrace (prefixWord ++ tailWord_2261981) baseStart_2261981 baseEnd_2261981 := by
    simpa [prefixWord, tailWord_2261981, baseEnd_2261981] using wordTrace_append hprefix tailTrace_2261981
  have hstable : (prefixWord ++ tailWord_2261981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261981).length < 2 ^ (prefixWord ++ tailWord_2261981).sum := by decide
  have hdescent : baseEnd_2261981 < baseStart_2261981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_2262010 : Nat := 118140960795 + 2262010 * 2 ^ 59
def prefixEnd_2262010 : Nat := 4983230072969 + 3 ^ 40 * 2262010 * 2
def baseEnd_2262010 : Nat := 1161498375276800109172211

theorem tailTrace_2262010 : CollatzResearch.WordTrace tailWord_2262010 prefixEnd_2262010 1161498375276800109172211 := by
  unfold tailWord_2262010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625570633782891349139871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55001521690087710264372989 20625570633782891349139871)
  ·
    refine ⟨30938355950674337023709807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20625570633782891349139871 30938355950674337023709807)
    ·
      refine ⟨46407533926011505535564711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30938355950674337023709807 46407533926011505535564711)
      ·
        refine ⟨69611300889017258303347067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46407533926011505535564711 69611300889017258303347067)
        ·
          refine ⟨104416951333525887455020601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69611300889017258303347067 104416951333525887455020601)
          ·
            refine ⟨78312713500144415591265451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104416951333525887455020601 78312713500144415591265451)
            ·
              refine ⟨117469070250216623386898177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78312713500144415591265451 117469070250216623386898177)
              ·
                refine ⟨88101802687662467540173633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117469070250216623386898177 88101802687662467540173633)
                ·
                  refine ⟨66076352015746850655130225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88101802687662467540173633 66076352015746850655130225)
                  ·
                    refine ⟨49557264011810137991347669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66076352015746850655130225 49557264011810137991347669)
                    ·
                      refine ⟨1161498375276800109172211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49557264011810137991347669 1161498375276800109172211)
                      ·
                        rfl

theorem cell23_2262010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_2262010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262010 prefixEnd_2262010 := by exact prefixLift 2262010
  have htrace : WordTrace (prefixWord ++ tailWord_2262010) baseStart_2262010 baseEnd_2262010 := by
    simpa [prefixWord, tailWord_2262010, baseEnd_2262010] using wordTrace_append hprefix tailTrace_2262010
  have hstable : (prefixWord ++ tailWord_2262010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262010).length < 2 ^ (prefixWord ++ tailWord_2262010).sum := by decide
  have hdescent : baseEnd_2262010 < baseStart_2262010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262028 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_2262028 : Nat := 118140960795 + 2262028 * 2 ^ 59
def prefixEnd_2262028 : Nat := 4983230072969 + 3 ^ 40 * 2262028 * 2
def baseEnd_2262028 : Nat := 1161507617928581038747129

theorem tailTrace_2262028 : CollatzResearch.WordTrace tailWord_2262028 prefixEnd_2262028 1161507617928581038747129 := by
  unfold tailWord_2262028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251469524533177235357369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55001959366044236313809825 41251469524533177235357369)
  ·
    refine ⟨30938602143399882926518027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41251469524533177235357369 30938602143399882926518027)
    ·
      refine ⟨46407903215099824389777041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30938602143399882926518027 46407903215099824389777041)
      ·
        refine ⟨34805927411324868292332781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46407903215099824389777041 34805927411324868292332781)
        ·
          refine ⟨13052222779246825609624793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34805927411324868292332781 13052222779246825609624793)
          ·
            refine ⟨9789167084435119207218595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13052222779246825609624793 9789167084435119207218595)
            ·
              refine ⟨14683750626652678810827893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789167084435119207218595 14683750626652678810827893)
              ·
                refine ⟨1376601621248688638515115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14683750626652678810827893 1376601621248688638515115)
                ·
                  refine ⟨2064902431873032957772673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376601621248688638515115 2064902431873032957772673)
                  ·
                    refine ⟨1548676823904774718329505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064902431873032957772673 1548676823904774718329505)
                    ·
                      refine ⟨1161507617928581038747129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548676823904774718329505 1161507617928581038747129)
                      ·
                        rfl

theorem cell23_2262028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_2262028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262028 prefixEnd_2262028 := by exact prefixLift 2262028
  have htrace : WordTrace (prefixWord ++ tailWord_2262028) baseStart_2262028 baseEnd_2262028 := by
    simpa [prefixWord, tailWord_2262028, baseEnd_2262028] using wordTrace_append hprefix tailTrace_2262028
  have hstable : (prefixWord ++ tailWord_2262028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262028).length < 2 ^ (prefixWord ++ tailWord_2262028).sum := by decide
  have hdescent : baseEnd_2262028 < baseStart_2262028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262058 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2262058 : Nat := 118140960795 + 2262058 * 2 ^ 59
def prefixEnd_2262058 : Nat := 4983230072969 + 3 ^ 40 * 2262058 * 2
def baseEnd_2262058 : Nat := 1161523022348215921371991

theorem tailTrace_2262058 : CollatzResearch.WordTrace tailWord_2262058 prefixEnd_2262058 1161523022348215921371991 := by
  unfold tailWord_2262058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626008309739417398576707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55002688825971779729537885 20626008309739417398576707)
  ·
    refine ⟨30939012464609126097865061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20626008309739417398576707 30939012464609126097865061)
    ·
      refine ⟨5801064837114211143349699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30939012464609126097865061 5801064837114211143349699)
      ·
        refine ⟨8701597255671316715024549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801064837114211143349699 8701597255671316715024549)
        ·
          refine ⟨1631549485438371884067103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8701597255671316715024549 1631549485438371884067103)
          ·
            refine ⟨2447324228157557826100655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631549485438371884067103 2447324228157557826100655)
            ·
              refine ⟨3670986342236336739150983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447324228157557826100655 3670986342236336739150983)
              ·
                refine ⟨5506479513354505108726475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670986342236336739150983 5506479513354505108726475)
                ·
                  refine ⟨8259719270031757663089713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5506479513354505108726475 8259719270031757663089713)
                  ·
                    refine ⟨6194789452523818247317285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8259719270031757663089713 6194789452523818247317285)
                    ·
                      refine ⟨1161523022348215921371991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6194789452523818247317285 1161523022348215921371991)
                      ·
                        rfl

theorem cell23_2262058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2262058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262058 prefixEnd_2262058 := by exact prefixLift 2262058
  have htrace : WordTrace (prefixWord ++ tailWord_2262058) baseStart_2262058 baseEnd_2262058 := by
    simpa [prefixWord, tailWord_2262058, baseEnd_2262058] using wordTrace_append hprefix tailTrace_2262058
  have hstable : (prefixWord ++ tailWord_2262058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262058).length < 2 ^ (prefixWord ++ tailWord_2262058).sum := by decide
  have hdescent : baseEnd_2262058 < baseStart_2262058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262087 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2262087 : Nat := 118140960795 + 2262087 * 2 ^ 59
def prefixEnd_2262087 : Nat := 4983230072969 + 3 ^ 40 * 2262087 * 2
def baseEnd_2262087 : Nat := 1161537913287196307909357

theorem tailTrace_2262087 : CollatzResearch.WordTrace tailWord_2262087 prefixEnd_2262087 1161537913287196307909357 := by
  unfold tailWord_2262087
  simp only [CollatzResearch.WordTrace]
  refine ⟨82505090955852607547112515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55003393970568405031408343 82505090955852607547112515)
  ·
    refine ⟨123757636433778911320668773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82505090955852607547112515 123757636433778911320668773)
    ·
      refine ⟨23204556831333545872625395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123757636433778911320668773 23204556831333545872625395)
      ·
        refine ⟨34806835247000318808938093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23204556831333545872625395 34806835247000318808938093)
        ·
          refine ⟨13052563217625119553351785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34806835247000318808938093 13052563217625119553351785)
          ·
            refine ⟨9789422413218839665013839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13052563217625119553351785 9789422413218839665013839)
            ·
              refine ⟨14684133619828259497520759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789422413218839665013839 14684133619828259497520759)
              ·
                refine ⟨22026200429742389246281139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14684133619828259497520759 22026200429742389246281139)
                ·
                  refine ⟨33039300644613583869421709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22026200429742389246281139 33039300644613583869421709)
                  ·
                    refine ⟨12389737741730093951033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33039300644613583869421709 12389737741730093951033141)
                    ·
                      refine ⟨1161537913287196307909357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12389737741730093951033141 1161537913287196307909357)
                      ·
                        rfl

theorem cell23_2262087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2262087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262087 prefixEnd_2262087 := by exact prefixLift 2262087
  have htrace : WordTrace (prefixWord ++ tailWord_2262087) baseStart_2262087 baseEnd_2262087 := by
    simpa [prefixWord, tailWord_2262087, baseEnd_2262087] using wordTrace_append hprefix tailTrace_2262087
  have hstable : (prefixWord ++ tailWord_2262087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262087).length < 2 ^ (prefixWord ++ tailWord_2262087).sum := by decide
  have hdescent : baseEnd_2262087 < baseStart_2262087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262097 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_2262097 : Nat := 118140960795 + 2262097 * 2 ^ 59
def prefixEnd_2262097 : Nat := 4983230072969 + 3 ^ 40 * 2262097 * 2
def baseEnd_2262097 : Nat := 1161543048093741268784311

theorem tailTrace_2262097 : CollatzResearch.WordTrace tailWord_2262097 prefixEnd_2262097 1161543048093741268784311 := by
  unfold tailWord_2262097
  simp only [CollatzResearch.WordTrace]
  refine ⟨82505455685816379254976545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55003637123877586169984363 82505455685816379254976545)
  ·
    refine ⟨61879091764362284441232409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82505455685816379254976545 61879091764362284441232409)
    ·
      refine ⟨46409318823271713330924307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61879091764362284441232409 46409318823271713330924307)
      ·
        refine ⟨69613978234907569996386461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46409318823271713330924307 69613978234907569996386461)
        ·
          refine ⟨26105241838090338748644923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69613978234907569996386461 26105241838090338748644923)
          ·
            refine ⟨39157862757135508122967385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26105241838090338748644923 39157862757135508122967385)
            ·
              refine ⟨29368397067851631092225539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39157862757135508122967385 29368397067851631092225539)
              ·
                refine ⟨44052595601777446638338309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29368397067851631092225539 44052595601777446638338309)
                ·
                  refine ⟨8259861675333271244688433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44052595601777446638338309 8259861675333271244688433)
                  ·
                    refine ⟨6194896256499953433516325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8259861675333271244688433 6194896256499953433516325)
                    ·
                      refine ⟨1161543048093741268784311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6194896256499953433516325 1161543048093741268784311)
                      ·
                        rfl

theorem cell23_2262097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_2262097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262097 prefixEnd_2262097 := by exact prefixLift 2262097
  have htrace : WordTrace (prefixWord ++ tailWord_2262097) baseStart_2262097 baseEnd_2262097 := by
    simpa [prefixWord, tailWord_2262097, baseEnd_2262097] using wordTrace_append hprefix tailTrace_2262097
  have hstable : (prefixWord ++ tailWord_2262097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262097).length < 2 ^ (prefixWord ++ tailWord_2262097).sum := by decide
  have hdescent : baseEnd_2262097 < baseStart_2262097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262101 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2262101 : Nat := 118140960795 + 2262101 * 2 ^ 59
def prefixEnd_2262101 : Nat := 4983230072969 + 3 ^ 40 * 2262101 * 2
def baseEnd_2262101 : Nat := 1161545102016359253134293

theorem tailTrace_2262101 : CollatzResearch.WordTrace tailWord_2262101 prefixEnd_2262101 1161545102016359253134293 := by
  unfold tailWord_2262101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82505601577801887938122157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55003734385201258625414771 82505601577801887938122157)
  ·
    refine ⟨30939600591675707976795809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82505601577801887938122157 30939600591675707976795809)
    ·
      refine ⟨23204700443756780982596857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30939600591675707976795809 23204700443756780982596857)
      ·
        refine ⟨17403525332817585736947643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23204700443756780982596857 17403525332817585736947643)
        ·
          refine ⟨26105287999226378605421465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17403525332817585736947643 26105287999226378605421465)
          ·
            refine ⟨19578965999419783954066099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26105287999226378605421465 19578965999419783954066099)
            ·
              refine ⟨29368448999129675931099149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19578965999419783954066099 29368448999129675931099149)
              ·
                refine ⟨11013168374673628474162181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29368448999129675931099149 11013168374673628474162181)
                ·
                  refine ⟨2064969070251305338905409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11013168374673628474162181 2064969070251305338905409)
                  ·
                    refine ⟨1548726802688479004179057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064969070251305338905409 1548726802688479004179057)
                    ·
                      refine ⟨1161545102016359253134293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548726802688479004179057 1161545102016359253134293)
                      ·
                        rfl

theorem cell23_2262101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2262101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262101 prefixEnd_2262101 := by exact prefixLift 2262101
  have htrace : WordTrace (prefixWord ++ tailWord_2262101) baseStart_2262101 baseEnd_2262101 := by
    simpa [prefixWord, tailWord_2262101, baseEnd_2262101] using wordTrace_append hprefix tailTrace_2262101
  have hstable : (prefixWord ++ tailWord_2262101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262101).length < 2 ^ (prefixWord ++ tailWord_2262101).sum := by decide
  have hdescent : baseEnd_2262101 < baseStart_2262101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262147 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2262147 : Nat := 118140960795 + 2262147 * 2 ^ 59
def prefixEnd_2262147 : Nat := 4983230072969 + 3 ^ 40 * 2262147 * 2
def baseEnd_2262147 : Nat := 1161568722126466073159081

theorem tailTrace_2262147 : CollatzResearch.WordTrace tailWord_2262147 prefixEnd_2262147 1161568722126466073159081 := by
  unfold tailWord_2262147
  simp only [CollatzResearch.WordTrace]
  refine ⟨82507279335635237794296695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55004852890423491862864463 82507279335635237794296695)
  ·
    refine ⟨123760919003452856691445043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82507279335635237794296695 123760919003452856691445043)
    ·
      refine ⟨185641378505179285037167565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123760919003452856691445043 185641378505179285037167565)
      ·
        refine ⟨69615516939442231888937837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185641378505179285037167565 69615516939442231888937837)
        ·
          refine ⟨26105818852290836958351689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69615516939442231888937837 26105818852290836958351689)
          ·
            refine ⟨19579364139218127718763767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26105818852290836958351689 19579364139218127718763767)
            ·
              refine ⟨29369046208827191578145651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19579364139218127718763767 29369046208827191578145651)
              ·
                refine ⟨44053569313240787367218477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29369046208827191578145651 44053569313240787367218477)
                ·
                  refine ⟨16520088492465295262706929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44053569313240787367218477 16520088492465295262706929)
                  ·
                    refine ⟨12390066369348971447030197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16520088492465295262706929 12390066369348971447030197)
                    ·
                      refine ⟨1161568722126466073159081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12390066369348971447030197 1161568722126466073159081)
                      ·
                        rfl

theorem cell23_2262147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2262147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262147 prefixEnd_2262147 := by exact prefixLift 2262147
  have htrace : WordTrace (prefixWord ++ tailWord_2262147) baseStart_2262147 baseEnd_2262147 := by
    simpa [prefixWord, tailWord_2262147, baseEnd_2262147] using wordTrace_append hprefix tailTrace_2262147
  have hstable : (prefixWord ++ tailWord_2262147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262147).length < 2 ^ (prefixWord ++ tailWord_2262147).sum := by decide
  have hdescent : baseEnd_2262147 < baseStart_2262147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262154 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_2262154 : Nat := 118140960795 + 2262154 * 2 ^ 59
def prefixEnd_2262154 : Nat := 4983230072969 + 3 ^ 40 * 2262154 * 2
def baseEnd_2262154 : Nat := 387190772163682515257183

theorem tailTrace_2262154 : CollatzResearch.WordTrace tailWord_2262154 prefixEnd_2262154 387190772163682515257183 := by
  unfold tailWord_2262154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626883661652469497450379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55005023097739918659867677 20626883661652469497450379)
  ·
    refine ⟨30940325492478704246175569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20626883661652469497450379 30940325492478704246175569)
    ·
      refine ⟨23205244119359028184631677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30940325492478704246175569 23205244119359028184631677)
      ·
        refine ⟨8701966544759635569236879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23205244119359028184631677 8701966544759635569236879)
        ·
          refine ⟨13052949817139453353855319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8701966544759635569236879 13052949817139453353855319)
          ·
            refine ⟨19579424725709180030782979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13052949817139453353855319 19579424725709180030782979)
            ·
              refine ⟨29369137088563770046174469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19579424725709180030782979 29369137088563770046174469)
              ·
                refine ⟨5506713204105706883657713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29369137088563770046174469 5506713204105706883657713)
                ·
                  refine ⟨4130034903079280162743285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506713204105706883657713 4130034903079280162743285)
                  ·
                    refine ⟨387190772163682515257183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4130034903079280162743285 387190772163682515257183)
                    ·
                      rfl

theorem cell23_2262154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_2262154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262154 prefixEnd_2262154 := by exact prefixLift 2262154
  have htrace : WordTrace (prefixWord ++ tailWord_2262154) baseStart_2262154 baseEnd_2262154 := by
    simpa [prefixWord, tailWord_2262154, baseEnd_2262154] using wordTrace_append hprefix tailTrace_2262154
  have hstable : (prefixWord ++ tailWord_2262154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262154).length < 2 ^ (prefixWord ++ tailWord_2262154).sum := by decide
  have hdescent : baseEnd_2262154 < baseStart_2262154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262158 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_2262158 : Nat := 118140960795 + 2262158 * 2 ^ 59
def prefixEnd_2262158 : Nat := 4983230072969 + 3 ^ 40 * 2262158 * 2
def baseEnd_2262158 : Nat := 129063818934851725569059

theorem tailTrace_2262158 : CollatzResearch.WordTrace tailWord_2262158 prefixEnd_2262158 129063818934851725569059 := by
  unfold tailWord_2262158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313460067324423334118391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55005120359063591115298085 10313460067324423334118391)
  ·
    refine ⟨15470190100986635001177587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10313460067324423334118391 15470190100986635001177587)
    ·
      refine ⟨23205285151479952501766381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15470190100986635001177587 23205285151479952501766381)
      ·
        refine ⟨8701981931804982188162393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23205285151479952501766381 8701981931804982188162393)
        ·
          refine ⟨6526486448853736641121795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701981931804982188162393 6526486448853736641121795)
          ·
            refine ⟨9789729673280604961682693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526486448853736641121795 9789729673280604961682693)
            ·
              refine ⟨1835574313740113430315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9789729673280604961682693 1835574313740113430315505)
              ·
                refine ⟨1376680735305085072736629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835574313740113430315505 1376680735305085072736629)
                ·
                  refine ⟨129063818934851725569059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1376680735305085072736629 129063818934851725569059)
                  ·
                    rfl

theorem cell23_2262158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_2262158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262158 prefixEnd_2262158 := by exact prefixLift 2262158
  have htrace : WordTrace (prefixWord ++ tailWord_2262158) baseStart_2262158 baseEnd_2262158 := by
    simpa [prefixWord, tailWord_2262158, baseEnd_2262158] using wordTrace_append hprefix tailTrace_2262158
  have hstable : (prefixWord ++ tailWord_2262158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262158).length < 2 ^ (prefixWord ++ tailWord_2262158).sum := by decide
  have hdescent : baseEnd_2262158 < baseStart_2262158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262204 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2262204 : Nat := 118140960795 + 2262204 * 2 ^ 59
def prefixEnd_2262204 : Nat := 4983230072969 + 3 ^ 40 * 2262204 * 2
def baseEnd_2262204 : Nat := 1161597990523772350146319

theorem tailTrace_2262204 : CollatzResearch.WordTrace tailWord_2262204 prefixEnd_2262204 1161597990523772350146319 := by
  unfold tailWord_2262204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41254679148214368264560833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55006238864285824352747777 41254679148214368264560833)
  ·
    refine ⟨30941009361160776198420625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41254679148214368264560833 30941009361160776198420625)
    ·
      refine ⟨23205757020870582148815469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30941009361160776198420625 23205757020870582148815469)
      ·
        refine ⟨8702158882826468305805801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23205757020870582148815469 8702158882826468305805801)
        ·
          refine ⟨6526619162119851229354351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8702158882826468305805801 6526619162119851229354351)
          ·
            refine ⟨9789928743179776844031527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526619162119851229354351 9789928743179776844031527)
            ·
              refine ⟨14684893114769665266047291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789928743179776844031527 14684893114769665266047291)
              ·
                refine ⟨22027339672154497899070937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14684893114769665266047291 22027339672154497899070937)
                ·
                  refine ⟨16520504754115873424303203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22027339672154497899070937 16520504754115873424303203)
                  ·
                    refine ⟨24780757131173810136454805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16520504754115873424303203 24780757131173810136454805)
                    ·
                      refine ⟨1161597990523772350146319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24780757131173810136454805 1161597990523772350146319)
                      ·
                        rfl

theorem cell23_2262204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2262204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262204 prefixEnd_2262204 := by exact prefixLift 2262204
  have htrace : WordTrace (prefixWord ++ tailWord_2262204) baseStart_2262204 baseEnd_2262204 := by
    simpa [prefixWord, tailWord_2262204, baseEnd_2262204] using wordTrace_append hprefix tailTrace_2262204
  have hstable : (prefixWord ++ tailWord_2262204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262204).length < 2 ^ (prefixWord ++ tailWord_2262204).sum := by decide
  have hdescent : baseEnd_2262204 < baseStart_2262204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262218 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_2262218 : Nat := 118140960795 + 2262218 * 2 ^ 59
def prefixEnd_2262218 : Nat := 4983230072969 + 3 ^ 40 * 2262218 * 2
def baseEnd_2262218 : Nat := 387201726417645098457085

theorem tailTrace_2262218 : CollatzResearch.WordTrace tailWord_2262218 prefixEnd_2262218 387201726417645098457085 := by
  unfold tailWord_2262218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20627467229594504230032827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55006579278918677946754205 20627467229594504230032827)
  ·
    refine ⟨30941200844391756345049241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20627467229594504230032827 30941200844391756345049241)
    ·
      refine ⟨23205900633293817258786931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30941200844391756345049241 23205900633293817258786931)
      ·
        refine ⟨34808850949940725888180397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23205900633293817258786931 34808850949940725888180397)
        ·
          refine ⟨13053319106227772208067649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34808850949940725888180397 13053319106227772208067649)
          ·
            refine ⟨9789989329670829156050737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13053319106227772208067649 9789989329670829156050737)
            ·
              refine ⟨7342491997253121867038053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9789989329670829156050737 7342491997253121867038053)
              ·
                refine ⟨1376717249484960350069635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7342491997253121867038053 1376717249484960350069635)
                ·
                  refine ⟨2065075874227440525104453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376717249484960350069635 2065075874227440525104453)
                  ·
                    refine ⟨387201726417645098457085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065075874227440525104453 387201726417645098457085)
                    ·
                      rfl

theorem cell23_2262218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_2262218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262218 prefixEnd_2262218 := by exact prefixLift 2262218
  have htrace : WordTrace (prefixWord ++ tailWord_2262218) baseStart_2262218 baseEnd_2262218 := by
    simpa [prefixWord, tailWord_2262218, baseEnd_2262218] using wordTrace_append hprefix tailTrace_2262218
  have hstable : (prefixWord ++ tailWord_2262218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262218).length < 2 ^ (prefixWord ++ tailWord_2262218).sum := by decide
  have hdescent : baseEnd_2262218 < baseStart_2262218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262244 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_2262244 : Nat := 118140960795 + 2262244 * 2 ^ 59
def prefixEnd_2262244 : Nat := 4983230072969 + 3 ^ 40 * 2262244 * 2
def baseEnd_2262244 : Nat := 387206176583317397882045

theorem tailTrace_2262244 : CollatzResearch.WordTrace tailWord_2262244 prefixEnd_2262244 387206176583317397882045 := by
  unfold tailWord_2262244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41255408608141911680288893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55007211477522548907051857 41255408608141911680288893)
  ·
    refine ⟨15470778228053216880108335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41255408608141911680288893 15470778228053216880108335)
    ·
      refine ⟨23206167342079825320162503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15470778228053216880108335 23206167342079825320162503)
      ·
        refine ⟨34809251013119737980243755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23206167342079825320162503 34809251013119737980243755)
        ·
          refine ⟨52213876519679606970365633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34809251013119737980243755 52213876519679606970365633)
          ·
            refine ⟨39160407389759705227774225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52213876519679606970365633 39160407389759705227774225)
            ·
              refine ⟨29370305542319778920830669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39160407389759705227774225 29370305542319778920830669)
              ·
                refine ⟨11013864578369917095311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29370305542319778920830669 11013864578369917095311501)
                ·
                  refine ⟨4130199216888718910741813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11013864578369917095311501 4130199216888718910741813)
                  ·
                    refine ⟨387206176583317397882045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4130199216888718910741813 387206176583317397882045)
                    ·
                      rfl

theorem cell23_2262244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_2262244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262244 prefixEnd_2262244 := by exact prefixLift 2262244
  have htrace : WordTrace (prefixWord ++ tailWord_2262244) baseStart_2262244 baseEnd_2262244 := by
    simpa [prefixWord, tailWord_2262244, baseEnd_2262244] using wordTrace_append hprefix tailTrace_2262244
  have hstable : (prefixWord ++ tailWord_2262244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262244).length < 2 ^ (prefixWord ++ tailWord_2262244).sum := by decide
  have hdescent : baseEnd_2262244 < baseStart_2262244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262251 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 5, 2]
def baseStart_2262251 : Nat := 118140960795 + 2262251 * 2 ^ 59
def prefixEnd_2262251 : Nat := 4983230072969 + 3 ^ 40 * 2262251 * 2
def baseEnd_2262251 : Nat := 1161622124114533666258603

theorem tailTrace_2262251 : CollatzResearch.WordTrace tailWord_2262251 prefixEnd_2262251 1161622124114533666258603 := by
  unfold tailWord_2262251
  simp only [CollatzResearch.WordTrace]
  refine ⟨82511072527258463556082607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55007381684838975704055071 82511072527258463556082607)
  ·
    refine ⟨123766608790887695334123911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82511072527258463556082607 123766608790887695334123911)
    ·
      refine ⟨185649913186331543001185867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123766608790887695334123911 185649913186331543001185867)
      ·
        refine ⟨278474869779497314501778801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185649913186331543001185867 278474869779497314501778801)
        ·
          refine ⟨208856152334622985876334101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278474869779497314501778801 208856152334622985876334101)
          ·
            refine ⟨9790132140685452462953161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 208856152334622985876334101 9790132140685452462953161)
            ·
              refine ⟨7342599105514089347214871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9790132140685452462953161 7342599105514089347214871)
              ·
                refine ⟨11013898658271134020822307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342599105514089347214871 11013898658271134020822307)
                ·
                  refine ⟨16520847987406701031233461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11013898658271134020822307 16520847987406701031233461)
                  ·
                    refine ⟨1548829498819378221678137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16520847987406701031233461 1548829498819378221678137)
                    ·
                      refine ⟨1161622124114533666258603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548829498819378221678137 1161622124114533666258603)
                      ·
                        rfl

theorem cell23_2262251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5, 2].length) (baseStart_2262251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262251 prefixEnd_2262251 := by exact prefixLift 2262251
  have htrace : WordTrace (prefixWord ++ tailWord_2262251) baseStart_2262251 baseEnd_2262251 := by
    simpa [prefixWord, tailWord_2262251, baseEnd_2262251] using wordTrace_append hprefix tailTrace_2262251
  have hstable : (prefixWord ++ tailWord_2262251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262251).length < 2 ^ (prefixWord ++ tailWord_2262251).sum := by decide
  have hdescent : baseEnd_2262251 < baseStart_2262251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262264 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2262264 : Nat := 118140960795 + 2262264 * 2 ^ 59
def prefixEnd_2262264 : Nat := 4983230072969 + 3 ^ 40 * 2262264 * 2
def baseEnd_2262264 : Nat := 1161628799363042115396043

theorem tailTrace_2262264 : CollatzResearch.WordTrace tailWord_2262264 prefixEnd_2262264 1161628799363042115396043 := by
  unfold tailWord_2262264
  simp only [CollatzResearch.WordTrace]
  refine ⟨41255773338105683388152923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55007697784140911184203897 41255773338105683388152923)
  ·
    refine ⟨61883660007158525082229385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41255773338105683388152923 61883660007158525082229385)
    ·
      refine ⟨46412745005368893811672039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61883660007158525082229385 46412745005368893811672039)
      ·
        refine ⟨69619117508053340717508059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46412745005368893811672039 69619117508053340717508059)
        ·
          refine ⟨104428676262080011076262089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69619117508053340717508059 104428676262080011076262089)
          ·
            refine ⟨78321507196560008307196567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104428676262080011076262089 78321507196560008307196567)
            ·
              refine ⟨117482260794840012460794851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78321507196560008307196567 117482260794840012460794851)
              ·
                refine ⟨176223391192260018691192277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117482260794840012460794851 176223391192260018691192277)
                ·
                  refine ⟨4130235731068594188074819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 176223391192260018691192277 4130235731068594188074819)
                  ·
                    refine ⟨6195353596602891282112229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130235731068594188074819 6195353596602891282112229)
                    ·
                      refine ⟨1161628799363042115396043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6195353596602891282112229 1161628799363042115396043)
                      ·
                        rfl

theorem cell23_2262264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2262264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262264 prefixEnd_2262264 := by exact prefixLift 2262264
  have htrace : WordTrace (prefixWord ++ tailWord_2262264) baseStart_2262264 baseEnd_2262264 := by
    simpa [prefixWord, tailWord_2262264, baseEnd_2262264] using wordTrace_append hprefix tailTrace_2262264
  have hstable : (prefixWord ++ tailWord_2262264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262264).length < 2 ^ (prefixWord ++ tailWord_2262264).sum := by decide
  have hdescent : baseEnd_2262264 < baseStart_2262264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262298 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2262298 : Nat := 118140960795 + 2262298 * 2 ^ 59
def prefixEnd_2262298 : Nat := 4983230072969 + 3 ^ 40 * 2262298 * 2
def baseEnd_2262298 : Nat := 1161646257705294982370887

theorem tailTrace_2262298 : CollatzResearch.WordTrace tailWord_2262298 prefixEnd_2262298 1161646257705294982370887 := by
  unfold tailWord_2262298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20628196689522047645760887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55008524505392127055362365 20628196689522047645760887)
  ·
    refine ⟨30942295034283071468641331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20628196689522047645760887 30942295034283071468641331)
    ·
      refine ⟨46413442551424607202961997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30942295034283071468641331 46413442551424607202961997)
      ·
        refine ⟨17405040956784227701110749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46413442551424607202961997 17405040956784227701110749)
        ·
          refine ⟨6526890358794085387916531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17405040956784227701110749 6526890358794085387916531)
          ·
            refine ⟨9790335538191128081874797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526890358794085387916531 9790335538191128081874797)
            ·
              refine ⟨3671375826821673030703049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9790335538191128081874797 3671375826821673030703049)
              ·
                refine ⟨2753531870116254773027287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3671375826821673030703049 2753531870116254773027287)
                ·
                  refine ⟨4130297805174382159540931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753531870116254773027287 4130297805174382159540931)
                  ·
                    refine ⟨6195446707761573239311397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130297805174382159540931 6195446707761573239311397)
                    ·
                      refine ⟨1161646257705294982370887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6195446707761573239311397 1161646257705294982370887)
                      ·
                        rfl

theorem cell23_2262298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2262298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262298 prefixEnd_2262298 := by exact prefixLift 2262298
  have htrace : WordTrace (prefixWord ++ tailWord_2262298) baseStart_2262298 baseEnd_2262298 := by
    simpa [prefixWord, tailWord_2262298, baseEnd_2262298] using wordTrace_append hprefix tailTrace_2262298
  have hstable : (prefixWord ++ tailWord_2262298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262298).length < 2 ^ (prefixWord ++ tailWord_2262298).sum := by decide
  have hdescent : baseEnd_2262298 < baseStart_2262298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262331 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 3]
def baseStart_2262331 : Nat := 118140960795 + 2262331 * 2 ^ 59
def prefixEnd_2262331 : Nat := 4983230072969 + 3 ^ 40 * 2262331 * 2
def baseEnd_2262331 : Nat := 1161663202566893353258235

theorem tailTrace_2262331 : CollatzResearch.WordTrace tailWord_2262331 prefixEnd_2262331 1161663202566893353258235 := by
  unfold tailWord_2262331
  simp only [CollatzResearch.WordTrace]
  refine ⟨82513990366968637218994847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55009326911312424812663231 82513990366968637218994847)
  ·
    refine ⟨123770985550452955828492271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82513990366968637218994847 123770985550452955828492271)
    ·
      refine ⟨185656478325679433742738407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123770985550452955828492271 185656478325679433742738407)
      ·
        refine ⟨278484717488519150614107611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185656478325679433742738407 278484717488519150614107611)
        ·
          refine ⟨417727076232778725921161417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278484717488519150614107611 417727076232778725921161417)
          ·
            refine ⟨313295307174584044440871063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417727076232778725921161417 313295307174584044440871063)
            ·
              refine ⟨469942960761876066661306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313295307174584044440871063 469942960761876066661306595)
              ·
                refine ⟨704914441142814099991959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469942960761876066661306595 704914441142814099991959893)
                ·
                  refine ⟨2065179026785588183570195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 704914441142814099991959893 2065179026785588183570195)
                  ·
                    refine ⟨3097768540178382275355293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065179026785588183570195 3097768540178382275355293)
                    ·
                      refine ⟨1161663202566893353258235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3097768540178382275355293 1161663202566893353258235)
                      ·
                        rfl

theorem cell23_2262331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 3].length) (baseStart_2262331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262331 prefixEnd_2262331 := by exact prefixLift 2262331
  have htrace : WordTrace (prefixWord ++ tailWord_2262331) baseStart_2262331 baseEnd_2262331 := by
    simpa [prefixWord, tailWord_2262331, baseEnd_2262331] using wordTrace_append hprefix tailTrace_2262331
  have hstable : (prefixWord ++ tailWord_2262331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262331).length < 2 ^ (prefixWord ++ tailWord_2262331).sum := by decide
  have hdescent : baseEnd_2262331 < baseStart_2262331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262332 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_2262332 : Nat := 118140960795 + 2262332 * 2 ^ 59
def prefixEnd_2262332 : Nat := 4983230072969 + 3 ^ 40 * 2262332 * 2
def baseEnd_2262332 : Nat := 1161663716047547849345731

theorem tailTrace_2262332 : CollatzResearch.WordTrace tailWord_2262332 prefixEnd_2262332 1161663716047547849345731 := by
  unfold tailWord_2262332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41257013419982507194890625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55009351226643342926520833 41257013419982507194890625)
  ·
    refine ⟨30942760064986880396167969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41257013419982507194890625 30942760064986880396167969)
    ·
      refine ⟨23207070048740160297125977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30942760064986880396167969 23207070048740160297125977)
      ·
        refine ⟨17405302536555120222844483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23207070048740160297125977 17405302536555120222844483)
        ·
          refine ⟨26107953804832680334266725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17405302536555120222844483 26107953804832680334266725)
          ·
            refine ⟨4895241338406127562675011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26107953804832680334266725 4895241338406127562675011)
            ·
              refine ⟨7342862007609191344012517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895241338406127562675011 7342862007609191344012517)
              ·
                refine ⟨1376786626426723377002347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7342862007609191344012517 1376786626426723377002347)
                ·
                  refine ⟨2065179939640085065503521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376786626426723377002347 2065179939640085065503521)
                  ·
                    refine ⟨1548884954730063799127641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2065179939640085065503521 1548884954730063799127641)
                    ·
                      refine ⟨1161663716047547849345731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548884954730063799127641 1161663716047547849345731)
                      ·
                        rfl

theorem cell23_2262332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_2262332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262332 prefixEnd_2262332 := by exact prefixLift 2262332
  have htrace : WordTrace (prefixWord ++ tailWord_2262332) baseStart_2262332 baseEnd_2262332 := by
    simpa [prefixWord, tailWord_2262332, baseEnd_2262332] using wordTrace_append hprefix tailTrace_2262332
  have hstable : (prefixWord ++ tailWord_2262332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262332).length < 2 ^ (prefixWord ++ tailWord_2262332).sum := by decide
  have hdescent : baseEnd_2262332 < baseStart_2262332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262342 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2262342 : Nat := 118140960795 + 2262342 * 2 ^ 59
def prefixEnd_2262342 : Nat := 4983230072969 + 3 ^ 40 * 2262342 * 2
def baseEnd_2262342 : Nat := 387222950284697603406895

theorem tailTrace_2262342 : CollatzResearch.WordTrace tailWord_2262342 prefixEnd_2262342 387222950284697603406895 := by
  unfold tailWord_2262342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578574736560274565551415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55009594379952524065096853 2578574736560274565551415)
  ·
    refine ⟨3867862104840411848327123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2578574736560274565551415 3867862104840411848327123)
    ·
      refine ⟨5801793157260617772490685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867862104840411848327123 5801793157260617772490685)
      ·
        refine ⟨2175672433972731664684007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5801793157260617772490685 2175672433972731664684007)
        ·
          refine ⟨3263508650959097497026011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175672433972731664684007 3263508650959097497026011)
          ·
            refine ⟨4895262976438646245539017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263508650959097497026011 4895262976438646245539017)
            ·
              refine ⟨3671447232328984684154263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895262976438646245539017 3671447232328984684154263)
              ·
                refine ⟨5507170848493477026231395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671447232328984684154263 5507170848493477026231395)
                ·
                  refine ⟨8260756272740215539347093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507170848493477026231395 8260756272740215539347093)
                  ·
                    refine ⟨387222950284697603406895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8260756272740215539347093 387222950284697603406895)
                    ·
                      rfl

theorem cell23_2262342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2262342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262342 prefixEnd_2262342 := by exact prefixLift 2262342
  have htrace : WordTrace (prefixWord ++ tailWord_2262342) baseStart_2262342 baseEnd_2262342 := by
    simpa [prefixWord, tailWord_2262342, baseEnd_2262342] using wordTrace_append hprefix tailTrace_2262342
  have hstable : (prefixWord ++ tailWord_2262342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262342).length < 2 ^ (prefixWord ++ tailWord_2262342).sum := by decide
  have hdescent : baseEnd_2262342 < baseStart_2262342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262344 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2262344 : Nat := 118140960795 + 2262344 * 2 ^ 59
def prefixEnd_2262344 : Nat := 4983230072969 + 3 ^ 40 * 2262344 * 2
def baseEnd_2262344 : Nat := 1161669877815401802395675

theorem tailTrace_2262344 : CollatzResearch.WordTrace tailWord_2262344 prefixEnd_2262344 1161669877815401802395675 := by
  unfold tailWord_2262344
  simp only [CollatzResearch.WordTrace]
  refine ⟨41257232257960770219609043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55009643010614360292812057 41257232257960770219609043)
  ·
    refine ⟨61885848386941155329413565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41257232257960770219609043 61885848386941155329413565)
    ·
      refine ⟨23207193145102933248530087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61885848386941155329413565 23207193145102933248530087)
      ·
        refine ⟨34810789717654399872795131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23207193145102933248530087 34810789717654399872795131)
        ·
          refine ⟨52216184576481599809192697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34810789717654399872795131 52216184576481599809192697)
          ·
            refine ⟨39162138432361199856894523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52216184576481599809192697 39162138432361199856894523)
            ·
              refine ⟨58743207648541799785341785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39162138432361199856894523 58743207648541799785341785)
              ·
                refine ⟨44057405736406349839006339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58743207648541799785341785 44057405736406349839006339)
                ·
                  refine ⟨66086108604609524758509509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44057405736406349839006339 66086108604609524758509509)
                  ·
                    refine ⟨12391145363364285892220533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66086108604609524758509509 12391145363364285892220533)
                    ·
                      refine ⟨1161669877815401802395675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12391145363364285892220533 1161669877815401802395675)
                      ·
                        rfl

theorem cell23_2262344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2262344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262344 prefixEnd_2262344 := by exact prefixLift 2262344
  have htrace : WordTrace (prefixWord ++ tailWord_2262344) baseStart_2262344 baseEnd_2262344 := by
    simpa [prefixWord, tailWord_2262344, baseEnd_2262344] using wordTrace_append hprefix tailTrace_2262344
  have hstable : (prefixWord ++ tailWord_2262344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262344).length < 2 ^ (prefixWord ++ tailWord_2262344).sum := by decide
  have hdescent : baseEnd_2262344 < baseStart_2262344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262348 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2262348 : Nat := 118140960795 + 2262348 * 2 ^ 59
def prefixEnd_2262348 : Nat := 4983230072969 + 3 ^ 40 * 2262348 * 2
def baseEnd_2262348 : Nat := 1161671931738019786745657

theorem tailTrace_2262348 : CollatzResearch.WordTrace tailWord_2262348 prefixEnd_2262348 1161671931738019786745657 := by
  unfold tailWord_2262348
  simp only [CollatzResearch.WordTrace]
  refine ⟨41257305203953524561181849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55009740271938032748242465 41257305203953524561181849)
  ·
    refine ⟨30942978902965143420886387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41257305203953524561181849 30942978902965143420886387)
    ·
      refine ⟨46414468354447715131329581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30942978902965143420886387 46414468354447715131329581)
      ·
        refine ⟨17405425632917893174248593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46414468354447715131329581 17405425632917893174248593)
        ·
          refine ⟨13054069224688419880686445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17405425632917893174248593 13054069224688419880686445)
          ·
            refine ⟨4895275959258157455257417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13054069224688419880686445 4895275959258157455257417)
            ·
              refine ⟨3671456969443618091443063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895275959258157455257417 3671456969443618091443063)
              ·
                refine ⟨5507185454165427137164595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671456969443618091443063 5507185454165427137164595)
                ·
                  refine ⟨8260778181248140705746893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507185454165427137164595 8260778181248140705746893)
                  ·
                    refine ⟨3097791817968052764655085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8260778181248140705746893 3097791817968052764655085)
                    ·
                      refine ⟨1161671931738019786745657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3097791817968052764655085 1161671931738019786745657)
                      ·
                        rfl

theorem cell23_2262348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2262348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262348 prefixEnd_2262348 := by exact prefixLift 2262348
  have htrace : WordTrace (prefixWord ++ tailWord_2262348) baseStart_2262348 baseEnd_2262348 := by
    simpa [prefixWord, tailWord_2262348, baseEnd_2262348] using wordTrace_append hprefix tailTrace_2262348
  have hstable : (prefixWord ++ tailWord_2262348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262348).length < 2 ^ (prefixWord ++ tailWord_2262348).sum := by decide
  have hdescent : baseEnd_2262348 < baseStart_2262348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262349 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2262349 : Nat := 118140960795 + 2262349 * 2 ^ 59
def prefixEnd_2262349 : Nat := 4983230072969 + 3 ^ 40 * 2262349 * 2
def baseEnd_2262349 : Nat := 1161672445218674282833153

theorem tailTrace_2262349 : CollatzResearch.WordTrace tailWord_2262349 prefixEnd_2262349 1161672445218674282833153 := by
  unfold tailWord_2262349
  simp only [CollatzResearch.WordTrace]
  refine ⟨82514646880903426293150101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55009764587268950862100067 82514646880903426293150101)
  ·
    refine ⟨3867874072542348107491411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82514646880903426293150101 3867874072542348107491411)
    ·
      refine ⟨5801811108813522161237117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867874072542348107491411 5801811108813522161237117)
      ·
        refine ⟨2175679165805070810463919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5801811108813522161237117 2175679165805070810463919)
        ·
          refine ⟨3263518748707606215695879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175679165805070810463919 3263518748707606215695879)
          ·
            refine ⟨4895278123061409323543819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263518748707606215695879 4895278123061409323543819)
            ·
              refine ⟨7342917184592113985315729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895278123061409323543819 7342917184592113985315729)
              ·
                refine ⟨5507187888444085488986797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7342917184592113985315729 5507187888444085488986797)
                ·
                  refine ⟨2065195458166532058370049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5507187888444085488986797 2065195458166532058370049)
                  ·
                    refine ⟨1548896593624899043777537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2065195458166532058370049 1548896593624899043777537)
                    ·
                      refine ⟨1161672445218674282833153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548896593624899043777537 1161672445218674282833153)
                      ·
                        rfl

theorem cell23_2262349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2262349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262349 prefixEnd_2262349 := by exact prefixLift 2262349
  have htrace : WordTrace (prefixWord ++ tailWord_2262349) baseStart_2262349 baseEnd_2262349 := by
    simpa [prefixWord, tailWord_2262349, baseEnd_2262349] using wordTrace_append hprefix tailTrace_2262349
  have hstable : (prefixWord ++ tailWord_2262349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262349).length < 2 ^ (prefixWord ++ tailWord_2262349).sum := by decide
  have hdescent : baseEnd_2262349 < baseStart_2262349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262381 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2262381 : Nat := 118140960795 + 2262381 * 2 ^ 59
def prefixEnd_2262381 : Nat := 4983230072969 + 3 ^ 40 * 2262381 * 2
def baseEnd_2262381 : Nat := 387229625533206052544335

theorem tailTrace_2262381 : CollatzResearch.WordTrace tailWord_2262381 prefixEnd_2262381 387229625533206052544335 := by
  unfold tailWord_2262381
  simp only [CollatzResearch.WordTrace]
  refine ⟨82515814016787495758314997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55010542677858330505543331 82515814016787495758314997)
  ·
    refine ⟨7735857564073827727342031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82515814016787495758314997 7735857564073827727342031)
    ·
      refine ⟨11603786346110741591013047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735857564073827727342031 11603786346110741591013047)
      ·
        refine ⟨17405679519166112386519571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11603786346110741591013047 17405679519166112386519571)
        ·
          refine ⟨26108519278749168579779357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17405679519166112386519571 26108519278749168579779357)
          ·
            refine ⟨9790694729530938217417259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26108519278749168579779357 9790694729530938217417259)
            ·
              refine ⟨14686042094296407326125889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9790694729530938217417259 14686042094296407326125889)
              ·
                refine ⟨11014531570722305494594417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14686042094296407326125889 11014531570722305494594417)
                ·
                  refine ⟨8260898678041729120945813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11014531570722305494594417 8260898678041729120945813)
                  ·
                    refine ⟨387229625533206052544335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8260898678041729120945813 387229625533206052544335)
                    ·
                      rfl

theorem cell23_2262381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2262381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262381 prefixEnd_2262381 := by exact prefixLift 2262381
  have htrace : WordTrace (prefixWord ++ tailWord_2262381) baseStart_2262381 baseEnd_2262381 := by
    simpa [prefixWord, tailWord_2262381, baseEnd_2262381] using wordTrace_append hprefix tailTrace_2262381
  have hstable : (prefixWord ++ tailWord_2262381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262381).length < 2 ^ (prefixWord ++ tailWord_2262381).sum := by decide
  have hdescent : baseEnd_2262381 < baseStart_2262381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262382 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2262382 : Nat := 118140960795 + 2262382 * 2 ^ 59
def prefixEnd_2262382 : Nat := 4983230072969 + 3 ^ 40 * 2262382 * 2
def baseEnd_2262382 : Nat := 1161689390080272653720501

theorem tailTrace_2262382 : CollatzResearch.WordTrace tailWord_2262382 prefixEnd_2262382 1161689390080272653720501 := by
  unfold tailWord_2262382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314481311222984116137675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55010566993189248619400933 10314481311222984116137675)
  ·
    refine ⟨15471721966834476174206513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314481311222984116137675 15471721966834476174206513)
    ·
      refine ⟨11603791475125857130654885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15471721966834476174206513 11603791475125857130654885)
      ·
        refine ⟨2175710901586098211997791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11603791475125857130654885 2175710901586098211997791)
        ·
          refine ⟨3263566352379147317996687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175710901586098211997791 3263566352379147317996687)
          ·
            refine ⟨4895349528568720976995031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263566352379147317996687 4895349528568720976995031)
            ·
              refine ⟨7343024292853081465492547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895349528568720976995031 7343024292853081465492547)
              ·
                refine ⟨11014536439279622198238821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7343024292853081465492547 11014536439279622198238821)
                ·
                  refine ⟨2065225582364929162169779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11014536439279622198238821 2065225582364929162169779)
                  ·
                    refine ⟨3097838373547393743254669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065225582364929162169779 3097838373547393743254669)
                    ·
                      refine ⟨1161689390080272653720501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3097838373547393743254669 1161689390080272653720501)
                      ·
                        rfl

theorem cell23_2262382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2262382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262382 prefixEnd_2262382 := by exact prefixLift 2262382
  have htrace : WordTrace (prefixWord ++ tailWord_2262382) baseStart_2262382 baseEnd_2262382 := by
    simpa [prefixWord, tailWord_2262382, baseEnd_2262382] using wordTrace_append hprefix tailTrace_2262382
  have hstable : (prefixWord ++ tailWord_2262382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262382).length < 2 ^ (prefixWord ++ tailWord_2262382).sum := by decide
  have hdescent : baseEnd_2262382 < baseStart_2262382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262394 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_2262394 : Nat := 118140960795 + 2262394 * 2 ^ 59
def prefixEnd_2262394 : Nat := 4983230072969 + 3 ^ 40 * 2262394 * 2
def baseEnd_2262394 : Nat := 129077283538680734085605

theorem tailTrace_2262394 : CollatzResearch.WordTrace tailWord_2262394 prefixEnd_2262394 129077283538680734085605 := by
  unfold tailWord_2262394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20629072041435099744634559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55010858777160265985692157 20629072041435099744634559)
  ·
    refine ⟨30943608062152649616951839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20629072041435099744634559 30943608062152649616951839)
    ·
      refine ⟨46415412093228974425427759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30943608062152649616951839 46415412093228974425427759)
      ·
        refine ⟨69623118139843461638141639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46415412093228974425427759 69623118139843461638141639)
        ·
          refine ⟨104434677209765192457212459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69623118139843461638141639 104434677209765192457212459)
          ·
            refine ⟨156652015814647788685818689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104434677209765192457212459 156652015814647788685818689)
            ·
              refine ⟨117489011860985841514364017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156652015814647788685818689 117489011860985841514364017)
              ·
                refine ⟨88116758895739381135773013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117489011860985841514364017 88116758895739381135773013)
                ·
                  refine ⟨129077283538680734085605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 88116758895739381135773013 129077283538680734085605)
                  ·
                    rfl

theorem cell23_2262394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_2262394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262394 prefixEnd_2262394 := by exact prefixLift 2262394
  have htrace : WordTrace (prefixWord ++ tailWord_2262394) baseStart_2262394 baseEnd_2262394 := by
    simpa [prefixWord, tailWord_2262394, baseEnd_2262394] using wordTrace_append hprefix tailTrace_2262394
  have hstable : (prefixWord ++ tailWord_2262394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262394).length < 2 ^ (prefixWord ++ tailWord_2262394).sum := by decide
  have hdescent : baseEnd_2262394 < baseStart_2262394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262405 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_2262405 : Nat := 118140960795 + 2262405 * 2 ^ 59
def prefixEnd_2262405 : Nat := 4983230072969 + 3 ^ 40 * 2262405 * 2
def baseEnd_2262405 : Nat := 1161701200135326063732895

theorem tailTrace_2262405 : CollatzResearch.WordTrace tailWord_2262405 prefixEnd_2262405 1161701200135326063732895 := by
  unfold tailWord_2262405
  simp only [CollatzResearch.WordTrace]
  refine ⟨82516689368700547857188669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55011126245800365238125779 82516689368700547857188669)
  ·
    refine ⟨30943758513262705446445751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82516689368700547857188669 30943758513262705446445751)
    ·
      refine ⟨46415637769894058169668627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30943758513262705446445751 46415637769894058169668627)
      ·
        refine ⟨69623456654841087254502941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46415637769894058169668627 69623456654841087254502941)
        ·
          refine ⟨26108796245565407720438603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69623456654841087254502941 26108796245565407720438603)
          ·
            refine ⟨39163194368348111580657905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26108796245565407720438603 39163194368348111580657905)
            ·
              refine ⟨29372395776261083685493429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39163194368348111580657905 29372395776261083685493429)
              ·
                refine ⟨2753662104024476595515009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29372395776261083685493429 2753662104024476595515009)
                ·
                  refine ⟨2065246578018357446636257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753662104024476595515009 2065246578018357446636257)
                  ·
                    refine ⟨1548934933513768084977193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2065246578018357446636257 1548934933513768084977193)
                    ·
                      refine ⟨1161701200135326063732895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1548934933513768084977193 1161701200135326063732895)
                      ·
                        rfl

theorem cell23_2262405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_2262405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262405 prefixEnd_2262405 := by exact prefixLift 2262405
  have htrace : WordTrace (prefixWord ++ tailWord_2262405) baseStart_2262405 baseEnd_2262405 := by
    simpa [prefixWord, tailWord_2262405, baseEnd_2262405] using wordTrace_append hprefix tailTrace_2262405
  have hstable : (prefixWord ++ tailWord_2262405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262405).length < 2 ^ (prefixWord ++ tailWord_2262405).sum := by decide
  have hdescent : baseEnd_2262405 < baseStart_2262405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262421 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_2262421 : Nat := 118140960795 + 2262421 * 2 ^ 59
def prefixEnd_2262421 : Nat := 4983230072969 + 3 ^ 40 * 2262421 * 2
def baseEnd_2262421 : Nat := 1161709415825798001132821

theorem tailTrace_2262421 : CollatzResearch.WordTrace tailWord_2262421 prefixEnd_2262421 1161709415825798001132821 := by
  unfold tailWord_2262421
  simp only [CollatzResearch.WordTrace]
  refine ⟨82517272936642582589771117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55011515291095055059847411 82517272936642582589771117)
  ·
    refine ⟨30943977351240968471164169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82517272936642582589771117 30943977351240968471164169)
    ·
      refine ⟨23207983013430726353373127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30943977351240968471164169 23207983013430726353373127)
      ·
        refine ⟨34811974520146089530059691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23207983013430726353373127 34811974520146089530059691)
        ·
          refine ⟨52217961780219134295089537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34811974520146089530059691 52217961780219134295089537)
          ·
            refine ⟨39163471335164350721317153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52217961780219134295089537 39163471335164350721317153)
            ·
              refine ⟨29372603501373263040987865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39163471335164350721317153 29372603501373263040987865)
              ·
                refine ⟨22029452626029947280740899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29372603501373263040987865 22029452626029947280740899)
                ·
                  refine ⟨33044178939044920921111349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22029452626029947280740899 33044178939044920921111349)
                  ·
                    refine ⟨3097891775535461336354189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33044178939044920921111349 3097891775535461336354189)
                    ·
                      refine ⟨1161709415825798001132821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3097891775535461336354189 1161709415825798001132821)
                      ·
                        rfl

theorem cell23_2262421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_2262421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262421 prefixEnd_2262421 := by exact prefixLift 2262421
  have htrace : WordTrace (prefixWord ++ tailWord_2262421) baseStart_2262421 baseEnd_2262421 := by
    simpa [prefixWord, tailWord_2262421, baseEnd_2262421] using wordTrace_append hprefix tailTrace_2262421
  have hstable : (prefixWord ++ tailWord_2262421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262421).length < 2 ^ (prefixWord ++ tailWord_2262421).sum := by decide
  have hdescent : baseEnd_2262421 < baseStart_2262421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262445 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2262445 : Nat := 118140960795 + 2262445 * 2 ^ 59
def prefixEnd_2262445 : Nat := 4983230072969 + 3 ^ 40 * 2262445 * 2
def baseEnd_2262445 : Nat := 129080193262389545248079

theorem tailTrace_2262445 : CollatzResearch.WordTrace tailWord_2262445 prefixEnd_2262445 129080193262389545248079 := by
  unfold tailWord_2262445
  simp only [CollatzResearch.WordTrace]
  refine ⟨82518148288555634688644789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55012098859037089792429859 82518148288555634688644789)
  ·
    refine ⟨7736076402052090752060449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82518148288555634688644789 7736076402052090752060449)
    ·
      refine ⟨5802057301539068064045337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7736076402052090752060449 5802057301539068064045337)
      ·
        refine ⟨4351542976154301048034003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5802057301539068064045337 4351542976154301048034003)
        ·
          refine ⟨6527314464231451572051005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351542976154301048034003 6527314464231451572051005)
          ·
            refine ⟨2447742924086794339519127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6527314464231451572051005 2447742924086794339519127)
            ·
              refine ⟨3671614386130191509278691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447742924086794339519127 3671614386130191509278691)
              ·
                refine ⟨5507421579195287263918037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671614386130191509278691 5507421579195287263918037)
                ·
                  refine ⟨129080193262389545248079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5507421579195287263918037 129080193262389545248079)
                  ·
                    rfl

theorem cell23_2262445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2262445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262445 prefixEnd_2262445 := by exact prefixLift 2262445
  have htrace : WordTrace (prefixWord ++ tailWord_2262445) baseStart_2262445 baseEnd_2262445 := by
    simpa [prefixWord, tailWord_2262445, baseEnd_2262445] using wordTrace_append hprefix tailTrace_2262445
  have hstable : (prefixWord ++ tailWord_2262445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262445).length < 2 ^ (prefixWord ++ tailWord_2262445).sum := by decide
  have hdescent : baseEnd_2262445 < baseStart_2262445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262478 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2262478 : Nat := 118140960795 + 2262478 * 2 ^ 59
def prefixEnd_2262478 : Nat := 4983230072969 + 3 ^ 40 * 2262478 * 2
def baseEnd_2262478 : Nat := 1161738684223104278120059

theorem tailTrace_2262478 : CollatzResearch.WordTrace tailWord_2262478 prefixEnd_2262478 1161738684223104278120059 := by
  unfold tailWord_2262478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314918987179510165574511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55012901264957387549730725 10314918987179510165574511)
  ·
    refine ⟨15472378480769265248361767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314918987179510165574511 15472378480769265248361767)
    ·
      refine ⟨23208567721153897872542651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15472378480769265248361767 23208567721153897872542651)
      ·
        refine ⟨34812851581730846808813977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23208567721153897872542651 34812851581730846808813977)
        ·
          refine ⟨26109638686298135106610483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34812851581730846808813977 26109638686298135106610483)
          ·
            refine ⟨39164458029447202659915725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26109638686298135106610483 39164458029447202659915725)
            ·
              refine ⟨14686671761042700997468397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39164458029447202659915725 14686671761042700997468397)
              ·
                refine ⟨5507501910391012874050649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14686671761042700997468397 5507501910391012874050649)
                ·
                  refine ⟨4130626432793259655537987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5507501910391012874050649 4130626432793259655537987)
                  ·
                    refine ⟨6195939649189889483306981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130626432793259655537987 6195939649189889483306981)
                    ·
                      refine ⟨1161738684223104278120059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6195939649189889483306981 1161738684223104278120059)
                      ·
                        rfl

theorem cell23_2262478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2262478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262478 prefixEnd_2262478 := by exact prefixLift 2262478
  have htrace : WordTrace (prefixWord ++ tailWord_2262478) baseStart_2262478 baseEnd_2262478 := by
    simpa [prefixWord, tailWord_2262478, baseEnd_2262478] using wordTrace_append hprefix tailTrace_2262478
  have hstable : (prefixWord ++ tailWord_2262478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262478).length < 2 ^ (prefixWord ++ tailWord_2262478).sum := by decide
  have hdescent : baseEnd_2262478 < baseStart_2262478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262552 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 6]
def baseStart_2262552 : Nat := 118140960795 + 2262552 * 2 ^ 59
def prefixEnd_2262552 : Nat := 4983230072969 + 3 ^ 40 * 2262552 * 2
def baseEnd_2262552 : Nat := 129086297976837443177191

theorem tailTrace_2262552 : CollatzResearch.WordTrace tailWord_2262552 prefixEnd_2262552 129086297976837443177191 := by
  unfold tailWord_2262552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41261025449583995981394955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55014700599445327975193273 41261025449583995981394955)
  ·
    refine ⟨61891538174375993972092433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41261025449583995981394955 61891538174375993972092433)
    ·
      refine ⟨46418653630781995479069325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61891538174375993972092433 46418653630781995479069325)
      ·
        refine ⟨17406995111543248304650997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46418653630781995479069325 17406995111543248304650997)
        ·
          refine ⟨1631905791707179528561031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17406995111543248304650997 1631905791707179528561031)
          ·
            refine ⟨2447858687560769292841547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631905791707179528561031 2447858687560769292841547)
            ·
              refine ⟨3671788031341153939262321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447858687560769292841547 3671788031341153939262321)
              ·
                refine ⟨2753841023505865454446741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3671788031341153939262321 2753841023505865454446741)
                ·
                  refine ⟨129086297976837443177191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2753841023505865454446741 129086297976837443177191)
                  ·
                    rfl

theorem cell23_2262552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_2262552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262552 prefixEnd_2262552 := by exact prefixLift 2262552
  have htrace : WordTrace (prefixWord ++ tailWord_2262552) baseStart_2262552 baseEnd_2262552 := by
    simpa [prefixWord, tailWord_2262552, baseEnd_2262552] using wordTrace_append hprefix tailTrace_2262552
  have hstable : (prefixWord ++ tailWord_2262552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262552).length < 2 ^ (prefixWord ++ tailWord_2262552).sum := by decide
  have hdescent : baseEnd_2262552 < baseStart_2262552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262585 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2262585 : Nat := 118140960795 + 2262585 * 2 ^ 59
def prefixEnd_2262585 : Nat := 4983230072969 + 3 ^ 40 * 2262585 * 2
def baseEnd_2262585 : Nat := 1161793626653135359482067

theorem tailTrace_2262585 : CollatzResearch.WordTrace tailWord_2262585 prefixEnd_2262585 1161793626653135359482067 := by
  unfold tailWord_2262585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82523254508048438598741209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55015503005365625732494139 82523254508048438598741209)
  ·
    refine ⟨61892440881036328949055907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82523254508048438598741209 61892440881036328949055907)
    ·
      refine ⟨92838661321554493423583861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61892440881036328949055907 92838661321554493423583861)
      ·
        refine ⟨8703624498895733758460987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92838661321554493423583861 8703624498895733758460987)
        ·
          refine ⟨13055436748343600637691481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8703624498895733758460987 13055436748343600637691481)
          ·
            refine ⟨9791577561257700478268611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13055436748343600637691481 9791577561257700478268611)
            ·
              refine ⟨14687366341886550717402917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9791577561257700478268611 14687366341886550717402917)
              ·
                refine ⟨2753881189103728259513047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14687366341886550717402917 2753881189103728259513047)
                ·
                  refine ⟨4130821783655592389269571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753881189103728259513047 4130821783655592389269571)
                  ·
                    refine ⟨6196232675483388583904357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130821783655592389269571 6196232675483388583904357)
                    ·
                      refine ⟨1161793626653135359482067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6196232675483388583904357 1161793626653135359482067)
                      ·
                        rfl

theorem cell23_2262585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2262585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262585 prefixEnd_2262585 := by exact prefixLift 2262585
  have htrace : WordTrace (prefixWord ++ tailWord_2262585) baseStart_2262585 baseEnd_2262585 := by
    simpa [prefixWord, tailWord_2262585, baseEnd_2262585] using wordTrace_append hprefix tailTrace_2262585
  have hstable : (prefixWord ++ tailWord_2262585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262585).length < 2 ^ (prefixWord ++ tailWord_2262585).sum := by decide
  have hdescent : baseEnd_2262585 < baseStart_2262585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262611 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_2262611 : Nat := 118140960795 + 2262611 * 2 ^ 59
def prefixEnd_2262611 : Nat := 4983230072969 + 3 ^ 40 * 2262611 * 2
def baseEnd_2262611 : Nat := 1161806977150152257756947

theorem tailTrace_2262611 : CollatzResearch.WordTrace tailWord_2262611 prefixEnd_2262611 1161806977150152257756947 := by
  unfold tailWord_2262611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82524202805954245039187687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55016135203969496692791791 82524202805954245039187687)
  ·
    refine ⟨123786304208931367558781531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82524202805954245039187687 123786304208931367558781531)
    ·
      refine ⟨185679456313397051338172297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123786304208931367558781531 185679456313397051338172297)
      ·
        refine ⟨139259592235047788503629223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185679456313397051338172297 139259592235047788503629223)
        ·
          refine ⟨208889388352571682755443835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139259592235047788503629223 208889388352571682755443835)
          ·
            refine ⟨313334082528857524133165753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208889388352571682755443835 313334082528857524133165753)
            ·
              refine ⟨235000561896643143099874315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313334082528857524133165753 235000561896643143099874315)
              ·
                refine ⟨352500842844964714649811473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235000561896643143099874315 352500842844964714649811473)
                ·
                  refine ⟨264375632133723535987358605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352500842844964714649811473 264375632133723535987358605)
                  ·
                    refine ⟨99140862050146325995259477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264375632133723535987358605 99140862050146325995259477)
                    ·
                      refine ⟨1161806977150152257756947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 99140862050146325995259477 1161806977150152257756947)
                      ·
                        rfl

theorem cell23_2262611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_2262611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262611 prefixEnd_2262611 := by exact prefixLift 2262611
  have htrace : WordTrace (prefixWord ++ tailWord_2262611) baseStart_2262611 baseEnd_2262611 := by
    simpa [prefixWord, tailWord_2262611, baseEnd_2262611] using wordTrace_append hprefix tailTrace_2262611
  have hstable : (prefixWord ++ tailWord_2262611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262611).length < 2 ^ (prefixWord ++ tailWord_2262611).sum := by decide
  have hdescent : baseEnd_2262611 < baseStart_2262611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262629 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2262629 : Nat := 118140960795 + 2262629 * 2 ^ 59
def prefixEnd_2262629 : Nat := 4983230072969 + 3 ^ 40 * 2262629 * 2
def baseEnd_2262629 : Nat := 387272073267311062443955

theorem tailTrace_2262629 : CollatzResearch.WordTrace tailWord_2262629 prefixEnd_2262629 387272073267311062443955 := by
  unfold tailWord_2262629
  simp only [CollatzResearch.WordTrace]
  refine ⟨82524859319889034113342941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55016572879926022742228627 82524859319889034113342941)
  ·
    refine ⟨30946822244958387792503603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82524859319889034113342941 30946822244958387792503603)
    ·
      refine ⟨46420233367437581688755405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30946822244958387792503603 46420233367437581688755405)
      ·
        refine ⟨17407587512789093133283277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46420233367437581688755405 17407587512789093133283277)
        ·
          refine ⟨6527845317295909924981229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17407587512789093133283277 6527845317295909924981229)
          ·
            refine ⟨2447941993985966221867961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6527845317295909924981229 2447941993985966221867961)
            ·
              refine ⟨1835956495489474666400971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447941993985966221867961 1835956495489474666400971)
              ·
                refine ⟨2753934743234211999601457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835956495489474666400971 2753934743234211999601457)
                ·
                  refine ⟨2065451057425658999701093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753934743234211999601457 2065451057425658999701093)
                  ·
                    refine ⟨387272073267311062443955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065451057425658999701093 387272073267311062443955)
                    ·
                      rfl

theorem cell23_2262629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2262629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262629 prefixEnd_2262629 := by exact prefixLift 2262629
  have htrace : WordTrace (prefixWord ++ tailWord_2262629) baseStart_2262629 baseEnd_2262629 := by
    simpa [prefixWord, tailWord_2262629, baseEnd_2262629] using wordTrace_append hprefix tailTrace_2262629
  have hstable : (prefixWord ++ tailWord_2262629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262629).length < 2 ^ (prefixWord ++ tailWord_2262629).sum := by decide
  have hdescent : baseEnd_2262629 < baseStart_2262629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262668 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_2262668 : Nat := 118140960795 + 2262668 * 2 ^ 59
def prefixEnd_2262668 : Nat := 4983230072969 + 3 ^ 40 * 2262668 * 2
def baseEnd_2262668 : Nat := 387278748515819511581395

theorem tailTrace_2262668 : CollatzResearch.WordTrace tailWord_2262668 prefixEnd_2262668 387278748515819511581395 := by
  unfold tailWord_2262668
  simp only [CollatzResearch.WordTrace]
  refine ⟨41263140883373871887006329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55017521177831829182675105 41263140883373871887006329)
  ·
    refine ⟨30947355662530403915254747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41263140883373871887006329 30947355662530403915254747)
    ·
      refine ⟨46421033493795605872882121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30947355662530403915254747 46421033493795605872882121)
      ·
        refine ⟨34815775120346704404661591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46421033493795605872882121 34815775120346704404661591)
        ·
          refine ⟨52223662680520056606992387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34815775120346704404661591 52223662680520056606992387)
          ·
            refine ⟨78335494020780084910488581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52223662680520056606992387 78335494020780084910488581)
            ·
              refine ⟨14687905128896265920716609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78335494020780084910488581 14687905128896265920716609)
              ·
                refine ⟨11015928846672199440537457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14687905128896265920716609 11015928846672199440537457)
                ·
                  refine ⟨8261946635004149580403093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11015928846672199440537457 8261946635004149580403093)
                  ·
                    refine ⟨387278748515819511581395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8261946635004149580403093 387278748515819511581395)
                    ·
                      rfl

theorem cell23_2262668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_2262668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262668 prefixEnd_2262668 := by exact prefixLift 2262668
  have htrace : WordTrace (prefixWord ++ tailWord_2262668) baseStart_2262668 baseEnd_2262668 := by
    simpa [prefixWord, tailWord_2262668, baseEnd_2262668] using wordTrace_append hprefix tailTrace_2262668
  have hstable : (prefixWord ++ tailWord_2262668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262668).length < 2 ^ (prefixWord ++ tailWord_2262668).sum := by decide
  have hdescent : baseEnd_2262668 < baseStart_2262668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262692 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_2262692 : Nat := 118140960795 + 2262692 * 2 ^ 59
def prefixEnd_2262692 : Nat := 4983230072969 + 3 ^ 40 * 2262692 * 2
def baseEnd_2262692 : Nat := 1161848569083166440844075

theorem tailTrace_2262692 : CollatzResearch.WordTrace tailWord_2262692 prefixEnd_2262692 1161848569083166440844075 := by
  unfold tailWord_2262692
  simp only [CollatzResearch.WordTrace]
  refine ⟨41263578559330397936443165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55018104745773863915257553 41263578559330397936443165)
  ·
    refine ⟨15473841959748899226166187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41263578559330397936443165 15473841959748899226166187)
    ·
      refine ⟨23210762939623348839249281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15473841959748899226166187 23210762939623348839249281)
      ·
        refine ⟨17408072204717511629436961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23210762939623348839249281 17408072204717511629436961)
        ·
          refine ⟨13056054153538133722077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17408072204717511629436961 13056054153538133722077721)
          ·
            refine ⟨9792040615153600291558291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13056054153538133722077721 9792040615153600291558291)
            ·
              refine ⟨14688060922730400437337437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9792040615153600291558291 14688060922730400437337437)
              ·
                refine ⟨5508022846023900164001539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14688060922730400437337437 5508022846023900164001539)
                ·
                  refine ⟨8262034269035850246002309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5508022846023900164001539 8262034269035850246002309)
                  ·
                    refine ⟨1549131425444221921125433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8262034269035850246002309 1549131425444221921125433)
                    ·
                      refine ⟨1161848569083166440844075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549131425444221921125433 1161848569083166440844075)
                      ·
                        rfl

theorem cell23_2262692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_2262692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262692 prefixEnd_2262692 := by exact prefixLift 2262692
  have htrace : WordTrace (prefixWord ++ tailWord_2262692) baseStart_2262692 baseEnd_2262692 := by
    simpa [prefixWord, tailWord_2262692, baseEnd_2262692] using wordTrace_append hprefix tailTrace_2262692
  have hstable : (prefixWord ++ tailWord_2262692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262692).length < 2 ^ (prefixWord ++ tailWord_2262692).sum := by decide
  have hdescent : baseEnd_2262692 < baseStart_2262692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262732 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 7]
def baseStart_2262732 : Nat := 118140960795 + 2262732 * 2 ^ 59
def prefixEnd_2262732 : Nat := 4983230072969 + 3 ^ 40 * 2262732 * 2
def baseEnd_2262732 : Nat := 129096567589927364927099

theorem tailTrace_2262732 : CollatzResearch.WordTrace tailWord_2262732 prefixEnd_2262732 129096567589927364927099 := by
  unfold tailWord_2262732
  simp only [CollatzResearch.WordTrace]
  refine ⟨41264308019257941352171225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55019077359010588469561633 41264308019257941352171225)
  ·
    refine ⟨30948231014443456014128419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41264308019257941352171225 30948231014443456014128419)
    ·
      refine ⟨46422346521665184021192629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30948231014443456014128419 46422346521665184021192629)
      ·
        refine ⟨4352094986406111001986809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46422346521665184021192629 4352094986406111001986809)
        ·
          refine ⟨3264071239804583251490107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352094986406111001986809 3264071239804583251490107)
          ·
            refine ⟨4896106859706874877235161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264071239804583251490107 4896106859706874877235161)
            ·
              refine ⟨3672080144780156157926371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896106859706874877235161 3672080144780156157926371)
              ·
                refine ⟨5508120217170234236889557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672080144780156157926371 5508120217170234236889557)
                ·
                  refine ⟨129096567589927364927099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5508120217170234236889557 129096567589927364927099)
                  ·
                    rfl

theorem cell23_2262732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_2262732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262732 prefixEnd_2262732 := by exact prefixLift 2262732
  have htrace : WordTrace (prefixWord ++ tailWord_2262732) baseStart_2262732 baseEnd_2262732 := by
    simpa [prefixWord, tailWord_2262732, baseEnd_2262732] using wordTrace_append hprefix tailTrace_2262732
  have hstable : (prefixWord ++ tailWord_2262732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262732).length < 2 ^ (prefixWord ++ tailWord_2262732).sum := by decide
  have hdescent : baseEnd_2262732 < baseStart_2262732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262735 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 7, 2]
def baseStart_2262735 : Nat := 118140960795 + 2262735 * 2 ^ 59
def prefixEnd_2262735 : Nat := 4983230072969 + 3 ^ 40 * 2262735 * 2
def baseEnd_2262735 : Nat := 1161870648751309772606377

theorem tailTrace_2262735 : CollatzResearch.WordTrace tailWord_2262735 prefixEnd_2262735 1161870648751309772606377 := by
  unfold tailWord_2262735
  simp only [CollatzResearch.WordTrace]
  refine ⟨82528725457505014216701659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55019150305003342811134439 82528725457505014216701659)
  ·
    refine ⟨123793088186257521325052489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82528725457505014216701659 123793088186257521325052489)
    ·
      refine ⟨92844816139693140993789367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123793088186257521325052489 92844816139693140993789367)
      ·
        refine ⟨139267224209539711490684051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92844816139693140993789367 139267224209539711490684051)
        ·
          refine ⟨208900836314309567236026077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139267224209539711490684051 208900836314309567236026077)
          ·
            refine ⟨78337813617866087713509779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208900836314309567236026077 78337813617866087713509779)
            ·
              refine ⟨117506720426799131570264669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78337813617866087713509779 117506720426799131570264669)
              ·
                refine ⟨44065020160049674338849251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117506720426799131570264669 44065020160049674338849251)
                ·
                  refine ⟨66097530240074511508273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44065020160049674338849251 66097530240074511508273877)
                  ·
                    refine ⟨1549160865001746363475169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66097530240074511508273877 1549160865001746363475169)
                    ·
                      refine ⟨1161870648751309772606377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549160865001746363475169 1161870648751309772606377)
                      ·
                        rfl

theorem cell23_2262735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7, 2].length) (baseStart_2262735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262735 prefixEnd_2262735 := by exact prefixLift 2262735
  have htrace : WordTrace (prefixWord ++ tailWord_2262735) baseStart_2262735 baseEnd_2262735 := by
    simpa [prefixWord, tailWord_2262735, baseEnd_2262735] using wordTrace_append hprefix tailTrace_2262735
  have hstable : (prefixWord ++ tailWord_2262735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262735).length < 2 ^ (prefixWord ++ tailWord_2262735).sum := by decide
  have hdescent : baseEnd_2262735 < baseStart_2262735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262775 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 5, 4]
def baseStart_2262775 : Nat := 118140960795 + 2262775 * 2 ^ 59
def prefixEnd_2262775 : Nat := 4983230072969 + 3 ^ 40 * 2262775 * 2
def baseEnd_2262775 : Nat := 387297062659163205368731

theorem tailTrace_2262775 : CollatzResearch.WordTrace tailWord_2262775 prefixEnd_2262775 387297062659163205368731 := by
  unfold tailWord_2262775
  simp only [CollatzResearch.WordTrace]
  refine ⟨82530184377360101048157779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55020122918240067365438519 82530184377360101048157779)
  ·
    refine ⟨123795276566040151572236669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82530184377360101048157779 123795276566040151572236669)
    ·
      refine ⟨46423228712265056839588751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123795276566040151572236669 46423228712265056839588751)
      ·
        refine ⟨69634843068397585259383127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46423228712265056839588751 69634843068397585259383127)
        ·
          refine ⟨104452264602596377889074691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69634843068397585259383127 104452264602596377889074691)
          ·
            refine ⟨156678396903894566833612037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104452264602596377889074691 156678396903894566833612037)
            ·
              refine ⟨29377199419480231281302257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156678396903894566833612037 29377199419480231281302257)
              ·
                refine ⟨22032899564610173460976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29377199419480231281302257 22032899564610173460976693)
                ·
                  refine ⟨2065584334182203761966565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22032899564610173460976693 2065584334182203761966565)
                  ·
                    refine ⟨387297062659163205368731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2065584334182203761966565 387297062659163205368731)
                    ·
                      rfl

theorem cell23_2262775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_2262775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262775 prefixEnd_2262775 := by exact prefixLift 2262775
  have htrace : WordTrace (prefixWord ++ tailWord_2262775) baseStart_2262775 baseEnd_2262775 := by
    simpa [prefixWord, tailWord_2262775, baseEnd_2262775] using wordTrace_append hprefix tailTrace_2262775
  have hstable : (prefixWord ++ tailWord_2262775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262775).length < 2 ^ (prefixWord ++ tailWord_2262775).sum := by decide
  have hdescent : baseEnd_2262775 < baseStart_2262775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262876 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2262876 : Nat := 118140960795 + 2262876 * 2 ^ 59
def prefixEnd_2262876 : Nat := 4983230072969 + 3 ^ 40 * 2262876 * 2
def baseEnd_2262876 : Nat := 1161943049523593720943229

theorem tailTrace_2262876 : CollatzResearch.WordTrace tailWord_2262876 prefixEnd_2262876 1161943049523593720943229 := by
  unfold tailWord_2262876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41266934074997097648792241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55022578766662796865056321 41266934074997097648792241)
  ·
    refine ⟨30950200556247823236594181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41266934074997097648792241 30950200556247823236594181)
    ·
      refine ⟨5803162604296466856861409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30950200556247823236594181 5803162604296466856861409)
      ·
        refine ⟨4352371953222350142646057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5803162604296466856861409 4352371953222350142646057)
        ·
          refine ⟨3264278964916762606984543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352371953222350142646057 3264278964916762606984543)
          ·
            refine ⟨4896418447375143910476815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264278964916762606984543 4896418447375143910476815)
            ·
              refine ⟨7344627671062715865715223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896418447375143910476815 7344627671062715865715223)
              ·
                refine ⟨11016941506594073798572835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7344627671062715865715223 11016941506594073798572835)
                ·
                  refine ⟨16525412259891110697859253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11016941506594073798572835 16525412259891110697859253)
                  ·
                    refine ⟨1549257399364791627924305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16525412259891110697859253 1549257399364791627924305)
                    ·
                      refine ⟨1161943049523593720943229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549257399364791627924305 1161943049523593720943229)
                      ·
                        rfl

theorem cell23_2262876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2262876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262876 prefixEnd_2262876 := by exact prefixLift 2262876
  have htrace : WordTrace (prefixWord ++ tailWord_2262876) baseStart_2262876 baseEnd_2262876 := by
    simpa [prefixWord, tailWord_2262876, baseEnd_2262876] using wordTrace_append hprefix tailTrace_2262876
  have hstable : (prefixWord ++ tailWord_2262876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262876).length < 2 ^ (prefixWord ++ tailWord_2262876).sum := by decide
  have hdescent : baseEnd_2262876 < baseStart_2262876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262883 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 1, 1, 3]
def baseStart_2262883 : Nat := 118140960795 + 2262883 * 2 ^ 59
def prefixEnd_2262883 : Nat := 4983230072969 + 3 ^ 40 * 2262883 * 2
def baseEnd_2262883 : Nat := 1161946643888175193555697

theorem tailTrace_2262883 : CollatzResearch.WordTrace tailWord_2262883 prefixEnd_2262883 1161946643888175193555697 := by
  unfold tailWord_2262883
  simp only [CollatzResearch.WordTrace]
  refine ⟨82534123460968835493089303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55022748973979223662059535 82534123460968835493089303)
  ·
    refine ⟨123801185191453253239633955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82534123460968835493089303 123801185191453253239633955)
    ·
      refine ⟨185701777787179879859450933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123801185191453253239633955 185701777787179879859450933)
      ·
        refine ⟨17409541667548113736823525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185701777787179879859450933 17409541667548113736823525)
        ·
          refine ⟨3264289062665271325654411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17409541667548113736823525 3264289062665271325654411)
          ·
            refine ⟨4896433593997906988481617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264289062665271325654411 4896433593997906988481617)
            ·
              refine ⟨3672325195498430241361213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896433593997906988481617 3672325195498430241361213)
              ·
                refine ⟨1377121948311911340510455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3672325195498430241361213 1377121948311911340510455)
                ·
                  refine ⟨2065682922467867010765683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377121948311911340510455 2065682922467867010765683)
                  ·
                    refine ⟨3098524383701800516148525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065682922467867010765683 3098524383701800516148525)
                    ·
                      refine ⟨1161946643888175193555697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098524383701800516148525 1161946643888175193555697)
                      ·
                        rfl

theorem cell23_2262883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_2262883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262883 prefixEnd_2262883 := by exact prefixLift 2262883
  have htrace : WordTrace (prefixWord ++ tailWord_2262883) baseStart_2262883 baseEnd_2262883 := by
    simpa [prefixWord, tailWord_2262883, baseEnd_2262883] using wordTrace_append hprefix tailTrace_2262883
  have hstable : (prefixWord ++ tailWord_2262883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262883).length < 2 ^ (prefixWord ++ tailWord_2262883).sum := by decide
  have hdescent : baseEnd_2262883 < baseStart_2262883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262885 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2262885 : Nat := 118140960795 + 2262885 * 2 ^ 59
def prefixEnd_2262885 : Nat := 4983230072969 + 3 ^ 40 * 2262885 * 2
def baseEnd_2262885 : Nat := 1161947670849484185730687

theorem tailTrace_2262885 : CollatzResearch.WordTrace tailWord_2262885 prefixEnd_2262885 1161947670849484185730687 := by
  unfold tailWord_2262885
  simp only [CollatzResearch.WordTrace]
  refine ⟨82534196406961589834662109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55022797604641059889774739 82534196406961589834662109)
  ·
    refine ⟨30950323652610596187998291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82534196406961589834662109 30950323652610596187998291)
    ·
      refine ⟨46425485478915894281997437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30950323652610596187998291 46425485478915894281997437)
      ·
        refine ⟨17409557054593460355749039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46425485478915894281997437 17409557054593460355749039)
        ·
          refine ⟨26114335581890190533623559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17409557054593460355749039 26114335581890190533623559)
          ·
            refine ⟨39171503372835285800435339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26114335581890190533623559 39171503372835285800435339)
            ·
              refine ⟨58757255059252928700653009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39171503372835285800435339 58757255059252928700653009)
              ·
                refine ⟨44067941294439696525489757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58757255059252928700653009 44067941294439696525489757)
                ·
                  refine ⟨16525477985414886197058659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44067941294439696525489757 16525477985414886197058659)
                  ·
                    refine ⟨24788216978122329295587989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16525477985414886197058659 24788216978122329295587989)
                    ·
                      refine ⟨1161947670849484185730687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24788216978122329295587989 1161947670849484185730687)
                      ·
                        rfl

theorem cell23_2262885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2262885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262885 prefixEnd_2262885 := by exact prefixLift 2262885
  have htrace : WordTrace (prefixWord ++ tailWord_2262885) baseStart_2262885 baseEnd_2262885 := by
    simpa [prefixWord, tailWord_2262885, baseEnd_2262885] using wordTrace_append hprefix tailTrace_2262885
  have hstable : (prefixWord ++ tailWord_2262885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262885).length < 2 ^ (prefixWord ++ tailWord_2262885).sum := by decide
  have hdescent : baseEnd_2262885 < baseStart_2262885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262934 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2262934 : Nat := 118140960795 + 2262934 * 2 ^ 59
def prefixEnd_2262934 : Nat := 4983230072969 + 3 ^ 40 * 2262934 * 2
def baseEnd_2262934 : Nat := 1161972831401554494017963

theorem tailTrace_2262934 : CollatzResearch.WordTrace tailWord_2262934 prefixEnd_2262934 1161972831401554494017963 := by
  unfold tailWord_2262934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158498973986504450199741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55023989055856047468797237 5158498973986504450199741)
  ·
    refine ⟨1934437115244939168824903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5158498973986504450199741 1934437115244939168824903)
    ·
      refine ⟨2901655672867408753237355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934437115244939168824903 2901655672867408753237355)
      ·
        refine ⟨4352483509301113129856033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901655672867408753237355 4352483509301113129856033)
        ·
          refine ⟨3264362631975834847392025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352483509301113129856033 3264362631975834847392025)
          ·
            refine ⟨2448271973981876135544019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3264362631975834847392025 2448271973981876135544019)
            ·
              refine ⟨3672407960972814203316029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448271973981876135544019 3672407960972814203316029)
              ·
                refine ⟨1377152985364805326243511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3672407960972814203316029 1377152985364805326243511)
                ·
                  refine ⟨2065729478047207989365267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377152985364805326243511 2065729478047207989365267)
                  ·
                    refine ⟨3098594217070811984047901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065729478047207989365267 3098594217070811984047901)
                    ·
                      refine ⟨1161972831401554494017963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098594217070811984047901 1161972831401554494017963)
                      ·
                        rfl

theorem cell23_2262934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2262934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262934 prefixEnd_2262934 := by exact prefixLift 2262934
  have htrace : WordTrace (prefixWord ++ tailWord_2262934) baseStart_2262934 baseEnd_2262934 := by
    simpa [prefixWord, tailWord_2262934, baseEnd_2262934] using wordTrace_append hprefix tailTrace_2262934
  have hstable : (prefixWord ++ tailWord_2262934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262934).length < 2 ^ (prefixWord ++ tailWord_2262934).sum := by decide
  have hdescent : baseEnd_2262934 < baseStart_2262934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262940 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2262940 : Nat := 118140960795 + 2262940 * 2 ^ 59
def prefixEnd_2262940 : Nat := 4983230072969 + 3 ^ 40 * 2262940 * 2
def baseEnd_2262940 : Nat := 1161975912285481470542935

theorem tailTrace_2262940 : CollatzResearch.WordTrace tailWord_2262940 prefixEnd_2262940 1161975912285481470542935 := by
  unfold tailWord_2262940
  simp only [CollatzResearch.WordTrace]
  refine ⟨41268101210881167113957137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55024134947841556151942849 41268101210881167113957137)
  ·
    refine ⟨30951075908160875335467853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41268101210881167113957137 30951075908160875335467853)
    ·
      refine ⟨11606653465560328250800445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30951075908160875335467853 11606653465560328250800445)
      ·
        refine ⟨4352495049585123094050167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11606653465560328250800445 4352495049585123094050167)
        ·
          refine ⟨6528742574377684641075251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352495049585123094050167 6528742574377684641075251)
          ·
            refine ⟨9793113861566526961612877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528742574377684641075251 9793113861566526961612877)
            ·
              refine ⟨3672417698087447610604829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9793113861566526961612877 3672417698087447610604829)
              ·
                refine ⟨1377156636782792853976811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3672417698087447610604829 1377156636782792853976811)
                ·
                  refine ⟨2065734955174189280965217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377156636782792853976811 2065734955174189280965217)
                  ·
                    refine ⟨1549301216380641960723913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2065734955174189280965217 1549301216380641960723913)
                    ·
                      refine ⟨1161975912285481470542935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549301216380641960723913 1161975912285481470542935)
                      ·
                        rfl

theorem cell23_2262940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2262940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262940 prefixEnd_2262940 := by exact prefixLift 2262940
  have htrace : WordTrace (prefixWord ++ tailWord_2262940) baseStart_2262940 baseEnd_2262940 := by
    simpa [prefixWord, tailWord_2262940, baseEnd_2262940] using wordTrace_append hprefix tailTrace_2262940
  have hstable : (prefixWord ++ tailWord_2262940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262940).length < 2 ^ (prefixWord ++ tailWord_2262940).sum := by decide
  have hdescent : baseEnd_2262940 < baseStart_2262940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262973 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_2262973 : Nat := 118140960795 + 2262973 * 2 ^ 59
def prefixEnd_2262973 : Nat := 4983230072969 + 3 ^ 40 * 2262973 * 2
def baseEnd_2262973 : Nat := 1161992857147079841430283

theorem tailTrace_2262973 : CollatzResearch.WordTrace tailWord_2262973 prefixEnd_2262973 1161992857147079841430283 := by
  unfold tailWord_2262973
  simp only [CollatzResearch.WordTrace]
  refine ⟨82537406030642780863865573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55024937353761853909243715 82537406030642780863865573)
  ·
    refine ⟨15475763630745521411974795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82537406030642780863865573 15475763630745521411974795)
    ·
      refine ⟨23213645446118282117962193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15475763630745521411974795 23213645446118282117962193)
      ·
        refine ⟨17410234084588711588471645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23213645446118282117962193 17410234084588711588471645)
        ·
          refine ⟨6528837781720766845676867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17410234084588711588471645 6528837781720766845676867)
          ·
            refine ⟨9793256672581150268515301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528837781720766845676867 9793256672581150268515301)
            ·
              refine ⟨1836235626108965675346619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9793256672581150268515301 1836235626108965675346619)
              ·
                refine ⟨2754353439163448513019929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836235626108965675346619 2754353439163448513019929)
                ·
                  refine ⟨2065765079372586384764947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754353439163448513019929 2065765079372586384764947)
                  ·
                    refine ⟨3098647619058879577147421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065765079372586384764947 3098647619058879577147421)
                    ·
                      refine ⟨1161992857147079841430283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098647619058879577147421 1161992857147079841430283)
                      ·
                        rfl

theorem cell23_2262973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_2262973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262973 prefixEnd_2262973 := by exact prefixLift 2262973
  have htrace : WordTrace (prefixWord ++ tailWord_2262973) baseStart_2262973 baseEnd_2262973 := by
    simpa [prefixWord, tailWord_2262973, baseEnd_2262973] using wordTrace_append hprefix tailTrace_2262973
  have hstable : (prefixWord ++ tailWord_2262973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262973).length < 2 ^ (prefixWord ++ tailWord_2262973).sum := by decide
  have hdescent : baseEnd_2262973 < baseStart_2262973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262996 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2262996 : Nat := 118140960795 + 2262996 * 2 ^ 59
def prefixEnd_2262996 : Nat := 4983230072969 + 3 ^ 40 * 2262996 * 2
def baseEnd_2262996 : Nat := 1162004667202133251442677

theorem tailTrace_2262996 : CollatzResearch.WordTrace tailWord_2262996 prefixEnd_2262996 1162004667202133251442677 := by
  unfold tailWord_2262996
  simp only [CollatzResearch.WordTrace]
  refine ⟨41269122454779727895976421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55025496606372970527968561 41269122454779727895976421)
  ·
    refine ⟨7737960460271198980495579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41269122454779727895976421 7737960460271198980495579)
    ·
      refine ⟨11606940690406798470743369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737960460271198980495579 11606940690406798470743369)
      ·
        refine ⟨8705205517805098853057527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11606940690406798470743369 8705205517805098853057527)
        ·
          refine ⟨13057808276707648279586291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705205517805098853057527 13057808276707648279586291)
          ·
            refine ⟨19586712415061472419379437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13057808276707648279586291 19586712415061472419379437)
            ·
              refine ⟨7345017155648052157267289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19586712415061472419379437 7345017155648052157267289)
              ·
                refine ⟨5508762866736039117950467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7345017155648052157267289 5508762866736039117950467)
                ·
                  refine ⟨8263144300104058676925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5508762866736039117950467 8263144300104058676925701)
                  ·
                    refine ⟨1549339556269511001923569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8263144300104058676925701 1549339556269511001923569)
                    ·
                      refine ⟨1162004667202133251442677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549339556269511001923569 1162004667202133251442677)
                      ·
                        rfl

theorem cell23_2262996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2262996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2262996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2262996 prefixEnd_2262996 := by exact prefixLift 2262996
  have htrace : WordTrace (prefixWord ++ tailWord_2262996) baseStart_2262996 baseEnd_2262996 := by
    simpa [prefixWord, tailWord_2262996, baseEnd_2262996] using wordTrace_append hprefix tailTrace_2262996
  have hstable : (prefixWord ++ tailWord_2262996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262996).length < 2 ^ (prefixWord ++ tailWord_2262996).sum := by decide
  have hdescent : baseEnd_2262996 < baseStart_2262996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263032 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_2263032 : Nat := 118140960795 + 2263032 * 2 ^ 59
def prefixEnd_2263032 : Nat := 4983230072969 + 3 ^ 40 * 2263032 * 2
def baseEnd_2263032 : Nat := 387341050835231703530837

theorem tailTrace_2263032 : CollatzResearch.WordTrace tailWord_2263032 prefixEnd_2263032 387341050835231703530837 := by
  unfold tailWord_2263032
  simp only [CollatzResearch.WordTrace]
  refine ⟨41269778968714516970131675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55026371958286022626842233 41269778968714516970131675)
  ·
    refine ⟨61904668453071775455197513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41269778968714516970131675 61904668453071775455197513)
    ·
      refine ⟨46428501339803831591398135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61904668453071775455197513 46428501339803831591398135)
      ·
        refine ⟨69642752009705747387097203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46428501339803831591398135 69642752009705747387097203)
        ·
          refine ⟨104464128014558621080645805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69642752009705747387097203 104464128014558621080645805)
          ·
            refine ⟨39174048005459482905242177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104464128014558621080645805 39174048005459482905242177)
            ·
              refine ⟨29380536004094612178931633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39174048005459482905242177 29380536004094612178931633)
              ·
                refine ⟨22035402003070959134198725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29380536004094612178931633 22035402003070959134198725)
                ·
                  refine ⟨4131637875575804837662261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22035402003070959134198725 4131637875575804837662261)
                  ·
                    refine ⟨387341050835231703530837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4131637875575804837662261 387341050835231703530837)
                    ·
                      rfl

theorem cell23_2263032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_2263032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263032 prefixEnd_2263032 := by exact prefixLift 2263032
  have htrace : WordTrace (prefixWord ++ tailWord_2263032) baseStart_2263032 baseEnd_2263032 := by
    simpa [prefixWord, tailWord_2263032, baseEnd_2263032] using wordTrace_append hprefix tailTrace_2263032
  have hstable : (prefixWord ++ tailWord_2263032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263032).length < 2 ^ (prefixWord ++ tailWord_2263032).sum := by decide
  have hdescent : baseEnd_2263032 < baseStart_2263032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263089 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2263089 : Nat := 118140960795 + 2263089 * 2 ^ 59
def prefixEnd_2263089 : Nat := 4983230072969 + 3 ^ 40 * 2263089 * 2
def baseEnd_2263089 : Nat := 1162052420903001387579749

theorem tailTrace_2263089 : CollatzResearch.WordTrace tailWord_2263089 prefixEnd_2263089 1162052420903001387579749 := by
  unfold tailWord_2263089
  simp only [CollatzResearch.WordTrace]
  refine ⟨82541636898222532675088321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55027757932148355116725547 82541636898222532675088321)
  ·
    refine ⟨61906227673666899506316241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82541636898222532675088321 61906227673666899506316241)
    ·
      refine ⟨46429670755250174629737181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61906227673666899506316241 46429670755250174629737181)
      ·
        refine ⟨17411126533218815486151443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46429670755250174629737181 17411126533218815486151443)
        ·
          refine ⟨26116689799828223229227165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17411126533218815486151443 26116689799828223229227165)
          ·
            refine ⟨9793758674935583710960187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26116689799828223229227165 9793758674935583710960187)
            ·
              refine ⟨14690638012403375566440281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793758674935583710960187 14690638012403375566440281)
              ·
                refine ⟨11017978509302531674830211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14690638012403375566440281 11017978509302531674830211)
                ·
                  refine ⟨16526967763953797512245317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11017978509302531674830211 16526967763953797512245317)
                  ·
                    refine ⟨3098806455741337033545997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16526967763953797512245317 3098806455741337033545997)
                    ·
                      refine ⟨1162052420903001387579749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098806455741337033545997 1162052420903001387579749)
                      ·
                        rfl

theorem cell23_2263089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2263089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263089 prefixEnd_2263089 := by exact prefixLift 2263089
  have htrace : WordTrace (prefixWord ++ tailWord_2263089) baseStart_2263089 baseEnd_2263089 := by
    simpa [prefixWord, tailWord_2263089, baseEnd_2263089] using wordTrace_append hprefix tailTrace_2263089
  have hstable : (prefixWord ++ tailWord_2263089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263089).length < 2 ^ (prefixWord ++ tailWord_2263089).sum := by decide
  have hdescent : baseEnd_2263089 < baseStart_2263089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263112 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2263112 : Nat := 118140960795 + 2263112 * 2 ^ 59
def prefixEnd_2263112 : Nat := 4983230072969 + 3 ^ 40 * 2263112 * 2
def baseEnd_2263112 : Nat := 1162064230958054797592143

theorem tailTrace_2263112 : CollatzResearch.WordTrace tailWord_2263112 prefixEnd_2263112 1162064230958054797592143 := by
  unfold tailWord_2263112
  simp only [CollatzResearch.WordTrace]
  refine ⟨41271237888569603801587795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55028317184759471735450393 41271237888569603801587795)
  ·
    refine ⟨61906856832854405702381693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41271237888569603801587795 61906856832854405702381693)
    ·
      refine ⟨23215071312320402138393135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61906856832854405702381693 23215071312320402138393135)
      ·
        refine ⟨34822606968480603207589703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23215071312320402138393135 34822606968480603207589703)
        ·
          refine ⟨52233910452720904811384555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34822606968480603207589703 52233910452720904811384555)
          ·
            refine ⟨78350865679081357217076833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52233910452720904811384555 78350865679081357217076833)
            ·
              refine ⟨58763149259311017912807625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78350865679081357217076833 58763149259311017912807625)
              ·
                refine ⟨44072361944483263434605719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58763149259311017912807625 44072361944483263434605719)
                ·
                  refine ⟨66108542916724895151908579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44072361944483263434605719 66108542916724895151908579)
                  ·
                    refine ⟨99162814375087342727862869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66108542916724895151908579 99162814375087342727862869)
                    ·
                      refine ⟨1162064230958054797592143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 99162814375087342727862869 1162064230958054797592143)
                      ·
                        rfl

theorem cell23_2263112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2263112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263112 prefixEnd_2263112 := by exact prefixLift 2263112
  have htrace : WordTrace (prefixWord ++ tailWord_2263112) baseStart_2263112 baseEnd_2263112 := by
    simpa [prefixWord, tailWord_2263112, baseEnd_2263112] using wordTrace_append hprefix tailTrace_2263112
  have hstable : (prefixWord ++ tailWord_2263112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263112).length < 2 ^ (prefixWord ++ tailWord_2263112).sum := by decide
  have hdescent : baseEnd_2263112 < baseStart_2263112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263173 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2263173 : Nat := 118140960795 + 2263173 * 2 ^ 59
def prefixEnd_2263173 : Nat := 4983230072969 + 3 ^ 40 * 2263173 * 2
def baseEnd_2263173 : Nat := 387365184425993019643121

theorem tailTrace_2263173 : CollatzResearch.WordTrace tailWord_2263173 prefixEnd_2263173 387365184425993019643121 := by
  unfold tailWord_2263173
  simp only [CollatzResearch.WordTrace]
  refine ⟨82544700629918215021146173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55029800419945476680764115 82544700629918215021146173)
  ·
    refine ⟨30954262736219330632929815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82544700629918215021146173 30954262736219330632929815)
    ·
      refine ⟨46431394104328995949394723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30954262736219330632929815 46431394104328995949394723)
      ·
        refine ⟨69647091156493493924092085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46431394104328995949394723 69647091156493493924092085)
        ·
          refine ⟨6529414795921265055383633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69647091156493493924092085 6529414795921265055383633)
          ·
            refine ⟨4897061096940948791537725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6529414795921265055383633 4897061096940948791537725)
            ·
              refine ⟨1836397911352855796826647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4897061096940948791537725 1836397911352855796826647)
              ·
                refine ⟨2754596867029283695239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836397911352855796826647 2754596867029283695239971)
                ·
                  refine ⟨4131895300543925542859957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754596867029283695239971 4131895300543925542859957)
                  ·
                    refine ⟨387365184425993019643121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4131895300543925542859957 387365184425993019643121)
                    ·
                      rfl

theorem cell23_2263173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2263173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263173 prefixEnd_2263173 := by exact prefixLift 2263173
  have htrace : WordTrace (prefixWord ++ tailWord_2263173) baseStart_2263173 baseEnd_2263173 := by
    simpa [prefixWord, tailWord_2263173, baseEnd_2263173] using wordTrace_append hprefix tailTrace_2263173
  have hstable : (prefixWord ++ tailWord_2263173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263173).length < 2 ^ (prefixWord ++ tailWord_2263173).sum := by decide
  have hdescent : baseEnd_2263173 < baseStart_2263173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263189 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2263189 : Nat := 118140960795 + 2263189 * 2 ^ 59
def prefixEnd_2263189 : Nat := 4983230072969 + 3 ^ 40 * 2263189 * 2
def baseEnd_2263189 : Nat := 1162103768968450996329289

theorem tailTrace_2263189 : CollatzResearch.WordTrace tailWord_2263189 prefixEnd_2263189 1162103768968450996329289 := by
  unfold tailWord_2263189
  simp only [CollatzResearch.WordTrace]
  refine ⟨82545284197860249753728621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55030189465240166502485747 82545284197860249753728621)
  ·
    refine ⟨30954481574197593657648233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82545284197860249753728621 30954481574197593657648233)
    ·
      refine ⟨23215861180648195243236175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30954481574197593657648233 23215861180648195243236175)
      ·
        refine ⟨34823791770972292864854263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23215861180648195243236175 34823791770972292864854263)
        ·
          refine ⟨52235687656458439297281395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34823791770972292864854263 52235687656458439297281395)
          ·
            refine ⟨78353531484687658945922093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52235687656458439297281395 78353531484687658945922093)
            ·
              refine ⟨29382574306757872104720785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78353531484687658945922093 29382574306757872104720785)
              ·
                refine ⟨22036930730068404078540589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29382574306757872104720785 22036930730068404078540589)
                ·
                  refine ⟨8263849023775651529452721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22036930730068404078540589 8263849023775651529452721)
                  ·
                    refine ⟨6197886767831738647089541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8263849023775651529452721 6197886767831738647089541)
                    ·
                      refine ⟨1162103768968450996329289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6197886767831738647089541 1162103768968450996329289)
                      ·
                        rfl

theorem cell23_2263189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2263189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263189 prefixEnd_2263189 := by exact prefixLift 2263189
  have htrace : WordTrace (prefixWord ++ tailWord_2263189) baseStart_2263189 baseEnd_2263189 := by
    simpa [prefixWord, tailWord_2263189, baseEnd_2263189] using wordTrace_append hprefix tailTrace_2263189
  have hstable : (prefixWord ++ tailWord_2263189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263189).length < 2 ^ (prefixWord ++ tailWord_2263189).sum := by decide
  have hdescent : baseEnd_2263189 < baseStart_2263189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263196 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2263196 : Nat := 118140960795 + 2263196 * 2 ^ 59
def prefixEnd_2263196 : Nat := 4983230072969 + 3 ^ 40 * 2263196 * 2
def baseEnd_2263196 : Nat := 1162107363333032468941757

theorem tailTrace_2263196 : CollatzResearch.WordTrace tailWord_2263196 prefixEnd_2263196 1162107363333032468941757 := by
  unfold tailWord_2263196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41272769754417444974616721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55030359672556593299488961 41272769754417444974616721)
  ·
    refine ⟨30954577315813083730962541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41272769754417444974616721 30954577315813083730962541)
    ·
      refine ⟨11607966493429906399110953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30954577315813083730962541 11607966493429906399110953)
      ·
        refine ⟨8705974870072429799333215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11607966493429906399110953 8705974870072429799333215)
        ·
          refine ⟨13058962305108644698999823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705974870072429799333215 13058962305108644698999823)
          ·
            refine ⟨19588443457662967048499735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13058962305108644698999823 19588443457662967048499735)
            ·
              refine ⟨29382665186494450572749603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19588443457662967048499735 29382665186494450572749603)
              ·
                refine ⟨44073997779741675859124405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29382665186494450572749603 44073997779741675859124405)
                ·
                  refine ⟨4131937291850782111792913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44073997779741675859124405 4131937291850782111792913)
                  ·
                    refine ⟨3098952968888086583844685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131937291850782111792913 3098952968888086583844685)
                    ·
                      refine ⟨1162107363333032468941757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098952968888086583844685 1162107363333032468941757)
                      ·
                        rfl

theorem cell23_2263196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2263196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263196 prefixEnd_2263196 := by exact prefixLift 2263196
  have htrace : WordTrace (prefixWord ++ tailWord_2263196) baseStart_2263196 baseEnd_2263196 := by
    simpa [prefixWord, tailWord_2263196, baseEnd_2263196] using wordTrace_append hprefix tailTrace_2263196
  have hstable : (prefixWord ++ tailWord_2263196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263196).length < 2 ^ (prefixWord ++ tailWord_2263196).sum := by decide
  have hdescent : baseEnd_2263196 < baseStart_2263196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263213 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2263213 : Nat := 118140960795 + 2263213 * 2 ^ 59
def prefixEnd_2263213 : Nat := 4983230072969 + 3 ^ 40 * 2263213 * 2
def baseEnd_2263213 : Nat := 1162116092504158902429179

theorem tailTrace_2263213 : CollatzResearch.WordTrace tailWord_2263213 prefixEnd_2263213 1162116092504158902429179 := by
  unfold tailWord_2263213
  simp only [CollatzResearch.WordTrace]
  refine ⟨82546159549773301852602293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55030773033182201235068195 82546159549773301852602293)
  ·
    refine ⟨7738702457791247048681465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82546159549773301852602293 7738702457791247048681465)
    ·
      refine ⟨5804026843343435286511099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7738702457791247048681465 5804026843343435286511099)
      ·
        refine ⟨8706040265015152929766649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804026843343435286511099 8706040265015152929766649)
        ·
          refine ⟨6529530198761364697324987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8706040265015152929766649 6529530198761364697324987)
          ·
            refine ⟨9794295298142047045987481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529530198761364697324987 9794295298142047045987481)
            ·
              refine ⟨7345721473606535284490611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9794295298142047045987481 7345721473606535284490611)
              ·
                refine ⟨11018582210409802926735917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345721473606535284490611 11018582210409802926735917)
                ·
                  refine ⟨4131968328903676097525969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11018582210409802926735917 4131968328903676097525969)
                  ·
                    refine ⟨3098976246677757073144477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131968328903676097525969 3098976246677757073144477)
                    ·
                      refine ⟨1162116092504158902429179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098976246677757073144477 1162116092504158902429179)
                      ·
                        rfl

theorem cell23_2263213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2263213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263213 prefixEnd_2263213 := by exact prefixLift 2263213
  have htrace : WordTrace (prefixWord ++ tailWord_2263213) baseStart_2263213 baseEnd_2263213 := by
    simpa [prefixWord, tailWord_2263213, baseEnd_2263213] using wordTrace_append hprefix tailTrace_2263213
  have hstable : (prefixWord ++ tailWord_2263213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263213).length < 2 ^ (prefixWord ++ tailWord_2263213).sum := by decide
  have hdescent : baseEnd_2263213 < baseStart_2263213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263214 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2263214 : Nat := 118140960795 + 2263214 * 2 ^ 59
def prefixEnd_2263214 : Nat := 4983230072969 + 3 ^ 40 * 2263214 * 2
def baseEnd_2263214 : Nat := 1162116605984813398516675

theorem tailTrace_2263214 : CollatzResearch.WordTrace tailWord_2263214 prefixEnd_2263214 1162116605984813398516675 := by
  unfold tailWord_2263214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318274502846209877923587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55030797348513119348925797 10318274502846209877923587)
  ·
    refine ⟨15477411754269314816885381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10318274502846209877923587 15477411754269314816885381)
    ·
      refine ⟨2902014703925496528166009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15477411754269314816885381 2902014703925496528166009)
      ·
        refine ⟨2176511027944122396124507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2902014703925496528166009 2176511027944122396124507)
        ·
          refine ⟨3264766541916183594186761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176511027944122396124507 3264766541916183594186761)
          ·
            refine ⟨2448574906437137695640071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3264766541916183594186761 2448574906437137695640071)
            ·
              refine ⟨3672862359655706543460107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448574906437137695640071 3672862359655706543460107)
              ·
                refine ⟨5509293539483559815190161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672862359655706543460107 5509293539483559815190161)
                ·
                  refine ⟨4131970154612669861392621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509293539483559815190161 4131970154612669861392621)
                  ·
                    refine ⟨1549488807979751198022233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4131970154612669861392621 1549488807979751198022233)
                    ·
                      refine ⟨1162116605984813398516675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549488807979751198022233 1162116605984813398516675)
                      ·
                        rfl

theorem cell23_2263214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2263214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263214 prefixEnd_2263214 := by exact prefixLift 2263214
  have htrace : WordTrace (prefixWord ++ tailWord_2263214) baseStart_2263214 baseEnd_2263214 := by
    simpa [prefixWord, tailWord_2263214, baseEnd_2263214] using wordTrace_append hprefix tailTrace_2263214
  have hstable : (prefixWord ++ tailWord_2263214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263214).length < 2 ^ (prefixWord ++ tailWord_2263214).sum := by decide
  have hdescent : baseEnd_2263214 < baseStart_2263214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263226 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_2263226 : Nat := 118140960795 + 2263226 * 2 ^ 59
def prefixEnd_2263226 : Nat := 4983230072969 + 3 ^ 40 * 2263226 * 2
def baseEnd_2263226 : Nat := 1162122767752667351566619

theorem tailTrace_2263226 : CollatzResearch.WordTrace tailWord_2263226 prefixEnd_2263226 1162122767752667351566619 := by
  unfold tailWord_2263226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636658424681551268206383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55031089132484136715217021 20636658424681551268206383)
  ·
    refine ⟨30954987637022326902309575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20636658424681551268206383 30954987637022326902309575)
    ·
      refine ⟨46432481455533490353464363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30954987637022326902309575 46432481455533490353464363)
      ·
        refine ⟨69648722183300235530196545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46432481455533490353464363 69648722183300235530196545)
        ·
          refine ⟨52236541637475176647647409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69648722183300235530196545 52236541637475176647647409)
          ·
            refine ⟨39177406228106382485735557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52236541637475176647647409 39177406228106382485735557)
            ·
              refine ⟨7345763667769946716075417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39177406228106382485735557 7345763667769946716075417)
              ·
                refine ⟨5509322750827460037056563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7345763667769946716075417 5509322750827460037056563)
                ·
                  refine ⟨8263984126241190055584845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5509322750827460037056563 8263984126241190055584845)
                  ·
                    refine ⟨3098994047340446270844317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8263984126241190055584845 3098994047340446270844317)
                    ·
                      refine ⟨1162122767752667351566619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098994047340446270844317 1162122767752667351566619)
                      ·
                        rfl

theorem cell23_2263226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_2263226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263226 prefixEnd_2263226 := by exact prefixLift 2263226
  have htrace : WordTrace (prefixWord ++ tailWord_2263226) baseStart_2263226 baseEnd_2263226 := by
    simpa [prefixWord, tailWord_2263226, baseEnd_2263226] using wordTrace_append hprefix tailTrace_2263226
  have hstable : (prefixWord ++ tailWord_2263226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263226).length < 2 ^ (prefixWord ++ tailWord_2263226).sum := by decide
  have hdescent : baseEnd_2263226 < baseStart_2263226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263230 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2263230 : Nat := 118140960795 + 2263230 * 2 ^ 59
def prefixEnd_2263230 : Nat := 4983230072969 + 3 ^ 40 * 2263230 * 2
def baseEnd_2263230 : Nat := 1162124821675285335916601

theorem tailTrace_2263230 : CollatzResearch.WordTrace tailWord_2263230 prefixEnd_2263230 1162124821675285335916601 := by
  unfold tailWord_2263230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318347448838964219496393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55031186393807809170647429 10318347448838964219496393)
  ·
    refine ⟨7738760586629223164622295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10318347448838964219496393 7738760586629223164622295)
    ·
      refine ⟨11608140879943834746933443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738760586629223164622295 11608140879943834746933443)
      ·
        refine ⟨17412211319915752120400165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11608140879943834746933443 17412211319915752120400165)
        ·
          refine ⟨3264789622484203522575031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17412211319915752120400165 3264789622484203522575031)
          ·
            refine ⟨4897184433726305283862547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264789622484203522575031 4897184433726305283862547)
            ·
              refine ⟨7345776650589457925793821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897184433726305283862547 7345776650589457925793821)
              ·
                refine ⟨2754666243971046722172683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345776650589457925793821 2754666243971046722172683)
                ·
                  refine ⟨4131999365956570083259025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754666243971046722172683 4131999365956570083259025)
                  ·
                    refine ⟨3098999524467427562444269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131999365956570083259025 3098999524467427562444269)
                    ·
                      refine ⟨1162124821675285335916601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3098999524467427562444269 1162124821675285335916601)
                      ·
                        rfl

theorem cell23_2263230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2263230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263230 prefixEnd_2263230 := by exact prefixLift 2263230
  have htrace : WordTrace (prefixWord ++ tailWord_2263230) baseStart_2263230 baseEnd_2263230 := by
    simpa [prefixWord, tailWord_2263230, baseEnd_2263230] using wordTrace_append hprefix tailTrace_2263230
  have hstable : (prefixWord ++ tailWord_2263230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263230).length < 2 ^ (prefixWord ++ tailWord_2263230).sum := by decide
  have hdescent : baseEnd_2263230 < baseStart_2263230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263249 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_2263249 : Nat := 118140960795 + 2263249 * 2 ^ 59
def prefixEnd_2263249 : Nat := 4983230072969 + 3 ^ 40 * 2263249 * 2
def baseEnd_2263249 : Nat := 1162134577807720761579013

theorem tailTrace_2263249 : CollatzResearch.WordTrace tailWord_2263249 prefixEnd_2263249 1162134577807720761579013 := by
  unfold tailWord_2263249
  simp only [CollatzResearch.WordTrace]
  refine ⟨82547472577642880000912801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55031648385095253333941867 82547472577642880000912801)
  ·
    refine ⟨61910604433232160000684601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82547472577642880000912801 61910604433232160000684601)
    ·
      refine ⟨46432953324924120000513451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61910604433232160000684601 46432953324924120000513451)
      ·
        refine ⟨69649429987386180000770177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46432953324924120000513451 69649429987386180000770177)
        ·
          refine ⟨52237072490539635000577633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69649429987386180000770177 52237072490539635000577633)
          ·
            refine ⟨39177804367904726250433225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52237072490539635000577633 39177804367904726250433225)
            ·
              refine ⟨29383353275928544687824919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39177804367904726250433225 29383353275928544687824919)
              ·
                refine ⟨44075029913892817031737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29383353275928544687824919 44075029913892817031737379)
                ·
                  refine ⟨66112544870839225547606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44075029913892817031737379 66112544870839225547606069)
                  ·
                    refine ⟨6198051081641177395088069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66112544870839225547606069 6198051081641177395088069)
                    ·
                      refine ⟨1162134577807720761579013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6198051081641177395088069 1162134577807720761579013)
                      ·
                        rfl

theorem cell23_2263249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_2263249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263249 prefixEnd_2263249 := by exact prefixLift 2263249
  have htrace : WordTrace (prefixWord ++ tailWord_2263249) baseStart_2263249 baseEnd_2263249 := by
    simpa [prefixWord, tailWord_2263249, baseEnd_2263249] using wordTrace_append hprefix tailTrace_2263249
  have hstable : (prefixWord ++ tailWord_2263249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263249).length < 2 ^ (prefixWord ++ tailWord_2263249).sum := by decide
  have hdescent : baseEnd_2263249 < baseStart_2263249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263283 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 6, 2, 2]
def baseStart_2263283 : Nat := 118140960795 + 2263283 * 2 ^ 59
def prefixEnd_2263283 : Nat := 4983230072969 + 3 ^ 40 * 2263283 * 2
def baseEnd_2263283 : Nat := 1162152036149973628553857

theorem tailTrace_2263283 : CollatzResearch.WordTrace tailWord_2263283 prefixEnd_2263283 1162152036149973628553857 := by
  unfold tailWord_2263283
  simp only [CollatzResearch.WordTrace]
  refine ⟨82548712659519703807650503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55032475106346469205100335 82548712659519703807650503)
  ·
    refine ⟨123823068989279555711475755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82548712659519703807650503 123823068989279555711475755)
    ·
      refine ⟨185734603483919333567213633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123823068989279555711475755 185734603483919333567213633)
      ·
        refine ⟨139300952612939500175410225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185734603483919333567213633 139300952612939500175410225)
        ·
          refine ⟨104475714459704625131557669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139300952612939500175410225 104475714459704625131557669)
          ·
            refine ⟨19589196461194617212167063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104475714459704625131557669 19589196461194617212167063)
            ·
              refine ⟨29383794691791925818250595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19589196461194617212167063 29383794691791925818250595)
              ·
                refine ⟨44075692037687888727375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29383794691791925818250595 44075692037687888727375893)
                ·
                  refine ⟨2066048064266619784095745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44075692037687888727375893 2066048064266619784095745)
                  ·
                    refine ⟨1549536048199964838071809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066048064266619784095745 1549536048199964838071809)
                    ·
                      refine ⟨1162152036149973628553857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549536048199964838071809 1162152036149973628553857)
                      ·
                        rfl

theorem cell23_2263283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2, 2].length) (baseStart_2263283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263283 prefixEnd_2263283 := by exact prefixLift 2263283
  have htrace : WordTrace (prefixWord ++ tailWord_2263283) baseStart_2263283 baseEnd_2263283 := by
    simpa [prefixWord, tailWord_2263283, baseEnd_2263283] using wordTrace_append hprefix tailTrace_2263283
  have hstable : (prefixWord ++ tailWord_2263283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263283).length < 2 ^ (prefixWord ++ tailWord_2263283).sum := by decide
  have hdescent : baseEnd_2263283 < baseStart_2263283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263286 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2263286 : Nat := 118140960795 + 2263286 * 2 ^ 59
def prefixEnd_2263286 : Nat := 4983230072969 + 3 ^ 40 * 2263286 * 2
def baseEnd_2263286 : Nat := 1162153576591937116816343

theorem tailTrace_2263286 : CollatzResearch.WordTrace tailWord_2263286 prefixEnd_2263286 1162153576591937116816343 := by
  unfold tailWord_2263286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159301379906802207500607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55032548052339223546673141 5159301379906802207500607)
  ·
    refine ⟨7738952069860203311250911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159301379906802207500607 7738952069860203311250911)
    ·
      refine ⟨11608428104790304966876367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738952069860203311250911 11608428104790304966876367)
      ·
        refine ⟨17412642157185457450314551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11608428104790304966876367 17412642157185457450314551)
        ·
          refine ⟨26118963235778186175471827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17412642157185457450314551 26118963235778186175471827)
          ·
            refine ⟨39178444853667279263207741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26118963235778186175471827 39178444853667279263207741)
            ·
              refine ⟨14691916820125229723702903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39178444853667279263207741 14691916820125229723702903)
              ·
                refine ⟨22037875230187844585554355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14691916820125229723702903 22037875230187844585554355)
                ·
                  refine ⟨33056812845281766878331533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22037875230187844585554355 33056812845281766878331533)
                  ·
                    refine ⟨12396304816980662579374325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33056812845281766878331533 12396304816980662579374325)
                    ·
                      refine ⟨1162153576591937116816343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12396304816980662579374325 1162153576591937116816343)
                      ·
                        rfl

theorem cell23_2263286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2263286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263286 prefixEnd_2263286 := by exact prefixLift 2263286
  have htrace : WordTrace (prefixWord ++ tailWord_2263286) baseStart_2263286 baseEnd_2263286 := by
    simpa [prefixWord, tailWord_2263286, baseEnd_2263286] using wordTrace_append hprefix tailTrace_2263286
  have hstable : (prefixWord ++ tailWord_2263286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263286).length < 2 ^ (prefixWord ++ tailWord_2263286).sum := by decide
  have hdescent : baseEnd_2263286 < baseStart_2263286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263299 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2263299 : Nat := 118140960795 + 2263299 * 2 ^ 59
def prefixEnd_2263299 : Nat := 4983230072969 + 3 ^ 40 * 2263299 * 2
def baseEnd_2263299 : Nat := 1162160251840445565953783

theorem tailTrace_2263299 : CollatzResearch.WordTrace tailWord_2263299 prefixEnd_2263299 1162160251840445565953783 := by
  unfold tailWord_2263299
  simp only [CollatzResearch.WordTrace]
  refine ⟨82549296227461738540232951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55032864151641159026821967 82549296227461738540232951)
  ·
    refine ⟨123823944341192607810349427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82549296227461738540232951 123823944341192607810349427)
    ·
      refine ⟨185735916511788911715524141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123823944341192607810349427 185735916511788911715524141)
      ·
        refine ⟨69650968691920841893321553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185735916511788911715524141 69650968691920841893321553)
        ·
          refine ⟨52238226518940631419991165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69650968691920841893321553 52238226518940631419991165)
          ·
            refine ⟨19589334944602736782496687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52238226518940631419991165 19589334944602736782496687)
            ·
              refine ⟨29384002416904105173745031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19589334944602736782496687 29384002416904105173745031)
              ·
                refine ⟨44076003625356157760617547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29384002416904105173745031 44076003625356157760617547)
                ·
                  refine ⟨66114005438034236640926321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44076003625356157760617547 66114005438034236640926321)
                  ·
                    refine ⟨49585504078525677480694741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66114005438034236640926321 49585504078525677480694741)
                    ·
                      refine ⟨1162160251840445565953783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49585504078525677480694741 1162160251840445565953783)
                      ·
                        rfl

theorem cell23_2263299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2263299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263299 prefixEnd_2263299 := by exact prefixLift 2263299
  have htrace : WordTrace (prefixWord ++ tailWord_2263299) baseStart_2263299 baseEnd_2263299 := by
    simpa [prefixWord, tailWord_2263299, baseEnd_2263299] using wordTrace_append hprefix tailTrace_2263299
  have hstable : (prefixWord ++ tailWord_2263299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263299).length < 2 ^ (prefixWord ++ tailWord_2263299).sum := by decide
  have hdescent : baseEnd_2263299 < baseStart_2263299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263306 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_2263306 : Nat := 118140960795 + 2263306 * 2 ^ 59
def prefixEnd_2263306 : Nat := 4983230072969 + 3 ^ 40 * 2263306 * 2
def baseEnd_2263306 : Nat := 129129316245003004285139

theorem tailTrace_2263306 : CollatzResearch.WordTrace tailWord_2263306 prefixEnd_2263306 129129316245003004285139 := by
  unfold tailWord_2263306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637387884609094683934443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55033034358957585823825181 20637387884609094683934443)
  ·
    refine ⟨30956081826913642025901665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20637387884609094683934443 30956081826913642025901665)
    ·
      refine ⟨23217061370185231519426249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30956081826913642025901665 23217061370185231519426249)
      ·
        refine ⟨17412796027638923639569687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23217061370185231519426249 17412796027638923639569687)
        ·
          refine ⟨26119194041458385459354531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17412796027638923639569687 26119194041458385459354531)
          ·
            refine ⟨39178791062187578189031797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26119194041458385459354531 39178791062187578189031797)
            ·
              refine ⟨3673011662080085455221731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39178791062187578189031797 3673011662080085455221731)
              ·
                refine ⟨5509517493120128182832597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673011662080085455221731 5509517493120128182832597)
                ·
                  refine ⟨129129316245003004285139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5509517493120128182832597 129129316245003004285139)
                  ·
                    rfl

theorem cell23_2263306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_2263306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263306 prefixEnd_2263306 := by exact prefixLift 2263306
  have htrace : WordTrace (prefixWord ++ tailWord_2263306) baseStart_2263306 baseEnd_2263306 := by
    simpa [prefixWord, tailWord_2263306, baseEnd_2263306] using wordTrace_append hprefix tailTrace_2263306
  have hstable : (prefixWord ++ tailWord_2263306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263306).length < 2 ^ (prefixWord ++ tailWord_2263306).sum := by decide
  have hdescent : baseEnd_2263306 < baseStart_2263306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263317 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_2263317 : Nat := 118140960795 + 2263317 * 2 ^ 59
def prefixEnd_2263317 : Nat := 4983230072969 + 3 ^ 40 * 2263317 * 2
def baseEnd_2263317 : Nat := 1162169494492226495528701

theorem tailTrace_2263317 : CollatzResearch.WordTrace tailWord_2263317 prefixEnd_2263317 1162169494492226495528701 := by
  unfold tailWord_2263317
  simp only [CollatzResearch.WordTrace]
  refine ⟨82549952741396527614388205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55033301827597685076258803 82549952741396527614388205)
  ·
    refine ⟨30956232278023697855395577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82549952741396527614388205 30956232278023697855395577)
    ·
      refine ⟨23217174208517773391546683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30956232278023697855395577 23217174208517773391546683)
      ·
        refine ⟨34825761312776660087320025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217174208517773391546683 34825761312776660087320025)
        ·
          refine ⟨26119320984582495065490019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34825761312776660087320025 26119320984582495065490019)
          ·
            refine ⟨39178981476873742598235029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26119320984582495065490019 39178981476873742598235029)
            ·
              refine ⟨1836514756728456684292267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39178981476873742598235029 1836514756728456684292267)
              ·
                refine ⟨2754772135092685026438401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836514756728456684292267 2754772135092685026438401)
                ·
                  refine ⟨2066079101319513769828801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754772135092685026438401 2066079101319513769828801)
                  ·
                    refine ⟨1549559325989635327371601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066079101319513769828801 1549559325989635327371601)
                    ·
                      refine ⟨1162169494492226495528701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549559325989635327371601 1162169494492226495528701)
                      ·
                        rfl

theorem cell23_2263317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_2263317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263317 prefixEnd_2263317 := by exact prefixLift 2263317
  have htrace : WordTrace (prefixWord ++ tailWord_2263317) baseStart_2263317 baseEnd_2263317 := by
    simpa [prefixWord, tailWord_2263317, baseEnd_2263317] using wordTrace_append hprefix tailTrace_2263317
  have hstable : (prefixWord ++ tailWord_2263317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263317).length < 2 ^ (prefixWord ++ tailWord_2263317).sum := by decide
  have hdescent : baseEnd_2263317 < baseStart_2263317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263353 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_2263353 : Nat := 118140960795 + 2263353 * 2 ^ 59
def prefixEnd_2263353 : Nat := 4983230072969 + 3 ^ 40 * 2263353 * 2
def baseEnd_2263353 : Nat := 387395993265262784892845

theorem tailTrace_2263353 : CollatzResearch.WordTrace tailWord_2263353 prefixEnd_2263353 387395993265262784892845 := by
  unfold tailWord_2263353
  simp only [CollatzResearch.WordTrace]
  refine ⟨82551265769266105762698713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55034177179510737175132475 82551265769266105762698713)
  ·
    refine ⟨61913449326949579322024035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82551265769266105762698713 61913449326949579322024035)
    ·
      refine ⟨92870173990424368983036053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61913449326949579322024035 92870173990424368983036053)
      ·
        refine ⟨4353289405801142296079815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92870173990424368983036053 4353289405801142296079815)
        ·
          refine ⟨6529934108701713444119723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353289405801142296079815 6529934108701713444119723)
          ·
            refine ⟨9794901163052570166179585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529934108701713444119723 9794901163052570166179585)
            ·
              refine ⟨7346175872289427624634689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9794901163052570166179585 7346175872289427624634689)
              ·
                refine ⟨5509631904217070718476017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7346175872289427624634689 5509631904217070718476017)
                ·
                  refine ⟨4132223928162803038857013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509631904217070718476017 4132223928162803038857013)
                  ·
                    refine ⟨387395993265262784892845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4132223928162803038857013 387395993265262784892845)
                    ·
                      rfl

theorem cell23_2263353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_2263353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263353 prefixEnd_2263353 := by exact prefixLift 2263353
  have htrace : WordTrace (prefixWord ++ tailWord_2263353) baseStart_2263353 baseEnd_2263353 := by
    simpa [prefixWord, tailWord_2263353, baseEnd_2263353] using wordTrace_append hprefix tailTrace_2263353
  have hstable : (prefixWord ++ tailWord_2263353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263353).length < 2 ^ (prefixWord ++ tailWord_2263353).sum := by decide
  have hdescent : baseEnd_2263353 < baseStart_2263353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263383 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 3, 4]
def baseStart_2263383 : Nat := 118140960795 + 2263383 * 2 ^ 59
def prefixEnd_2263383 : Nat := 4983230072969 + 3 ^ 40 * 2263383 * 2
def baseEnd_2263383 : Nat := 387401128071807745767799

theorem tailTrace_2263383 : CollatzResearch.WordTrace tailWord_2263383 prefixEnd_2263383 387401128071807745767799 := by
  unfold tailWord_2263383
  simp only [CollatzResearch.WordTrace]
  refine ⟨82552359959157420886290803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55034906639438280590860535 82552359959157420886290803)
  ·
    refine ⟨123828539938736131329436205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82552359959157420886290803 123828539938736131329436205)
    ·
      refine ⟨46435702477026049248538577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123828539938736131329436205 46435702477026049248538577)
      ·
        refine ⟨34826776857769536936403933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46435702477026049248538577 34826776857769536936403933)
        ·
          refine ⟨13060041321663576351151475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34826776857769536936403933 13060041321663576351151475)
          ·
            refine ⟨19590061982495364526727213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060041321663576351151475 19590061982495364526727213)
            ·
              refine ⟨7346273243435761697522705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19590061982495364526727213 7346273243435761697522705)
              ·
                refine ⟨5509704932576821273142029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7346273243435761697522705 5509704932576821273142029)
                ·
                  refine ⟨2066139349716307977428261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5509704932576821273142029 2066139349716307977428261)
                  ·
                    refine ⟨387401128071807745767799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066139349716307977428261 387401128071807745767799)
                    ·
                      rfl

theorem cell23_2263383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_2263383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263383 prefixEnd_2263383 := by exact prefixLift 2263383
  have htrace : WordTrace (prefixWord ++ tailWord_2263383) baseStart_2263383 baseEnd_2263383 := by
    simpa [prefixWord, tailWord_2263383, baseEnd_2263383] using wordTrace_append hprefix tailTrace_2263383
  have hstable : (prefixWord ++ tailWord_2263383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263383).length < 2 ^ (prefixWord ++ tailWord_2263383).sum := by decide
  have hdescent : baseEnd_2263383 < baseStart_2263383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263396 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 8]
def baseStart_2263396 : Nat := 118140960795 + 2263396 * 2 ^ 59
def prefixEnd_2263396 : Nat := 4983230072969 + 3 ^ 40 * 2263396 * 2
def baseEnd_2263396 : Nat := 129134451051547965160093

theorem tailTrace_2263396 : CollatzResearch.WordTrace tailWord_2263396 prefixEnd_2263396 129134451051547965160093 := by
  unfold tailWord_2263396
  simp only [CollatzResearch.WordTrace]
  refine ⟨41276417054055162053257021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55035222738740216071009361 41276417054055162053257021)
  ·
    refine ⟨15478656395270685769971383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41276417054055162053257021 15478656395270685769971383)
    ·
      refine ⟨23217984592906028654957075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478656395270685769971383 23217984592906028654957075)
      ·
        refine ⟨34826976889359042982435613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217984592906028654957075 34826976889359042982435613)
        ·
          refine ⟨13060116333509641118413355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34826976889359042982435613 13060116333509641118413355)
          ·
            refine ⟨19590174500264461677620033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060116333509641118413355 19590174500264461677620033)
            ·
              refine ⟨14692630875198346258215025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19590174500264461677620033 14692630875198346258215025)
              ·
                refine ⟨11019473156398759693661269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14692630875198346258215025 11019473156398759693661269)
                ·
                  refine ⟨129134451051547965160093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11019473156398759693661269 129134451051547965160093)
                  ·
                    rfl

theorem cell23_2263396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_2263396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263396 prefixEnd_2263396 := by exact prefixLift 2263396
  have htrace : WordTrace (prefixWord ++ tailWord_2263396) baseStart_2263396 baseEnd_2263396 := by
    simpa [prefixWord, tailWord_2263396, baseEnd_2263396] using wordTrace_append hprefix tailTrace_2263396
  have hstable : (prefixWord ++ tailWord_2263396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263396).length < 2 ^ (prefixWord ++ tailWord_2263396).sum := by decide
  have hdescent : baseEnd_2263396 < baseStart_2263396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263413 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 8]
def baseStart_2263413 : Nat := 118140960795 + 2263413 * 2 ^ 59
def prefixEnd_2263413 : Nat := 4983230072969 + 3 ^ 40 * 2263413 * 2
def baseEnd_2263413 : Nat := 129135420959450902214251

theorem tailTrace_2263413 : CollatzResearch.WordTrace tailWord_2263413 prefixEnd_2263413 129135420959450902214251 := by
  unfold tailWord_2263413
  simp only [CollatzResearch.WordTrace]
  refine ⟨82553454149048736009882893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55035636099365824006588595 82553454149048736009882893)
  ·
    refine ⟨30957545305893276003706085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82553454149048736009882893 30957545305893276003706085)
    ·
      refine ⟨5804539744854989250694891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30957545305893276003706085 5804539744854989250694891)
      ·
        refine ⟨8706809617282483876042337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804539744854989250694891 8706809617282483876042337)
        ·
          refine ⟨6530107212961862907031753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8706809617282483876042337 6530107212961862907031753)
          ·
            refine ⟨4897580409721397180273815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530107212961862907031753 4897580409721397180273815)
            ·
              refine ⟨7346370614582095770410723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897580409721397180273815 7346370614582095770410723)
              ·
                refine ⟨11019555921873143655616085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346370614582095770410723 11019555921873143655616085)
                ·
                  refine ⟨129135420959450902214251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11019555921873143655616085 129135420959450902214251)
                  ·
                    rfl

theorem cell23_2263413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_2263413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263413 prefixEnd_2263413 := by exact prefixLift 2263413
  have htrace : WordTrace (prefixWord ++ tailWord_2263413) baseStart_2263413 baseEnd_2263413 := by
    simpa [prefixWord, tailWord_2263413, baseEnd_2263413] using wordTrace_append hprefix tailTrace_2263413
  have hstable : (prefixWord ++ tailWord_2263413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263413).length < 2 ^ (prefixWord ++ tailWord_2263413).sum := by decide
  have hdescent : baseEnd_2263413 < baseStart_2263413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263423 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_2263423 : Nat := 118140960795 + 2263423 * 2 ^ 59
def prefixEnd_2263423 : Nat := 4983230072969 + 3 ^ 40 * 2263423 * 2
def baseEnd_2263423 : Nat := 1162223923441603080803213

theorem tailTrace_2263423 : CollatzResearch.WordTrace tailWord_2263423 prefixEnd_2263423 1162223923441603080803213 := by
  unfold tailWord_2263423
  simp only [CollatzResearch.WordTrace]
  refine ⟨82553818879012507717746923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55035879252675005145164615 82553818879012507717746923)
  ·
    refine ⟨123830728318518761576620385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82553818879012507717746923 123830728318518761576620385)
    ·
      refine ⟨92873046238889071182465289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123830728318518761576620385 92873046238889071182465289)
      ·
        refine ⟨69654784679166803386848967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92873046238889071182465289 69654784679166803386848967)
        ·
          refine ⟨104482177018750205080273451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69654784679166803386848967 104482177018750205080273451)
          ·
            refine ⟨156723265528125307620410177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104482177018750205080273451 156723265528125307620410177)
            ·
              refine ⟨117542449146093980715307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156723265528125307620410177 117542449146093980715307633)
              ·
                refine ⟨88156836859570485536480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117542449146093980715307633 88156836859570485536480725)
                ·
                  refine ⟨2066175863896183254761267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88156836859570485536480725 2066175863896183254761267)
                  ·
                    refine ⟨3099263795844274882141901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066175863896183254761267 3099263795844274882141901)
                    ·
                      refine ⟨1162223923441603080803213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3099263795844274882141901 1162223923441603080803213)
                      ·
                        rfl

theorem cell23_2263423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_2263423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263423 prefixEnd_2263423 := by exact prefixLift 2263423
  have htrace : WordTrace (prefixWord ++ tailWord_2263423) baseStart_2263423 baseEnd_2263423 := by
    simpa [prefixWord, tailWord_2263423, baseEnd_2263423] using wordTrace_append hprefix tailTrace_2263423
  have hstable : (prefixWord ++ tailWord_2263423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263423).length < 2 ^ (prefixWord ++ tailWord_2263423).sum := by decide
  have hdescent : baseEnd_2263423 < baseStart_2263423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263450 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2263450 : Nat := 118140960795 + 2263450 * 2 ^ 59
def prefixEnd_2263450 : Nat := 4983230072969 + 3 ^ 40 * 2263450 * 2
def baseEnd_2263450 : Nat := 1162237787419274475165589

theorem tailTrace_2263450 : CollatzResearch.WordTrace tailWord_2263450 prefixEnd_2263450 1162237787419274475165589 := by
  unfold tailWord_2263450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638700912478672832244951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55036535766609794219319869 20638700912478672832244951)
  ·
    refine ⟨30958051368718009248367427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20638700912478672832244951 30958051368718009248367427)
    ·
      refine ⟨46437077053077013872551141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30958051368718009248367427 46437077053077013872551141)
      ·
        refine ⟨8706951947451940101103339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46437077053077013872551141 8706951947451940101103339)
        ·
          refine ⟨13060427921177910151655009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706951947451940101103339 13060427921177910151655009)
          ·
            refine ⟨9795320940883432613741257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13060427921177910151655009 9795320940883432613741257)
            ·
              refine ⟨7346490705662574460305943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9795320940883432613741257 7346490705662574460305943)
              ·
                refine ⟨11019736058493861690458915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346490705662574460305943 11019736058493861690458915)
                ·
                  refine ⟨16529604087740792535688373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11019736058493861690458915 16529604087740792535688373)
                  ·
                    refine ⟨1549650383225699300220785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16529604087740792535688373 1549650383225699300220785)
                    ·
                      refine ⟨1162237787419274475165589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549650383225699300220785 1162237787419274475165589)
                      ·
                        rfl

theorem cell23_2263450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2263450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263450 prefixEnd_2263450 := by exact prefixLift 2263450
  have htrace : WordTrace (prefixWord ++ tailWord_2263450) baseStart_2263450 baseEnd_2263450 := by
    simpa [prefixWord, tailWord_2263450, baseEnd_2263450] using wordTrace_append hprefix tailTrace_2263450
  have hstable : (prefixWord ++ tailWord_2263450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263450).length < 2 ^ (prefixWord ++ tailWord_2263450).sum := by decide
  have hdescent : baseEnd_2263450 < baseStart_2263450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263474 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_2263474 : Nat := 118140960795 + 2263474 * 2 ^ 59
def prefixEnd_2263474 : Nat := 4983230072969 + 3 ^ 40 * 2263474 * 2
def baseEnd_2263474 : Nat := 1162250110954982381265479

theorem tailTrace_2263474 : CollatzResearch.WordTrace tailWord_2263474 prefixEnd_2263474 1162250110954982381265479 := by
  unfold tailWord_2263474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638919750456935856963369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55037119334551828951902317 20638919750456935856963369)
  ·
    refine ⟨15479189812842701892722527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20638919750456935856963369 15479189812842701892722527)
    ·
      refine ⟨23218784719264052839083791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15479189812842701892722527 23218784719264052839083791)
      ·
        refine ⟨34828177078896079258625687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23218784719264052839083791 34828177078896079258625687)
        ·
          refine ⟨52242265618344118887938531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34828177078896079258625687 52242265618344118887938531)
          ·
            refine ⟨78363398427516178331907797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52242265618344118887938531 78363398427516178331907797)
            ·
              refine ⟨1836642150644910429654089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78363398427516178331907797 1836642150644910429654089)
              ·
                refine ⟨1377481612983682822240567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836642150644910429654089 1377481612983682822240567)
                ·
                  refine ⟨2066222419475524233360851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377481612983682822240567 2066222419475524233360851)
                  ·
                    refine ⟨3099333629213286350041277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066222419475524233360851 3099333629213286350041277)
                    ·
                      refine ⟨1162250110954982381265479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3099333629213286350041277 1162250110954982381265479)
                      ·
                        rfl

theorem cell23_2263474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_2263474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263474 prefixEnd_2263474 := by exact prefixLift 2263474
  have htrace : WordTrace (prefixWord ++ tailWord_2263474) baseStart_2263474 baseEnd_2263474 := by
    simpa [prefixWord, tailWord_2263474, baseEnd_2263474] using wordTrace_append hprefix tailTrace_2263474
  have hstable : (prefixWord ++ tailWord_2263474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263474).length < 2 ^ (prefixWord ++ tailWord_2263474).sum := by decide
  have hdescent : baseEnd_2263474 < baseStart_2263474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263514 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_2263514 : Nat := 118140960795 + 2263514 * 2 ^ 59
def prefixEnd_2263514 : Nat := 4983230072969 + 3 ^ 40 * 2263514 * 2
def baseEnd_2263514 : Nat := 1162270650181162224765295

theorem tailTrace_2263514 : CollatzResearch.WordTrace tailWord_2263514 prefixEnd_2263514 1162270650181162224765295 := by
  unfold tailWord_2263514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20639284480420707564827399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55038091947788553506206397 20639284480420707564827399)
  ·
    refine ⟨30958926720631061347241099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20639284480420707564827399 30958926720631061347241099)
    ·
      refine ⟨46438390080946592020861649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30958926720631061347241099 46438390080946592020861649)
      ·
        refine ⟨34828792560709944015646237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46438390080946592020861649 34828792560709944015646237)
        ·
          refine ⟨13060797210266229005867339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34828792560709944015646237 13060797210266229005867339)
          ·
            refine ⟨19591195815399343508801009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060797210266229005867339 19591195815399343508801009)
            ·
              refine ⟨14693396861549507631600757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19591195815399343508801009 14693396861549507631600757)
              ·
                refine ⟨1377505955770266340462571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14693396861549507631600757 1377505955770266340462571)
                ·
                  refine ⟨2066258933655399510693857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377505955770266340462571 2066258933655399510693857)
                  ·
                    refine ⟨1549694200241549633020393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066258933655399510693857 1549694200241549633020393)
                    ·
                      refine ⟨1162270650181162224765295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549694200241549633020393 1162270650181162224765295)
                      ·
                        rfl

theorem cell23_2263514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_2263514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263514 prefixEnd_2263514 := by exact prefixLift 2263514
  have htrace : WordTrace (prefixWord ++ tailWord_2263514) baseStart_2263514 baseEnd_2263514 := by
    simpa [prefixWord, tailWord_2263514, baseEnd_2263514] using wordTrace_append hprefix tailTrace_2263514
  have hstable : (prefixWord ++ tailWord_2263514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263514).length < 2 ^ (prefixWord ++ tailWord_2263514).sum := by decide
  have hdescent : baseEnd_2263514 < baseStart_2263514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263565 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2263565 : Nat := 118140960795 + 2263565 * 2 ^ 59
def prefixEnd_2263565 : Nat := 4983230072969 + 3 ^ 40 * 2263565 * 2
def baseEnd_2263565 : Nat := 1162296837694541525227561

theorem tailTrace_2263565 : CollatzResearch.WordTrace tailWord_2263565 prefixEnd_2263565 1162296837694541525227561 := by
  unfold tailWord_2263565
  simp only [CollatzResearch.WordTrace]
  refine ⟨82558998044498065969416149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55039332029665377312944099 82558998044498065969416149)
  ·
    refine ⟨1934976516667923421158191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82558998044498065969416149 1934976516667923421158191)
    ·
      refine ⟨2902464775001885131737287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934976516667923421158191 2902464775001885131737287)
      ·
        refine ⟨4353697162502827697605931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2902464775001885131737287 4353697162502827697605931)
        ·
          refine ⟨6530545743754241546408897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353697162502827697605931 6530545743754241546408897)
          ·
            refine ⟨4897909307815681159806673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530545743754241546408897 4897909307815681159806673)
            ·
              refine ⟨3673431980861760869855005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897909307815681159806673 3673431980861760869855005)
              ·
                refine ⟨1377536992823160326195627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3673431980861760869855005 1377536992823160326195627)
                ·
                  refine ⟨2066305489234740489293441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377536992823160326195627 2066305489234740489293441)
                  ·
                    refine ⟨1549729116926055366970081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066305489234740489293441 1549729116926055366970081)
                    ·
                      refine ⟨1162296837694541525227561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549729116926055366970081 1162296837694541525227561)
                      ·
                        rfl

theorem cell23_2263565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2263565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263565 prefixEnd_2263565 := by exact prefixLift 2263565
  have htrace : WordTrace (prefixWord ++ tailWord_2263565) baseStart_2263565 baseEnd_2263565 := by
    simpa [prefixWord, tailWord_2263565, baseEnd_2263565] using wordTrace_append hprefix tailTrace_2263565
  have hstable : (prefixWord ++ tailWord_2263565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263565).length < 2 ^ (prefixWord ++ tailWord_2263565).sum := by decide
  have hdescent : baseEnd_2263565 < baseStart_2263565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263573 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2263573 : Nat := 118140960795 + 2263573 * 2 ^ 59
def prefixEnd_2263573 : Nat := 4983230072969 + 3 ^ 40 * 2263573 * 2
def baseEnd_2263573 : Nat := 1162300945539777493927523

theorem tailTrace_2263573 : CollatzResearch.WordTrace tailWord_2263573 prefixEnd_2263573 1162300945539777493927523 := by
  unfold tailWord_2263573
  simp only [CollatzResearch.WordTrace]
  refine ⟨82559289828469083335707373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55039526552312722223804915 82559289828469083335707373)
  ·
    refine ⟨30959733685675906250890265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82559289828469083335707373 30959733685675906250890265)
    ·
      refine ⟨23219800264256929688167699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30959733685675906250890265 23219800264256929688167699)
      ·
        refine ⟨34829700396385394532251549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219800264256929688167699 34829700396385394532251549)
        ·
          refine ⟨13061137648644522949594331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34829700396385394532251549 13061137648644522949594331)
          ·
            refine ⟨19591706472966784424391497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13061137648644522949594331 19591706472966784424391497)
            ·
              refine ⟨14693779854725088318293623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19591706472966784424391497 14693779854725088318293623)
              ·
                refine ⟨22040669782087632477440435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14693779854725088318293623 22040669782087632477440435)
                ·
                  refine ⟨33061004673131448716160653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22040669782087632477440435 33061004673131448716160653)
                  ·
                    refine ⟨12397876752424293268560245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33061004673131448716160653 12397876752424293268560245)
                    ·
                      refine ⟨1162300945539777493927523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12397876752424293268560245 1162300945539777493927523)
                      ·
                        rfl

theorem cell23_2263573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2263573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263573 prefixEnd_2263573 := by exact prefixLift 2263573
  have htrace : WordTrace (prefixWord ++ tailWord_2263573) baseStart_2263573 baseEnd_2263573 := by
    simpa [prefixWord, tailWord_2263573, baseEnd_2263573] using wordTrace_append hprefix tailTrace_2263573
  have hstable : (prefixWord ++ tailWord_2263573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263573).length < 2 ^ (prefixWord ++ tailWord_2263573).sum := by decide
  have hdescent : baseEnd_2263573 < baseStart_2263573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263644 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 7]
def baseStart_2263644 : Nat := 118140960795 + 2263644 * 2 ^ 59
def prefixEnd_2263644 : Nat := 4983230072969 + 3 ^ 40 * 2263644 * 2
def baseEnd_2263644 : Nat := 129148600296249635126633

theorem tailTrace_2263644 : CollatzResearch.WordTrace tailWord_2263644 prefixEnd_2263644 129148600296249635126633 := by
  unfold tailWord_2263644
  simp only [CollatzResearch.WordTrace]
  refine ⟨41280939705605931230770993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55041252940807908307694657 41280939705605931230770993)
  ·
    refine ⟨30960704779204448423078245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41280939705605931230770993 30960704779204448423078245)
    ·
      refine ⟨5805132146100834079327171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30960704779204448423078245 5805132146100834079327171)
      ·
        refine ⟨8707698219151251118990757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805132146100834079327171 8707698219151251118990757)
        ·
          refine ⟨1632693416090859584810767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8707698219151251118990757 1632693416090859584810767)
          ·
            refine ⟨2449040124136289377216151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632693416090859584810767 2449040124136289377216151)
            ·
              refine ⟨3673560186204434065824227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449040124136289377216151 3673560186204434065824227)
              ·
                refine ⟨5510340279306651098736341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673560186204434065824227 5510340279306651098736341)
                ·
                  refine ⟨129148600296249635126633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5510340279306651098736341 129148600296249635126633)
                  ·
                    rfl

theorem cell23_2263644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_2263644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263644 prefixEnd_2263644 := by exact prefixLift 2263644
  have htrace : WordTrace (prefixWord ++ tailWord_2263644) baseStart_2263644 baseEnd_2263644 := by
    simpa [prefixWord, tailWord_2263644, baseEnd_2263644] using wordTrace_append hprefix tailTrace_2263644
  have hstable : (prefixWord ++ tailWord_2263644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263644).length < 2 ^ (prefixWord ++ tailWord_2263644).sum := by decide
  have hdescent : baseEnd_2263644 < baseStart_2263644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263683 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 10]
def baseStart_2263683 : Nat := 118140960795 + 2263683 * 2 ^ 59
def prefixEnd_2263683 : Nat := 4983230072969 + 3 ^ 40 * 2263683 * 2
def baseEnd_2263683 : Nat := 129150825379085784839113

theorem tailTrace_2263683 : CollatzResearch.WordTrace tailWord_2263683 prefixEnd_2263683 129150825379085784839113 := by
  unfold tailWord_2263683
  simp only [CollatzResearch.WordTrace]
  refine ⟨82563301858070572122211703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55042201238713714748141135 82563301858070572122211703)
  ·
    refine ⟨123844952787105858183317555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82563301858070572122211703 123844952787105858183317555)
    ·
      refine ⟨185767429180658787274976333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123844952787105858183317555 185767429180658787274976333)
      ·
        refine ⟨69662785942747045228116125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185767429180658787274976333 69662785942747045228116125)
        ·
          refine ⟨26123544728530141960543547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69662785942747045228116125 26123544728530141960543547)
          ·
            refine ⟨39185317092795212940815321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26123544728530141960543547 39185317092795212940815321)
            ·
              refine ⟨29388987819596409705611491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39185317092795212940815321 29388987819596409705611491)
              ·
                refine ⟨44083481729394614558417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29388987819596409705611491 44083481729394614558417237)
                ·
                  refine ⟨129150825379085784839113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44083481729394614558417237 129150825379085784839113)
                  ·
                    rfl

theorem cell23_2263683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 10].length) (baseStart_2263683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263683 prefixEnd_2263683 := by exact prefixLift 2263683
  have htrace : WordTrace (prefixWord ++ tailWord_2263683) baseStart_2263683 baseEnd_2263683 := by
    simpa [prefixWord, tailWord_2263683, baseEnd_2263683] using wordTrace_append hprefix tailTrace_2263683
  have hstable : (prefixWord ++ tailWord_2263683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263683).length < 2 ^ (prefixWord ++ tailWord_2263683).sum := by decide
  have hdescent : baseEnd_2263683 < baseStart_2263683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263704 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 1, 4]
def baseStart_2263704 : Nat := 118140960795 + 2263704 * 2 ^ 59
def prefixEnd_2263704 : Nat := 4983230072969 + 3 ^ 40 * 2263704 * 2
def baseEnd_2263704 : Nat := 387456070501838827129807

theorem tailTrace_2263704 : CollatzResearch.WordTrace tailWord_2263704 prefixEnd_2263704 387456070501838827129807 := by
  unfold tailWord_2263704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41282033895497246354363083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55042711860662995139150777 41282033895497246354363083)
  ·
    refine ⟨61923050843245869531544625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41282033895497246354363083 61923050843245869531544625)
    ·
      refine ⟨46442288132434402148658469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61923050843245869531544625 46442288132434402148658469)
      ·
        refine ⟨8707929024831450402873463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46442288132434402148658469 8707929024831450402873463)
        ·
          refine ⟨13061893537247175604310195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8707929024831450402873463 13061893537247175604310195)
          ·
            refine ⟨19592840305870763406465293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13061893537247175604310195 19592840305870763406465293)
            ·
              refine ⟨7347315114701536277424485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19592840305870763406465293 7347315114701536277424485)
              ·
                refine ⟨1377621584006538052017091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7347315114701536277424485 1377621584006538052017091)
                ·
                  refine ⟨2066432376009807078025637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377621584006538052017091 2066432376009807078025637)
                  ·
                    refine ⟨387456070501838827129807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066432376009807078025637 387456070501838827129807)
                    ·
                      rfl

theorem cell23_2263704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_2263704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263704 prefixEnd_2263704 := by exact prefixLift 2263704
  have htrace : WordTrace (prefixWord ++ tailWord_2263704) baseStart_2263704 baseEnd_2263704 := by
    simpa [prefixWord, tailWord_2263704, baseEnd_2263704] using wordTrace_append hprefix tailTrace_2263704
  have hstable : (prefixWord ++ tailWord_2263704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263704).length < 2 ^ (prefixWord ++ tailWord_2263704).sum := by decide
  have hdescent : baseEnd_2263704 < baseStart_2263704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263727 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_2263727 : Nat := 118140960795 + 2263727 * 2 ^ 59
def prefixEnd_2263727 : Nat := 4983230072969 + 3 ^ 40 * 2263727 * 2
def baseEnd_2263727 : Nat := 1162380021560569891401815

theorem tailTrace_2263727 : CollatzResearch.WordTrace tailWord_2263727 prefixEnd_2263727 1162380021560569891401815 := by
  unfold tailWord_2263727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82564906669911167636813435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55043271113274111757875623 82564906669911167636813435)
  ·
    refine ⟨123847360004866751455220153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82564906669911167636813435 123847360004866751455220153)
    ·
      refine ⟨92885520003650063591415115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123847360004866751455220153 92885520003650063591415115)
      ·
        refine ⟨139328280005475095387122673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92885520003650063591415115 139328280005475095387122673)
        ·
          refine ⟨104496210004106321540342005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139328280005475095387122673 104496210004106321540342005)
          ·
            refine ⟨9796519687884967644407063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104496210004106321540342005 9796519687884967644407063)
            ·
              refine ⟨14694779531827451466610595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9796519687884967644407063 14694779531827451466610595)
              ·
                refine ⟨22042169297741177199915893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14694779531827451466610595 22042169297741177199915893)
                ·
                  refine ⟨2066453371663235362492115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22042169297741177199915893 2066453371663235362492115)
                  ·
                    refine ⟨3099680057494853043738173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066453371663235362492115 3099680057494853043738173)
                    ·
                      refine ⟨1162380021560569891401815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3099680057494853043738173 1162380021560569891401815)
                      ·
                        rfl

theorem cell23_2263727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_2263727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263727 prefixEnd_2263727 := by exact prefixLift 2263727
  have htrace : WordTrace (prefixWord ++ tailWord_2263727) baseStart_2263727 baseEnd_2263727 := by
    simpa [prefixWord, tailWord_2263727, baseEnd_2263727] using wordTrace_append hprefix tailTrace_2263727
  have hstable : (prefixWord ++ tailWord_2263727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263727).length < 2 ^ (prefixWord ++ tailWord_2263727).sum := by decide
  have hdescent : baseEnd_2263727 < baseStart_2263727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263777 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2263777 : Nat := 118140960795 + 2263777 * 2 ^ 59
def prefixEnd_2263777 : Nat := 4983230072969 + 3 ^ 40 * 2263777 * 2
def baseEnd_2263777 : Nat := 387468565197764898592195

theorem tailTrace_2263777 : CollatzResearch.WordTrace tailWord_2263777 prefixEnd_2263777 387468565197764898592195 := by
  unfold tailWord_2263777
  simp only [CollatzResearch.WordTrace]
  refine ⟨82566730319730026176133585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55044486879820017450755723 82566730319730026176133585)
  ·
    refine ⟨61925047739797519632100189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82566730319730026176133585 61925047739797519632100189)
    ·
      refine ⟨23221892902424069862037571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61925047739797519632100189 23221892902424069862037571)
      ·
        refine ⟨34832839353636104793056357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23221892902424069862037571 34832839353636104793056357)
        ·
          refine ⟨6531157378806769648698067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34832839353636104793056357 6531157378806769648698067)
          ·
            refine ⟨9796736068210154473047101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531157378806769648698067 9796736068210154473047101)
            ·
              refine ⟨3673776025578807927392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9796736068210154473047101 3673776025578807927392663)
              ·
                refine ⟨5510664038368211891088995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673776025578807927392663 5510664038368211891088995)
                ·
                  refine ⟨8265996057552317836633493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5510664038368211891088995 8265996057552317836633493)
                  ·
                    refine ⟨387468565197764898592195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8265996057552317836633493 387468565197764898592195)
                    ·
                      rfl

theorem cell23_2263777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2263777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263777 prefixEnd_2263777 := by exact prefixLift 2263777
  have htrace : WordTrace (prefixWord ++ tailWord_2263777) baseStart_2263777 baseEnd_2263777 := by
    simpa [prefixWord, tailWord_2263777, baseEnd_2263777] using wordTrace_append hprefix tailTrace_2263777
  have hstable : (prefixWord ++ tailWord_2263777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263777).length < 2 ^ (prefixWord ++ tailWord_2263777).sum := by decide
  have hdescent : baseEnd_2263777 < baseStart_2263777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263804 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_2263804 : Nat := 118140960795 + 2263804 * 2 ^ 59
def prefixEnd_2263804 : Nat := 4983230072969 + 3 ^ 40 * 2263804 * 2
def baseEnd_2263804 : Nat := 1162419559570966090138961

theorem tailTrace_2263804 : CollatzResearch.WordTrace tailWord_2263804 prefixEnd_2263804 1162419559570966090138961 := by
  unfold tailWord_2263804
  simp only [CollatzResearch.WordTrace]
  refine ⟨41283857545316104893683233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55045143393754806524910977 41283857545316104893683233)
  ·
    refine ⟨30962893158987078670262425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41283857545316104893683233 30962893158987078670262425)
    ·
      refine ⟨23222169869240309002696819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30962893158987078670262425 23222169869240309002696819)
      ·
        refine ⟨34833254803860463504045229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23222169869240309002696819 34833254803860463504045229)
        ·
          refine ⟨13062470551447673814016961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34833254803860463504045229 13062470551447673814016961)
          ·
            refine ⟨9796852913585755360512721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13062470551447673814016961 9796852913585755360512721)
            ·
              refine ⟨7347639685189316520384541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9796852913585755360512721 7347639685189316520384541)
              ·
                refine ⟨2755364881945993695144203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7347639685189316520384541 2755364881945993695144203)
                ·
                  refine ⟨4133047322918990542716305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755364881945993695144203 4133047322918990542716305)
                  ·
                    refine ⟨3099785492189242907037229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133047322918990542716305 3099785492189242907037229)
                    ·
                      refine ⟨1162419559570966090138961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3099785492189242907037229 1162419559570966090138961)
                      ·
                        rfl

theorem cell23_2263804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_2263804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263804 prefixEnd_2263804 := by exact prefixLift 2263804
  have htrace : WordTrace (prefixWord ++ tailWord_2263804) baseStart_2263804 baseEnd_2263804 := by
    simpa [prefixWord, tailWord_2263804, baseEnd_2263804] using wordTrace_append hprefix tailTrace_2263804
  have hstable : (prefixWord ++ tailWord_2263804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263804).length < 2 ^ (prefixWord ++ tailWord_2263804).sum := by decide
  have hdescent : baseEnd_2263804 < baseStart_2263804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263820 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_2263820 : Nat := 118140960795 + 2263820 * 2 ^ 59
def prefixEnd_2263820 : Nat := 4983230072969 + 3 ^ 40 * 2263820 * 2
def baseEnd_2263820 : Nat := 387475925087146009179629

theorem tailTrace_2263820 : CollatzResearch.WordTrace tailWord_2263820 prefixEnd_2263820 387475925087146009179629 := by
  unfold tailWord_2263820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41284149329287122259974457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55045532439049496346632609 41284149329287122259974457)
  ·
    refine ⟨30963111996965341694980843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41284149329287122259974457 30963111996965341694980843)
    ·
      refine ⟨46444667995448012542471265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30963111996965341694980843 46444667995448012542471265)
      ·
        refine ⟨34833500996586009406853449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46444667995448012542471265 34833500996586009406853449)
        ·
          refine ⟨26125125747439507055140087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34833500996586009406853449 26125125747439507055140087)
          ·
            refine ⟨39187688621159260582710131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26125125747439507055140087 39187688621159260582710131)
            ·
              refine ⟨58781532931738890874065197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39187688621159260582710131 58781532931738890874065197)
              ·
                refine ⟨22043074849402084077774449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58781532931738890874065197 22043074849402084077774449)
                ·
                  refine ⟨16532306137051563058330837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22043074849402084077774449 16532306137051563058330837)
                  ·
                    refine ⟨387475925087146009179629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16532306137051563058330837 387475925087146009179629)
                    ·
                      rfl

theorem cell23_2263820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_2263820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263820 prefixEnd_2263820 := by exact prefixLift 2263820
  have htrace : WordTrace (prefixWord ++ tailWord_2263820) baseStart_2263820 baseEnd_2263820 := by
    simpa [prefixWord, tailWord_2263820, baseEnd_2263820] using wordTrace_append hprefix tailTrace_2263820
  have hstable : (prefixWord ++ tailWord_2263820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263820).length < 2 ^ (prefixWord ++ tailWord_2263820).sum := by decide
  have hdescent : baseEnd_2263820 < baseStart_2263820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263869 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2263869 : Nat := 118140960795 + 2263869 * 2 ^ 59
def prefixEnd_2263869 : Nat := 4983230072969 + 3 ^ 40 * 2263869 * 2
def baseEnd_2263869 : Nat := 1162452935813508335826163

theorem tailTrace_2263869 : CollatzResearch.WordTrace tailWord_2263869 prefixEnd_2263869 1162452935813508335826163 := by
  unfold tailWord_2263869
  simp only [CollatzResearch.WordTrace]
  refine ⟨82570085835396725888482661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55046723890264483925655107 82570085835396725888482661)
  ·
    refine ⟨15481891094136886104090499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82570085835396725888482661 15481891094136886104090499)
    ·
      refine ⟨23222836641205329156135749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15481891094136886104090499 23222836641205329156135749)
      ·
        refine ⟨4354281870225999216775453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23222836641205329156135749 4354281870225999216775453)
        ·
          refine ⟨1632855701334749706290795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4354281870225999216775453 1632855701334749706290795)
          ·
            refine ⟨2449283552002124559436193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632855701334749706290795 2449283552002124559436193)
            ·
              refine ⟨1836962664001593419577145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449283552002124559436193 1836962664001593419577145)
              ·
                refine ⟨1377721998001195064682859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836962664001593419577145 1377721998001195064682859)
                ·
                  refine ⟨2066582997001792597024289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377721998001195064682859 2066582997001792597024289)
                  ·
                    refine ⟨1549937247751344447768217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066582997001792597024289 1549937247751344447768217)
                    ·
                      refine ⟨1162452935813508335826163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549937247751344447768217 1162452935813508335826163)
                      ·
                        rfl

theorem cell23_2263869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2263869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263869 prefixEnd_2263869 := by exact prefixLift 2263869
  have htrace : WordTrace (prefixWord ++ tailWord_2263869) baseStart_2263869 baseEnd_2263869 := by
    simpa [prefixWord, tailWord_2263869, baseEnd_2263869] using wordTrace_append hprefix tailTrace_2263869
  have hstable : (prefixWord ++ tailWord_2263869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263869).length < 2 ^ (prefixWord ++ tailWord_2263869).sum := by decide
  have hdescent : baseEnd_2263869 < baseStart_2263869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263897 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 7]
def baseStart_2263897 : Nat := 118140960795 + 2263897 * 2 ^ 59
def prefixEnd_2263897 : Nat := 4983230072969 + 3 ^ 40 * 2263897 * 2
def baseEnd_2263897 : Nat := 129163034807981580697337

theorem tailTrace_2263897 : CollatzResearch.WordTrace tailWord_2263897 prefixEnd_2263897 129163034807981580697337 := by
  unfold tailWord_2263897
  simp only [CollatzResearch.WordTrace]
  refine ⟨82571107079295286670501945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55047404719530191113667963 82571107079295286670501945)
  ·
    refine ⟨61928330309471465002876459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82571107079295286670501945 61928330309471465002876459)
    ·
      refine ⟨92892495464207197504314689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61928330309471465002876459 92892495464207197504314689)
      ·
        refine ⟨69669371598155398128236017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92892495464207197504314689 69669371598155398128236017)
        ·
          refine ⟨52252028698616548596177013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69669371598155398128236017 52252028698616548596177013)
          ·
            refine ⟨4898627690495301430891595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52252028698616548596177013 4898627690495301430891595)
            ·
              refine ⟨7347941535742952146337393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898627690495301430891595 7347941535742952146337393)
              ·
                refine ⟨5510956151807214109753045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7347941535742952146337393 5510956151807214109753045)
                ·
                  refine ⟨129163034807981580697337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5510956151807214109753045 129163034807981580697337)
                  ·
                    rfl

theorem cell23_2263897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_2263897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263897 prefixEnd_2263897 := by exact prefixLift 2263897
  have htrace : WordTrace (prefixWord ++ tailWord_2263897) baseStart_2263897 baseEnd_2263897 := by
    simpa [prefixWord, tailWord_2263897, baseEnd_2263897] using wordTrace_append hprefix tailTrace_2263897
  have hstable : (prefixWord ++ tailWord_2263897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263897).length < 2 ^ (prefixWord ++ tailWord_2263897).sum := by decide
  have hdescent : baseEnd_2263897 < baseStart_2263897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263925 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2263925 : Nat := 118140960795 + 2263925 * 2 ^ 59
def prefixEnd_2263925 : Nat := 4983230072969 + 3 ^ 40 * 2263925 * 2
def baseEnd_2263925 : Nat := 1162481690730160116725905

theorem tailTrace_2263925 : CollatzResearch.WordTrace tailWord_2263925 prefixEnd_2263925 1162481690730160116725905 := by
  unfold tailWord_2263925
  simp only [CollatzResearch.WordTrace]
  refine ⟨82572128323193847452521229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55048085548795898301680819 82572128323193847452521229)
  ·
    refine ⟨30964548121197692794695461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82572128323193847452521229 30964548121197692794695461)
    ·
      refine ⟨5805852772724567399005399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30964548121197692794695461 5805852772724567399005399)
      ·
        refine ⟨8708779159086851098508099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805852772724567399005399 8708779159086851098508099)
        ·
          refine ⟨13063168738630276647762149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8708779159086851098508099 13063168738630276647762149)
          ·
            refine ⟨2449344138493176871455403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13063168738630276647762149 2449344138493176871455403)
            ·
              refine ⟨3674016207739765307183105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449344138493176871455403 3674016207739765307183105)
              ·
                refine ⟨2755512155804823980387329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674016207739765307183105 2755512155804823980387329)
                ·
                  refine ⟨2066634116853617985290497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755512155804823980387329 2066634116853617985290497)
                  ·
                    refine ⟨1549975587640213488967873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2066634116853617985290497 1549975587640213488967873)
                    ·
                      refine ⟨1162481690730160116725905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1549975587640213488967873 1162481690730160116725905)
                      ·
                        rfl

theorem cell23_2263925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2263925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263925 prefixEnd_2263925 := by exact prefixLift 2263925
  have htrace : WordTrace (prefixWord ++ tailWord_2263925) baseStart_2263925 baseEnd_2263925 := by
    simpa [prefixWord, tailWord_2263925, baseEnd_2263925] using wordTrace_append hprefix tailTrace_2263925
  have hstable : (prefixWord ++ tailWord_2263925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263925).length < 2 ^ (prefixWord ++ tailWord_2263925).sum := by decide
  have hdescent : baseEnd_2263925 < baseStart_2263925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263927 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 2, 5]
def baseStart_2263927 : Nat := 118140960795 + 2263927 * 2 ^ 59
def prefixEnd_2263927 : Nat := 4983230072969 + 3 ^ 40 * 2263927 * 2
def baseEnd_2263927 : Nat := 387494239230489702966965

theorem tailTrace_2263927 : CollatzResearch.WordTrace tailWord_2263927 prefixEnd_2263927 387494239230489702966965 := by
  unfold tailWord_2263927
  simp only [CollatzResearch.WordTrace]
  refine ⟨82572201269186601794094035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55048134179457734529396023 82572201269186601794094035)
  ·
    refine ⟨123858301903779902691141053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82572201269186601794094035 123858301903779902691141053)
    ·
      refine ⟨46446863213917463509177895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123858301903779902691141053 46446863213917463509177895)
      ·
        refine ⟨69670294820876195263766843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46446863213917463509177895 69670294820876195263766843)
        ·
          refine ⟨104505442231314292895650265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69670294820876195263766843 104505442231314292895650265)
          ·
            refine ⟨78379081673485719671737699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104505442231314292895650265 78379081673485719671737699)
            ·
              refine ⟨117568622510228579507606549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78379081673485719671737699 117568622510228579507606549)
              ·
                refine ⟨5511029180166964664419057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117568622510228579507606549 5511029180166964664419057)
                ·
                  refine ⟨4133271885125223498314293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511029180166964664419057 4133271885125223498314293)
                  ·
                    refine ⟨387494239230489702966965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4133271885125223498314293 387494239230489702966965)
                    ·
                      rfl

theorem cell23_2263927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_2263927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263927 prefixEnd_2263927 := by exact prefixLift 2263927
  have htrace : WordTrace (prefixWord ++ tailWord_2263927) baseStart_2263927 baseEnd_2263927 := by
    simpa [prefixWord, tailWord_2263927, baseEnd_2263927] using wordTrace_append hprefix tailTrace_2263927
  have hstable : (prefixWord ++ tailWord_2263927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263927).length < 2 ^ (prefixWord ++ tailWord_2263927).sum := by decide
  have hdescent : baseEnd_2263927 < baseStart_2263927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263947 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_2263947 : Nat := 118140960795 + 2263947 * 2 ^ 59
def prefixEnd_2263947 : Nat := 4983230072969 + 3 ^ 40 * 2263947 * 2
def baseEnd_2263947 : Nat := 1162492987304559030650803

theorem tailTrace_2263947 : CollatzResearch.WordTrace tailWord_2263947 prefixEnd_2263947 1162492987304559030650803 := by
  unfold tailWord_2263947
  simp only [CollatzResearch.WordTrace]
  refine ⟨82572930729114145209822095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55048620486076096806548063 82572930729114145209822095)
  ·
    refine ⟨123859396093671217814733143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82572930729114145209822095 123859396093671217814733143)
    ·
      refine ⟨185789094140506826722099715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123859396093671217814733143 185789094140506826722099715)
      ·
        refine ⟨278683641210760240083149573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185789094140506826722099715 278683641210760240083149573)
        ·
          refine ⟨52253182727017545015590545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278683641210760240083149573 52253182727017545015590545)
          ·
            refine ⟨39189887045263158761692909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52253182727017545015590545 39189887045263158761692909)
            ·
              refine ⟨14696207641973684535634841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39189887045263158761692909 14696207641973684535634841)
              ·
                refine ⟨11022155731480263401726131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14696207641973684535634841 11022155731480263401726131)
                ·
                  refine ⟨16533233597220395102589197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11022155731480263401726131 16533233597220395102589197)
                  ·
                    refine ⟨6199962598957648163470949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16533233597220395102589197 6199962598957648163470949)
                    ·
                      refine ⟨1162492987304559030650803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6199962598957648163470949 1162492987304559030650803)
                      ·
                        rfl

theorem cell23_2263947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_2263947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263947 prefixEnd_2263947 := by exact prefixLift 2263947
  have htrace : WordTrace (prefixWord ++ tailWord_2263947) baseStart_2263947 baseEnd_2263947 := by
    simpa [prefixWord, tailWord_2263947, baseEnd_2263947] using wordTrace_append hprefix tailTrace_2263947
  have hstable : (prefixWord ++ tailWord_2263947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263947).length < 2 ^ (prefixWord ++ tailWord_2263947).sum := by decide
  have hdescent : baseEnd_2263947 < baseStart_2263947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263991 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 1, 4]
def baseStart_2263991 : Nat := 118140960795 + 2263991 * 2 ^ 59
def prefixEnd_2263991 : Nat := 4983230072969 + 3 ^ 40 * 2263991 * 2
def baseEnd_2263991 : Nat := 387505193484452286166867

theorem tailTrace_2263991 : CollatzResearch.WordTrace tailWord_2263991 prefixEnd_2263991 387505193484452286166867 := by
  unfold tailWord_2263991
  simp only [CollatzResearch.WordTrace]
  refine ⟨82574535540954740724423827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55049690360636493816282551 82574535540954740724423827)
  ·
    refine ⟨123861803311432111086635741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82574535540954740724423827 123861803311432111086635741)
    ·
      refine ⟨46448176241787041657488403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123861803311432111086635741 46448176241787041657488403)
      ·
        refine ⟨69672264362680562486232605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46448176241787041657488403 69672264362680562486232605)
        ·
          refine ⟨26127099136005210932337227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69672264362680562486232605 26127099136005210932337227)
          ·
            refine ⟨39190648704007816398505841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26127099136005210932337227 39190648704007816398505841)
            ·
              refine ⟨29392986528005862298879381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39190648704007816398505841 29392986528005862298879381)
              ·
                refine ⟨1377796243500274795259971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29392986528005862298879381 1377796243500274795259971)
                ·
                  refine ⟨2066694365250412192889957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377796243500274795259971 2066694365250412192889957)
                  ·
                    refine ⟨387505193484452286166867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066694365250412192889957 387505193484452286166867)
                    ·
                      rfl

theorem cell23_2263991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_2263991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2263991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2263991 prefixEnd_2263991 := by exact prefixLift 2263991
  have htrace : WordTrace (prefixWord ++ tailWord_2263991) baseStart_2263991 baseEnd_2263991 := by
    simpa [prefixWord, tailWord_2263991, baseEnd_2263991] using wordTrace_append hprefix tailTrace_2263991
  have hstable : (prefixWord ++ tailWord_2263991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263991).length < 2 ^ (prefixWord ++ tailWord_2263991).sum := by decide
  have hdescent : baseEnd_2263991 < baseStart_2263991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264007 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2264007 : Nat := 118140960795 + 2264007 * 2 ^ 59
def prefixEnd_2264007 : Nat := 4983230072969 + 3 ^ 40 * 2264007 * 2
def baseEnd_2264007 : Nat := 1162523796143828795900527

theorem tailTrace_2264007 : CollatzResearch.WordTrace tailWord_2264007 prefixEnd_2264007 1162523796143828795900527 := by
  unfold tailWord_2264007
  simp only [CollatzResearch.WordTrace]
  refine ⟨82575119108896775457006275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55050079405931183638004183 82575119108896775457006275)
  ·
    refine ⟨123862678663345163185509413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82575119108896775457006275 123862678663345163185509413)
    ·
      refine ⟨23224252249377218097283015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123862678663345163185509413 23224252249377218097283015)
      ·
        refine ⟨34836378374065827145924523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23224252249377218097283015 34836378374065827145924523)
        ·
          refine ⟨52254567561098740718886785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34836378374065827145924523 52254567561098740718886785)
          ·
            refine ⟨39190925670824055539165089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52254567561098740718886785 39190925670824055539165089)
            ·
              refine ⟨29393194253118041654373817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39190925670824055539165089 29393194253118041654373817)
              ·
                refine ⟨22044895689838531240780363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29393194253118041654373817 22044895689838531240780363)
                ·
                  refine ⟨33067343534757796861170545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22044895689838531240780363 33067343534757796861170545)
                  ·
                    refine ⟨24800507651068347645877909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33067343534757796861170545 24800507651068347645877909)
                    ·
                      refine ⟨1162523796143828795900527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24800507651068347645877909 1162523796143828795900527)
                      ·
                        rfl

theorem cell23_2264007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2264007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264007 prefixEnd_2264007 := by exact prefixLift 2264007
  have htrace : WordTrace (prefixWord ++ tailWord_2264007) baseStart_2264007 baseEnd_2264007 := by
    simpa [prefixWord, tailWord_2264007, baseEnd_2264007] using wordTrace_append hprefix tailTrace_2264007
  have hstable : (prefixWord ++ tailWord_2264007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264007).length < 2 ^ (prefixWord ++ tailWord_2264007).sum := by decide
  have hdescent : baseEnd_2264007 < baseStart_2264007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264018 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2264018 : Nat := 118140960795 + 2264018 * 2 ^ 59
def prefixEnd_2264018 : Nat := 4983230072969 + 3 ^ 40 * 2264018 * 2
def baseEnd_2264018 : Nat := 1162529444431028252862977

theorem tailTrace_2264018 : CollatzResearch.WordTrace tailWord_2264018 prefixEnd_2264018 1162529444431028252862977 := by
  unfold tailWord_2264018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20643880077964231083914177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55050346874571282890437805 20643880077964231083914177)
  ·
    refine ⟨15482910058473173312935633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20643880077964231083914177 15482910058473173312935633)
    ·
      refine ⟨11612182543854879984701725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15482910058473173312935633 11612182543854879984701725)
      ·
        refine ⟨4354568453945579994263147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11612182543854879984701725 4354568453945579994263147)
        ·
          refine ⟨6531852680918369991394721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354568453945579994263147 6531852680918369991394721)
          ·
            refine ⟨4898889510688777493546041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531852680918369991394721 4898889510688777493546041)
            ·
              refine ⟨3674167133016583120159531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4898889510688777493546041 3674167133016583120159531)
              ·
                refine ⟨5511250699524874680239297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674167133016583120159531 5511250699524874680239297)
                ·
                  refine ⟨4133438024643656010179473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511250699524874680239297 4133438024643656010179473)
                  ·
                    refine ⟨3100078518482742007634605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133438024643656010179473 3100078518482742007634605)
                    ·
                      refine ⟨1162529444431028252862977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3100078518482742007634605 1162529444431028252862977)
                      ·
                        rfl

theorem cell23_2264018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2264018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264018 prefixEnd_2264018 := by exact prefixLift 2264018
  have htrace : WordTrace (prefixWord ++ tailWord_2264018) baseStart_2264018 baseEnd_2264018 := by
    simpa [prefixWord, tailWord_2264018, baseEnd_2264018] using wordTrace_append hprefix tailTrace_2264018
  have hstable : (prefixWord ++ tailWord_2264018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264018).length < 2 ^ (prefixWord ++ tailWord_2264018).sum := by decide
  have hdescent : baseEnd_2264018 < baseStart_2264018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264071 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2264071 : Nat := 118140960795 + 2264071 * 2 ^ 59
def prefixEnd_2264071 : Nat := 4983230072969 + 3 ^ 40 * 2264071 * 2
def baseEnd_2264071 : Nat := 1162556658905716545500233

theorem tailTrace_2264071 : CollatzResearch.WordTrace tailWord_2264071 prefixEnd_2264071 1162556658905716545500233 := by
  unfold tailWord_2264071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82577453380664914387336067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55051635587109942924890711 82577453380664914387336067)
  ·
    refine ⟨123866180070997371581004101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82577453380664914387336067 123866180070997371581004101)
    ·
      refine ⟨23224908763312007171438269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123866180070997371581004101 23224908763312007171438269)
      ·
        refine ⟨8709340786242002689289351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23224908763312007171438269 8709340786242002689289351)
        ·
          refine ⟨13064011179363004033934027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709340786242002689289351 13064011179363004033934027)
          ·
            refine ⟨19596016769044506050901041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13064011179363004033934027 19596016769044506050901041)
            ·
              refine ⟨14697012576783379538175781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19596016769044506050901041 14697012576783379538175781)
              ·
                refine ⟨2755689858146883663407959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14697012576783379538175781 2755689858146883663407959)
                ·
                  refine ⟨4133534787220325495111939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755689858146883663407959 4133534787220325495111939)
                  ·
                    refine ⟨6200302180830488242667909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133534787220325495111939 6200302180830488242667909)
                    ·
                      refine ⟨1162556658905716545500233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6200302180830488242667909 1162556658905716545500233)
                      ·
                        rfl

theorem cell23_2264071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2264071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264071 prefixEnd_2264071 := by exact prefixLift 2264071
  have htrace : WordTrace (prefixWord ++ tailWord_2264071) baseStart_2264071 baseEnd_2264071 := by
    simpa [prefixWord, tailWord_2264071, baseEnd_2264071] using wordTrace_append hprefix tailTrace_2264071
  have hstable : (prefixWord ++ tailWord_2264071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264071).length < 2 ^ (prefixWord ++ tailWord_2264071).sum := by decide
  have hdescent : baseEnd_2264071 < baseStart_2264071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264088 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2264088 : Nat := 118140960795 + 2264088 * 2 ^ 59
def prefixEnd_2264088 : Nat := 4983230072969 + 3 ^ 40 * 2264088 * 2
def baseEnd_2264088 : Nat := 1162565388076842978987655

theorem tailTrace_2264088 : CollatzResearch.WordTrace tailWord_2264088 prefixEnd_2264088 1162565388076842978987655 := by
  unfold tailWord_2264088
  simp only [CollatzResearch.WordTrace]
  refine ⟨41289036710801663145352459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55052048947735550860469945 41289036710801663145352459)
  ·
    refine ⟨61933555066202494718028689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41289036710801663145352459 61933555066202494718028689)
    ·
      refine ⟨46450166299651871038521517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61933555066202494718028689 46450166299651871038521517)
      ·
        refine ⟨17418812362369451639445569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46450166299651871038521517 17418812362369451639445569)
        ·
          refine ⟨13064109271777088729584177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17418812362369451639445569 13064109271777088729584177)
          ·
            refine ⟨9798081953832816547188133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064109271777088729584177 9798081953832816547188133)
            ·
              refine ⟨1837140366343653102597775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9798081953832816547188133 1837140366343653102597775)
              ·
                refine ⟨2755710549515479653896663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837140366343653102597775 2755710549515479653896663)
                ·
                  refine ⟨4133565824273219480844995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755710549515479653896663 4133565824273219480844995)
                  ·
                    refine ⟨6200348736409829221267493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133565824273219480844995 6200348736409829221267493)
                    ·
                      refine ⟨1162565388076842978987655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6200348736409829221267493 1162565388076842978987655)
                      ·
                        rfl

theorem cell23_2264088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2264088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264088 prefixEnd_2264088 := by exact prefixLift 2264088
  have htrace : WordTrace (prefixWord ++ tailWord_2264088) baseStart_2264088 baseEnd_2264088 := by
    simpa [prefixWord, tailWord_2264088, baseEnd_2264088] using wordTrace_append hprefix tailTrace_2264088
  have hstable : (prefixWord ++ tailWord_2264088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264088).length < 2 ^ (prefixWord ++ tailWord_2264088).sum := by decide
  have hdescent : baseEnd_2264088 < baseStart_2264088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264098 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2264098 : Nat := 118140960795 + 2264098 * 2 ^ 59
def prefixEnd_2264098 : Nat := 4983230072969 + 3 ^ 40 * 2264098 * 2
def baseEnd_2264098 : Nat := 387523507627795979954203

theorem tailTrace_2264098 : CollatzResearch.WordTrace tailWord_2264098 prefixEnd_2264098 387523507627795979954203 := by
  unfold tailWord_2264098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644609537891774499642237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55052292101044731999045965 20644609537891774499642237)
  ·
    refine ⟨7741728576709415437365839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20644609537891774499642237 7741728576709415437365839)
    ·
      refine ⟨11612592865064123156048759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7741728576709415437365839 11612592865064123156048759)
      ·
        refine ⟨17418889297596184734073139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11612592865064123156048759 17418889297596184734073139)
        ·
          refine ⟨26128333946394277101109709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17418889297596184734073139 26128333946394277101109709)
          ·
            refine ⟨9798125229897853912916141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26128333946394277101109709 9798125229897853912916141)
            ·
              refine ⟨3674296961211695217343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9798125229897853912916141 3674296961211695217343553)
              ·
                refine ⟨2755722720908771413007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674296961211695217343553 2755722720908771413007665)
                ·
                  refine ⟨2066792040681578559755749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755722720908771413007665 2066792040681578559755749)
                  ·
                    refine ⟨387523507627795979954203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066792040681578559755749 387523507627795979954203)
                    ·
                      rfl

theorem cell23_2264098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2264098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264098 prefixEnd_2264098 := by exact prefixLift 2264098
  have htrace : WordTrace (prefixWord ++ tailWord_2264098) baseStart_2264098 baseEnd_2264098 := by
    simpa [prefixWord, tailWord_2264098, baseEnd_2264098] using wordTrace_append hprefix tailTrace_2264098
  have hstable : (prefixWord ++ tailWord_2264098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264098).length < 2 ^ (prefixWord ++ tailWord_2264098).sum := by decide
  have hdescent : baseEnd_2264098 < baseStart_2264098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264118 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2264118 : Nat := 118140960795 + 2264118 * 2 ^ 59
def prefixEnd_2264118 : Nat := 4983230072969 + 3 ^ 40 * 2264118 * 2
def baseEnd_2264118 : Nat := 1162580792496477861612517

theorem tailTrace_2264118 : CollatzResearch.WordTrace tailWord_2264118 prefixEnd_2264118 1162580792496477861612517 := by
  unfold tailWord_2264118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161197975718415088393563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55052778407663094276198005 5161197975718415088393563)
  ·
    refine ⟨7741796963577622632590345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5161197975718415088393563 7741796963577622632590345)
    ·
      refine ⟨5806347722683216974442759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7741796963577622632590345 5806347722683216974442759)
      ·
        refine ⟨8709521584024825461664139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806347722683216974442759 8709521584024825461664139)
        ·
          refine ⟨13064282376037238192496209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709521584024825461664139 13064282376037238192496209)
          ·
            refine ⟨9798211782027928644372157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064282376037238192496209 9798211782027928644372157)
            ·
              refine ⟨3674329418260473241639559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9798211782027928644372157 3674329418260473241639559)
              ·
                refine ⟨5511494127390709862459339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674329418260473241639559 5511494127390709862459339)
                ·
                  refine ⟨8267241191086064793689009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511494127390709862459339 8267241191086064793689009)
                  ·
                    refine ⟨6200430893314548595266757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8267241191086064793689009 6200430893314548595266757)
                    ·
                      refine ⟨1162580792496477861612517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6200430893314548595266757 1162580792496477861612517)
                      ·
                        rfl

theorem cell23_2264118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2264118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264118 prefixEnd_2264118 := by exact prefixLift 2264118
  have htrace : WordTrace (prefixWord ++ tailWord_2264118) baseStart_2264118 baseEnd_2264118 := by
    simpa [prefixWord, tailWord_2264118, baseEnd_2264118] using wordTrace_append hprefix tailTrace_2264118
  have hstable : (prefixWord ++ tailWord_2264118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264118).length < 2 ^ (prefixWord ++ tailWord_2264118).sum := by decide
  have hdescent : baseEnd_2264118 < baseStart_2264118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264154 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_2264154 : Nat := 118140960795 + 2264154 * 2 ^ 59
def prefixEnd_2264154 : Nat := 4983230072969 + 3 ^ 40 * 2264154 * 2
def baseEnd_2264154 : Nat := 387533092600013240254117

theorem tailTrace_2264154 : CollatzResearch.WordTrace tailWord_2264154 prefixEnd_2264154 387533092600013240254117 := by
  unfold tailWord_2264154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645120159841054890651879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55053653759576146375071677 20645120159841054890651879)
  ·
    refine ⟨30967680239761582335977819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20645120159841054890651879 30967680239761582335977819)
    ·
      refine ⟨46451520359642373503966729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30967680239761582335977819 46451520359642373503966729)
      ·
        refine ⟨34838640269731780127975047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46451520359642373503966729 34838640269731780127975047)
        ·
          refine ⟨52257960404597670191962571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34838640269731780127975047 52257960404597670191962571)
          ·
            refine ⟨78386940606896505287943857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52257960404597670191962571 78386940606896505287943857)
            ·
              refine ⟨58790205455172378965957893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78386940606896505287943857 58790205455172378965957893)
              ·
                refine ⟨11023163522844821056117105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58790205455172378965957893 11023163522844821056117105)
                ·
                  refine ⟨8267372642133615792087829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11023163522844821056117105 8267372642133615792087829)
                  ·
                    refine ⟨387533092600013240254117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8267372642133615792087829 387533092600013240254117)
                    ·
                      rfl

theorem cell23_2264154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_2264154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264154 prefixEnd_2264154 := by exact prefixLift 2264154
  have htrace : WordTrace (prefixWord ++ tailWord_2264154) baseStart_2264154 baseEnd_2264154 := by
    simpa [prefixWord, tailWord_2264154, baseEnd_2264154] using wordTrace_append hprefix tailTrace_2264154
  have hstable : (prefixWord ++ tailWord_2264154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264154).length < 2 ^ (prefixWord ++ tailWord_2264154).sum := by decide
  have hdescent : baseEnd_2264154 < baseStart_2264154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264164 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_2264164 : Nat := 118140960795 + 2264164 * 2 ^ 59
def prefixEnd_2264164 : Nat := 4983230072969 + 3 ^ 40 * 2264164 * 2
def baseEnd_2264164 : Nat := 1162604412606584681637305

theorem tailTrace_2264164 : CollatzResearch.WordTrace tailWord_2264164 prefixEnd_2264164 1162604412606584681637305 := by
  unfold tailWord_2264164
  simp only [CollatzResearch.WordTrace]
  refine ⟨41290422684663995635235773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55053896912885327513647697 41290422684663995635235773)
  ·
    refine ⟨15483908506748998363213415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41290422684663995635235773 15483908506748998363213415)
    ·
      refine ⟨23225862760123497544820123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15483908506748998363213415 23225862760123497544820123)
      ·
        refine ⟨34838794140185246317230185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23225862760123497544820123 34838794140185246317230185)
        ·
          refine ⟨26129095605138934737922639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34838794140185246317230185 26129095605138934737922639)
          ·
            refine ⟨39193643407708402106883959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26129095605138934737922639 39193643407708402106883959)
            ·
              refine ⟨58790465111562603160325939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39193643407708402106883959 58790465111562603160325939)
              ·
                refine ⟨88185697667343904740488909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58790465111562603160325939 88185697667343904740488909)
                ·
                  refine ⟨33069636625253964277683341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88185697667343904740488909 33069636625253964277683341)
                  ·
                    refine ⟨12401113734470236604131253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33069636625253964277683341 12401113734470236604131253)
                    ·
                      refine ⟨1162604412606584681637305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12401113734470236604131253 1162604412606584681637305)
                      ·
                        rfl

theorem cell23_2264164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_2264164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264164 prefixEnd_2264164 := by exact prefixLift 2264164
  have htrace : WordTrace (prefixWord ++ tailWord_2264164) baseStart_2264164 baseEnd_2264164 := by
    simpa [prefixWord, tailWord_2264164, baseEnd_2264164] using wordTrace_append hprefix tailTrace_2264164
  have hstable : (prefixWord ++ tailWord_2264164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264164).length < 2 ^ (prefixWord ++ tailWord_2264164).sum := by decide
  have hdescent : baseEnd_2264164 < baseStart_2264164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264178 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2264178 : Nat := 118140960795 + 2264178 * 2 ^ 59
def prefixEnd_2264178 : Nat := 4983230072969 + 3 ^ 40 * 2264178 * 2
def baseEnd_2264178 : Nat := 1162611601335747626862241

theorem tailTrace_2264178 : CollatzResearch.WordTrace tailWord_2264178 prefixEnd_2264178 1162611601335747626862241 := by
  unfold tailWord_2264178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645338997819317915370297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55054237327518181107654125 20645338997819317915370297)
  ·
    refine ⟨15484004248364488436527723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20645338997819317915370297 15484004248364488436527723)
    ·
      refine ⟨23226006372546732654791585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484004248364488436527723 23226006372546732654791585)
      ·
        refine ⟨17419504779410049491093689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23226006372546732654791585 17419504779410049491093689)
        ·
          refine ⟨13064628584557537118320267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17419504779410049491093689 13064628584557537118320267)
          ·
            refine ⟨19596942876836305677480401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13064628584557537118320267 19596942876836305677480401)
            ·
              refine ⟨14697707157627229258110301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19596942876836305677480401 14697707157627229258110301)
              ·
                refine ⟨5511640184110210971791363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14697707157627229258110301 5511640184110210971791363)
                ·
                  refine ⟨8267460276165316457687045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511640184110210971791363 8267460276165316457687045)
                  ·
                    refine ⟨1550148801780996835816321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8267460276165316457687045 1550148801780996835816321)
                    ·
                      refine ⟨1162611601335747626862241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550148801780996835816321 1162611601335747626862241)
                      ·
                        rfl

theorem cell23_2264178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2264178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264178 prefixEnd_2264178 := by exact prefixLift 2264178
  have htrace : WordTrace (prefixWord ++ tailWord_2264178) baseStart_2264178 baseEnd_2264178 := by
    simpa [prefixWord, tailWord_2264178, baseEnd_2264178] using wordTrace_append hprefix tailTrace_2264178
  have hstable : (prefixWord ++ tailWord_2264178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264178).length < 2 ^ (prefixWord ++ tailWord_2264178).sum := by decide
  have hdescent : baseEnd_2264178 < baseStart_2264178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264184 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 7]
def baseStart_2264184 : Nat := 118140960795 + 2264184 * 2 ^ 59
def prefixEnd_2264184 : Nat := 4983230072969 + 3 ^ 40 * 2264184 * 2
def baseEnd_2264184 : Nat := 129179409135519400376357

theorem tailTrace_2264184 : CollatzResearch.WordTrace tailWord_2264184 prefixEnd_2264184 129179409135519400376357 := by
  unfold tailWord_2264184
  simp only [CollatzResearch.WordTrace]
  refine ⟨41290787414627767343099803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55054383219503689790799737 41290787414627767343099803)
  ·
    refine ⟨61936181121941651014649705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41290787414627767343099803 61936181121941651014649705)
    ·
      refine ⟨46452135841456238260987279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61936181121941651014649705 46452135841456238260987279)
      ·
        refine ⟨69678203762184357391480919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46452135841456238260987279 69678203762184357391480919)
        ·
          refine ⟨104517305643276536087221379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69678203762184357391480919 104517305643276536087221379)
          ·
            refine ⟨156775958464914804130832069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104517305643276536087221379 156775958464914804130832069)
            ·
              refine ⟨29395492212171525774531013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156775958464914804130832069 29395492212171525774531013)
              ·
                refine ⟨5511654789782161082724565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29395492212171525774531013 5511654789782161082724565)
                ·
                  refine ⟨129179409135519400376357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5511654789782161082724565 129179409135519400376357)
                  ·
                    rfl

theorem cell23_2264184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_2264184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264184 prefixEnd_2264184 := by exact prefixLift 2264184
  have htrace : WordTrace (prefixWord ++ tailWord_2264184) baseStart_2264184 baseEnd_2264184 := by
    simpa [prefixWord, tailWord_2264184, baseEnd_2264184] using wordTrace_append hprefix tailTrace_2264184
  have hstable : (prefixWord ++ tailWord_2264184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264184).length < 2 ^ (prefixWord ++ tailWord_2264184).sum := by decide
  have hdescent : baseEnd_2264184 < baseStart_2264184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264228 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_2264228 : Nat := 118140960795 + 2264228 * 2 ^ 59
def prefixEnd_2264228 : Nat := 4983230072969 + 3 ^ 40 * 2264228 * 2
def baseEnd_2264228 : Nat := 1162637275368472431237011

theorem tailTrace_2264228 : CollatzResearch.WordTrace tailWord_2264228 prefixEnd_2264228 1162637275368472431237011 := by
  unfold tailWord_2264228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41291589820548065100400669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55055453094064086800534225 41291589820548065100400669)
  ·
    refine ⟨15484346182705524412650251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41291589820548065100400669 15484346182705524412650251)
    ·
      refine ⟨23226519274058286618975377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484346182705524412650251 23226519274058286618975377)
      ·
        refine ⟨17419889455543714964231533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23226519274058286618975377 17419889455543714964231533)
        ·
          refine ⟨6532458545828893111586825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17419889455543714964231533 6532458545828893111586825)
          ·
            refine ⟨4899343909371669833690119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532458545828893111586825 4899343909371669833690119)
            ·
              refine ⟨7349015864057504750535179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899343909371669833690119 7349015864057504750535179)
              ·
                refine ⟨11023523796086257125802769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349015864057504750535179 11023523796086257125802769)
                ·
                  refine ⟨8267642847064692844352077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11023523796086257125802769 8267642847064692844352077)
                  ·
                    refine ⟨3100366067649259816632029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8267642847064692844352077 3100366067649259816632029)
                    ·
                      refine ⟨1162637275368472431237011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3100366067649259816632029 1162637275368472431237011)
                      ·
                        rfl

theorem cell23_2264228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_2264228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264228 prefixEnd_2264228 := by exact prefixLift 2264228
  have htrace : WordTrace (prefixWord ++ tailWord_2264228) baseStart_2264228 baseEnd_2264228 := by
    simpa [prefixWord, tailWord_2264228, baseEnd_2264228] using wordTrace_append hprefix tailTrace_2264228
  have hstable : (prefixWord ++ tailWord_2264228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264228).length < 2 ^ (prefixWord ++ tailWord_2264228).sum := by decide
  have hdescent : baseEnd_2264228 < baseStart_2264228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264251 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4]
def baseStart_2264251 : Nat := 118140960795 + 2264251 * 2 ^ 59
def prefixEnd_2264251 : Nat := 4983230072969 + 3 ^ 40 * 2264251 * 2
def baseEnd_2264251 : Nat := 1162649085423525841249405

theorem tailTrace_2264251 : CollatzResearch.WordTrace tailWord_2264251 prefixEnd_2264251 1162649085423525841249405 := by
  unfold tailWord_2264251
  simp only [CollatzResearch.WordTrace]
  refine ⟨82584018520012805128888607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55056012346675203419259071 82584018520012805128888607)
  ·
    refine ⟨123876027780019207693332911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82584018520012805128888607 123876027780019207693332911)
    ·
      refine ⟨185814041670028811539999367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123876027780019207693332911 185814041670028811539999367)
      ·
        refine ⟨278721062505043217309999051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185814041670028811539999367 278721062505043217309999051)
        ·
          refine ⟨418081593757564825964998577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278721062505043217309999051 418081593757564825964998577)
          ·
            refine ⟨313561195318173619473748933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418081593757564825964998577 313561195318173619473748933)
            ·
              refine ⟨58792724122157553651327925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313561195318173619473748933 58792724122157553651327925)
              ·
                refine ⟨5511817886452270654811993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58792724122157553651327925 5511817886452270654811993)
                ·
                  refine ⟨4133863414839202991108995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511817886452270654811993 4133863414839202991108995)
                  ·
                    refine ⟨6200795122258804486663493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133863414839202991108995 6200795122258804486663493)
                    ·
                      refine ⟨1162649085423525841249405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6200795122258804486663493 1162649085423525841249405)
                      ·
                        rfl

theorem cell23_2264251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_2264251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264251 prefixEnd_2264251 := by exact prefixLift 2264251
  have htrace : WordTrace (prefixWord ++ tailWord_2264251) baseStart_2264251 baseEnd_2264251 := by
    simpa [prefixWord, tailWord_2264251, baseEnd_2264251] using wordTrace_append hprefix tailTrace_2264251
  have hstable : (prefixWord ++ tailWord_2264251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264251).length < 2 ^ (prefixWord ++ tailWord_2264251).sum := by decide
  have hdescent : baseEnd_2264251 < baseStart_2264251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264261 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2264261 : Nat := 118140960795 + 2264261 * 2 ^ 59
def prefixEnd_2264261 : Nat := 4983230072969 + 3 ^ 40 * 2264261 * 2
def baseEnd_2264261 : Nat := 387551406743356934041453

theorem tailTrace_2264261 : CollatzResearch.WordTrace tailWord_2264261 prefixEnd_2264261 387551406743356934041453 := by
  unfold tailWord_2264261
  simp only [CollatzResearch.WordTrace]
  refine ⟨82584383249976576836752637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55056255499984384557835091 82584383249976576836752637)
  ·
    refine ⟨30969143718741216313782239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82584383249976576836752637 30969143718741216313782239)
    ·
      refine ⟨46453715578111824470673359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30969143718741216313782239 46453715578111824470673359)
      ·
        refine ⟨69680573367167736706010039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46453715578111824470673359 69680573367167736706010039)
        ·
          refine ⟨104520860050751605059015059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69680573367167736706010039 104520860050751605059015059)
          ·
            refine ⟨156781290076127407588522589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104520860050751605059015059 156781290076127407588522589)
            ·
              refine ⟨58792983778547777845695971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156781290076127407588522589 58792983778547777845695971)
              ·
                refine ⟨88189475667821666768543957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58792983778547777845695971 88189475667821666768543957)
                ·
                  refine ⟨2066940835964570314887749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88189475667821666768543957 2066940835964570314887749)
                  ·
                    refine ⟨387551406743356934041453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066940835964570314887749 387551406743356934041453)
                    ·
                      rfl

theorem cell23_2264261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2264261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264261 prefixEnd_2264261 := by exact prefixLift 2264261
  have htrace : WordTrace (prefixWord ++ tailWord_2264261) baseStart_2264261 baseEnd_2264261 := by
    simpa [prefixWord, tailWord_2264261, baseEnd_2264261] using wordTrace_append hprefix tailTrace_2264261
  have hstable : (prefixWord ++ tailWord_2264261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264261).length < 2 ^ (prefixWord ++ tailWord_2264261).sum := by decide
  have hdescent : baseEnd_2264261 < baseStart_2264261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264322 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2264322 : Nat := 118140960795 + 2264322 * 2 ^ 59
def prefixEnd_2264322 : Nat := 4983230072969 + 3 ^ 40 * 2264322 * 2
def baseEnd_2264322 : Nat := 1162685542549995063461579

theorem tailTrace_2264322 : CollatzResearch.WordTrace tailWord_2264322 prefixEnd_2264322 1162685542549995063461579 := by
  unfold tailWord_2264322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20646652025688896063680805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55057738735170389503148813 20646652025688896063680805)
  ·
    refine ⟨3871247254816668011940151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20646652025688896063680805 3871247254816668011940151)
    ·
      refine ⟨5806870882225002017910227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871247254816668011940151 5806870882225002017910227)
      ·
        refine ⟨8710306323337503026865341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806870882225002017910227 8710306323337503026865341)
        ·
          refine ⟨3266364871251563635074503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8710306323337503026865341 3266364871251563635074503)
          ·
            refine ⟨4899547306877345452611755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266364871251563635074503 4899547306877345452611755)
            ·
              refine ⟨7349320960316018178917633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899547306877345452611755 7349320960316018178917633)
              ·
                refine ⟨5511990720237013634188225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7349320960316018178917633 5511990720237013634188225)
                ·
                  refine ⟨4133993040177760225641169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511990720237013634188225 4133993040177760225641169)
                  ·
                    refine ⟨3100494780133320169230877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133993040177760225641169 3100494780133320169230877)
                    ·
                      refine ⟨1162685542549995063461579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3100494780133320169230877 1162685542549995063461579)
                      ·
                        rfl

theorem cell23_2264322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2264322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264322 prefixEnd_2264322 := by exact prefixLift 2264322
  have htrace : WordTrace (prefixWord ++ tailWord_2264322) baseStart_2264322 baseEnd_2264322 := by
    simpa [prefixWord, tailWord_2264322, baseEnd_2264322] using wordTrace_append hprefix tailTrace_2264322
  have hstable : (prefixWord ++ tailWord_2264322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264322).length < 2 ^ (prefixWord ++ tailWord_2264322).sum := by decide
  have hdescent : baseEnd_2264322 < baseStart_2264322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264341 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2264341 : Nat := 118140960795 + 2264341 * 2 ^ 59
def prefixEnd_2264341 : Nat := 4983230072969 + 3 ^ 40 * 2264341 * 2
def baseEnd_2264341 : Nat := 1162695298682430489123991

theorem tailTrace_2264341 : CollatzResearch.WordTrace tailWord_2264341 prefixEnd_2264341 1162695298682430489123991 := by
  unfold tailWord_2264341
  simp only [CollatzResearch.WordTrace]
  refine ⟨82587301089686750499664877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55058200726457833666443251 82587301089686750499664877)
  ·
    refine ⟨30970237908632531437374329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82587301089686750499664877 30970237908632531437374329)
    ·
      refine ⟨23227678431474398578030747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30970237908632531437374329 23227678431474398578030747)
      ·
        refine ⟨34841517647211597867046121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23227678431474398578030747 34841517647211597867046121)
        ·
          refine ⟨26131138235408698400284591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34841517647211597867046121 26131138235408698400284591)
          ·
            refine ⟨39196707353113047600426887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26131138235408698400284591 39196707353113047600426887)
            ·
              refine ⟨58795061029669571400640331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39196707353113047600426887 58795061029669571400640331)
              ·
                refine ⟨88192591544504357100960497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58795061029669571400640331 88192591544504357100960497)
                ·
                  refine ⟨66144443658378267825720373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88192591544504357100960497 66144443658378267825720373)
                  ·
                    refine ⟨6201041592972962608661285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66144443658378267825720373 6201041592972962608661285)
                    ·
                      refine ⟨1162695298682430489123991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6201041592972962608661285 1162695298682430489123991)
                      ·
                        rfl

theorem cell23_2264341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2264341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264341 prefixEnd_2264341 := by exact prefixLift 2264341
  have htrace : WordTrace (prefixWord ++ tailWord_2264341) baseStart_2264341 baseEnd_2264341 := by
    simpa [prefixWord, tailWord_2264341, baseEnd_2264341] using wordTrace_append hprefix tailTrace_2264341
  have hstable : (prefixWord ++ tailWord_2264341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264341).length < 2 ^ (prefixWord ++ tailWord_2264341).sum := by decide
  have hdescent : baseEnd_2264341 < baseStart_2264341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264355 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 1, 5]
def baseStart_2264355 : Nat := 118140960795 + 2264355 * 2 ^ 59
def prefixEnd_2264355 : Nat := 4983230072969 + 3 ^ 40 * 2264355 * 2
def baseEnd_2264355 : Nat := 387567495803864478116309

theorem tailTrace_2264355 : CollatzResearch.WordTrace tailWord_2264355 prefixEnd_2264355 387567495803864478116309 := by
  unfold tailWord_2264355
  simp only [CollatzResearch.WordTrace]
  refine ⟨82587811711636030890674519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55058541141090687260449679 82587811711636030890674519)
  ·
    refine ⟨123881717567454046336011779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82587811711636030890674519 123881717567454046336011779)
    ·
      refine ⟨185822576351181069504017669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123881717567454046336011779 185822576351181069504017669)
      ·
        refine ⟨34841733065846450532003313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185822576351181069504017669 34841733065846450532003313)
        ·
          refine ⟨26131299799384837899002485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34841733065846450532003313 26131299799384837899002485)
          ·
            refine ⟨2449809356192328553031483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26131299799384837899002485 2449809356192328553031483)
            ·
              refine ⟨3674714034288492829547225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449809356192328553031483 3674714034288492829547225)
              ·
                refine ⟨2756035525716369622160419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674714034288492829547225 2756035525716369622160419)
                ·
                  refine ⟨4134053288574554433240629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756035525716369622160419 4134053288574554433240629)
                  ·
                    refine ⟨387567495803864478116309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4134053288574554433240629 387567495803864478116309)
                    ·
                      rfl

theorem cell23_2264355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 5].length) (baseStart_2264355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264355 prefixEnd_2264355 := by exact prefixLift 2264355
  have htrace : WordTrace (prefixWord ++ tailWord_2264355) baseStart_2264355 baseEnd_2264355 := by
    simpa [prefixWord, tailWord_2264355, baseEnd_2264355] using wordTrace_append hprefix tailTrace_2264355
  have hstable : (prefixWord ++ tailWord_2264355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264355).length < 2 ^ (prefixWord ++ tailWord_2264355).sum := by decide
  have hdescent : baseEnd_2264355 < baseStart_2264355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264362 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2264362 : Nat := 118140960795 + 2264362 * 2 ^ 59
def prefixEnd_2264362 : Nat := 4983230072969 + 3 ^ 40 * 2264362 * 2
def baseEnd_2264362 : Nat := 1162706081776174906961395

theorem tailTrace_2264362 : CollatzResearch.WordTrace tailWord_2264362 prefixEnd_2264362 1162706081776174906961395 := by
  unfold tailWord_2264362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647016755652667771544835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55058711348407114057452893 20647016755652667771544835)
  ·
    refine ⟨30970525133479001657317253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20647016755652667771544835 30970525133479001657317253)
    ·
      refine ⟨5806973462527312810746985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30970525133479001657317253 5806973462527312810746985)
      ·
        refine ⟨4355230096895484608060239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5806973462527312810746985 4355230096895484608060239)
        ·
          refine ⟨6532845145343226912090359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355230096895484608060239 6532845145343226912090359)
          ·
            refine ⟨9799267718014840368135539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6532845145343226912090359 9799267718014840368135539)
            ·
              refine ⟨14698901577022260552203309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9799267718014840368135539 14698901577022260552203309)
              ·
                refine ⟨5512088091383347707076241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14698901577022260552203309 5512088091383347707076241)
                ·
                  refine ⟨4134066068537510780307181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512088091383347707076241 4134066068537510780307181)
                  ·
                    refine ⟨1550274775701566542615193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4134066068537510780307181 1550274775701566542615193)
                    ·
                      refine ⟨1162706081776174906961395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550274775701566542615193 1162706081776174906961395)
                      ·
                        rfl

theorem cell23_2264362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2264362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264362 prefixEnd_2264362 := by exact prefixLift 2264362
  have htrace : WordTrace (prefixWord ++ tailWord_2264362) baseStart_2264362 baseEnd_2264362 := by
    simpa [prefixWord, tailWord_2264362, baseEnd_2264362] using wordTrace_append hprefix tailTrace_2264362
  have hstable : (prefixWord ++ tailWord_2264362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264362).length < 2 ^ (prefixWord ++ tailWord_2264362).sum := by decide
  have hdescent : baseEnd_2264362 < baseStart_2264362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264372 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2264372 : Nat := 118140960795 + 2264372 * 2 ^ 59
def prefixEnd_2264372 : Nat := 4983230072969 + 3 ^ 40 * 2264372 * 2
def baseEnd_2264372 : Nat := 387570405527573289278783

theorem tailTrace_2264372 : CollatzResearch.WordTrace tailWord_2264372 prefixEnd_2264372 387570405527573289278783 := by
  unfold tailWord_2264372
  simp only [CollatzResearch.WordTrace]
  refine ⟨41294215876287221397021685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55058954501716295196028913 41294215876287221397021685)
  ·
    refine ⟨3871332738401927005970783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41294215876287221397021685 3871332738401927005970783)
    ·
      refine ⟨5806999107602890508956175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871332738401927005970783 5806999107602890508956175)
      ·
        refine ⟨8710498661404335763434263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806999107602890508956175 8710498661404335763434263)
        ·
          refine ⟨13065747992106503645151395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8710498661404335763434263 13065747992106503645151395)
          ·
            refine ⟨19598621988159755467727093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13065747992106503645151395 19598621988159755467727093)
            ·
              refine ⟨1837370811389977075099415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19598621988159755467727093 1837370811389977075099415)
              ·
                refine ⟨2756056217084965612649123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837370811389977075099415 2756056217084965612649123)
                ·
                  refine ⟨4134084325627448418973685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756056217084965612649123 4134084325627448418973685)
                  ·
                    refine ⟨387570405527573289278783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4134084325627448418973685 387570405527573289278783)
                    ·
                      rfl

theorem cell23_2264372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2264372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264372 prefixEnd_2264372 := by exact prefixLift 2264372
  have htrace : WordTrace (prefixWord ++ tailWord_2264372) baseStart_2264372 baseEnd_2264372 := by
    simpa [prefixWord, tailWord_2264372, baseEnd_2264372] using wordTrace_append hprefix tailTrace_2264372
  have hstable : (prefixWord ++ tailWord_2264372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264372).length < 2 ^ (prefixWord ++ tailWord_2264372).sum := by decide
  have hdescent : baseEnd_2264372 < baseStart_2264372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264405 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2264405 : Nat := 118140960795 + 2264405 * 2 ^ 59
def prefixEnd_2264405 : Nat := 4983230072969 + 3 ^ 40 * 2264405 * 2
def baseEnd_2264405 : Nat := 1162728161444318238723697

theorem tailTrace_2264405 : CollatzResearch.WordTrace tailWord_2264405 prefixEnd_2264405 1162728161444318238723697 := by
  unfold tailWord_2264405
  simp only [CollatzResearch.WordTrace]
  refine ⟨82589635361454889429994669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55059756907636592953329779 82589635361454889429994669)
  ·
    refine ⟨30971113260545583536248001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82589635361454889429994669 30971113260545583536248001)
    ·
      refine ⟨23228334945409187652186001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30971113260545583536248001 23228334945409187652186001)
      ·
        refine ⟨17421251209056890739139501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23228334945409187652186001 17421251209056890739139501)
        ·
          refine ⟨6532969203396334027177313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17421251209056890739139501 6532969203396334027177313)
          ·
            refine ⟨4899726902547250520382985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532969203396334027177313 4899726902547250520382985)
            ·
              refine ⟨3674795176910437890287239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4899726902547250520382985 3674795176910437890287239)
              ·
                refine ⟨5512192765365656835430859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674795176910437890287239 5512192765365656835430859)
                ·
                  refine ⟨8268289148048485253146289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5512192765365656835430859 8268289148048485253146289)
                  ·
                    refine ⟨6201216861036363939859717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8268289148048485253146289 6201216861036363939859717)
                    ·
                      refine ⟨1162728161444318238723697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6201216861036363939859717 1162728161444318238723697)
                      ·
                        rfl

theorem cell23_2264405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2264405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264405 prefixEnd_2264405 := by exact prefixLift 2264405
  have htrace : WordTrace (prefixWord ++ tailWord_2264405) baseStart_2264405 baseEnd_2264405 := by
    simpa [prefixWord, tailWord_2264405, baseEnd_2264405] using wordTrace_append hprefix tailTrace_2264405
  have hstable : (prefixWord ++ tailWord_2264405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264405).length < 2 ^ (prefixWord ++ tailWord_2264405).sum := by decide
  have hdescent : baseEnd_2264405 < baseStart_2264405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264413 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2264413 : Nat := 118140960795 + 2264413 * 2 ^ 59
def prefixEnd_2264413 : Nat := 4983230072969 + 3 ^ 40 * 2264413 * 2
def baseEnd_2264413 : Nat := 1162732269289554207423661

theorem tailTrace_2264413 : CollatzResearch.WordTrace tailWord_2264413 prefixEnd_2264413 1162732269289554207423661 := by
  unfold tailWord_2264413
  simp only [CollatzResearch.WordTrace]
  refine ⟨82589927145425906796285893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55059951430283937864190595 82589927145425906796285893)
  ·
    refine ⟨15485611339767357524303605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82589927145425906796285893 15485611339767357524303605)
    ·
      refine ⟨1451776063103189767903463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15485611339767357524303605 1451776063103189767903463)
      ·
        refine ⟨2177664094654784651855195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451776063103189767903463 2177664094654784651855195)
        ·
          refine ⟨3266496141982176977782793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177664094654784651855195 3266496141982176977782793)
          ·
            refine ⟨2449872106486632733337095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266496141982176977782793 2449872106486632733337095)
            ·
              refine ⟨3674808159729949100005643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449872106486632733337095 3674808159729949100005643)
              ·
                refine ⟨5512212239594923650008465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674808159729949100005643 5512212239594923650008465)
                ·
                  refine ⟨4134159179696192737506349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512212239594923650008465 4134159179696192737506349)
                  ·
                    refine ⟨1550309692386072276564881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4134159179696192737506349 1550309692386072276564881)
                    ·
                      refine ⟨1162732269289554207423661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550309692386072276564881 1162732269289554207423661)
                      ·
                        rfl

theorem cell23_2264413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2264413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264413 prefixEnd_2264413 := by exact prefixLift 2264413
  have htrace : WordTrace (prefixWord ++ tailWord_2264413) baseStart_2264413 baseEnd_2264413 := by
    simpa [prefixWord, tailWord_2264413, baseEnd_2264413] using wordTrace_append hprefix tailTrace_2264413
  have hstable : (prefixWord ++ tailWord_2264413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264413).length < 2 ^ (prefixWord ++ tailWord_2264413).sum := by decide
  have hdescent : baseEnd_2264413 < baseStart_2264413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
