import V185TrunkScan23Chunk0153

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_909898 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_909898 : Nat := 118140960795 + 909898 * 2 ^ 59
def prefixEnd_909898 : Nat := 4983230072969 + 3 ^ 40 * 909898 * 2
def baseEnd_909898 : Nat := 467215020564786253590461

theorem tailTrace_909898 : CollatzResearch.WordTrace tailWord_909898 prefixEnd_909898 467215020564786253590461 := by
  unfold tailWord_909898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296676614400604762906587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22124470971734946034417565 8296676614400604762906587)
  ·
    refine ⟨12445014921600907144359881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8296676614400604762906587 12445014921600907144359881)
    ·
      refine ⟨9333761191200680358269911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12445014921600907144359881 9333761191200680358269911)
      ·
        refine ⟨14000641786801020537404867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9333761191200680358269911 14000641786801020537404867)
        ·
          refine ⟨21000962680201530806107301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14000641786801020537404867 21000962680201530806107301)
          ·
            refine ⟨3937680502537787026145119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21000962680201530806107301 3937680502537787026145119)
            ·
              refine ⟨5906520753806680539217679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937680502537787026145119 5906520753806680539217679)
              ·
                refine ⟨8859781130710020808826519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906520753806680539217679 8859781130710020808826519)
                ·
                  refine ⟨13289671696065031213239779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859781130710020808826519 13289671696065031213239779)
                  ·
                    refine ⟨19934507544097546819859669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13289671696065031213239779 19934507544097546819859669)
                    ·
                      refine ⟨467215020564786253590461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19934507544097546819859669 467215020564786253590461)
                      ·
                        rfl

theorem cell23_909898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_909898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909898 prefixEnd_909898 := by exact prefixLift 909898
  have htrace : WordTrace (prefixWord ++ tailWord_909898) baseStart_909898 baseEnd_909898 := by
    simpa [prefixWord, tailWord_909898, baseEnd_909898] using wordTrace_append hprefix tailTrace_909898
  have hstable : (prefixWord ++ tailWord_909898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909898).length < 2 ^ (prefixWord ++ tailWord_909898).sum := by decide
  have hdescent : baseEnd_909898 < baseStart_909898 := by decide
  rcases family_descends (prefixWord ++ tailWord_909898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909948 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 8]
def baseStart_909948 : Nat := 118140960795 + 909948 * 2 ^ 59
def prefixEnd_909948 : Nat := 4983230072969 + 3 ^ 40 * 909948 * 2
def baseEnd_909948 : Nat := 51915632733056784218359

theorem tailTrace_909948 : CollatzResearch.WordTrace tailWord_909948 prefixEnd_909948 51915632733056784218359 := by
  unfold tailWord_909948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594265053710638795473249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22125686738280851727297665 16594265053710638795473249)
  ·
    refine ⟨12445698790282979096604937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16594265053710638795473249 12445698790282979096604937)
    ·
      refine ⟨9334274092712234322453703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12445698790282979096604937 9334274092712234322453703)
      ·
        refine ⟨14001411139068351483680555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9334274092712234322453703 14001411139068351483680555)
        ·
          refine ⟨21002116708602527225520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14001411139068351483680555 21002116708602527225520833)
          ·
            refine ⟨15751587531451895419140625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21002116708602527225520833 15751587531451895419140625)
            ·
              refine ⟨11813690648588921564355469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15751587531451895419140625 11813690648588921564355469)
              ·
                refine ⟨4430133993220845586633301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11813690648588921564355469 4430133993220845586633301)
                ·
                  refine ⟨51915632733056784218359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4430133993220845586633301 51915632733056784218359)
                  ·
                    rfl

theorem cell23_909948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_909948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_909948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_909948 prefixEnd_909948 := by exact prefixLift 909948
  have htrace : WordTrace (prefixWord ++ tailWord_909948) baseStart_909948 baseEnd_909948 := by
    simpa [prefixWord, tailWord_909948, baseEnd_909948] using wordTrace_append hprefix tailTrace_909948
  have hstable : (prefixWord ++ tailWord_909948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909948).length < 2 ^ (prefixWord ++ tailWord_909948).sum := by decide
  have hdescent : baseEnd_909948 < baseStart_909948 := by decide
  rcases family_descends (prefixWord ++ tailWord_909948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910002 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_910002 : Nat := 118140960795 + 910002 * 2 ^ 59
def prefixEnd_910002 : Nat := 4983230072969 + 3 ^ 40 * 910002 * 2
def baseEnd_910002 : Nat := 467268422552853846689983

theorem tailTrace_910002 : CollatzResearch.WordTrace tailWord_910002 prefixEnd_910002 467268422552853846689983 := by
  unfold tailWord_910002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297624912306411203353065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22126999766150429875608173 8297624912306411203353065)
  ·
    refine ⟨6223218684229808402514799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8297624912306411203353065 6223218684229808402514799)
    ·
      refine ⟨9334828026344712603772199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223218684229808402514799 9334828026344712603772199)
      ·
        refine ⟨14002242039517068905658299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9334828026344712603772199 14002242039517068905658299)
        ·
          refine ⟨21003363059275603358487449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14002242039517068905658299 21003363059275603358487449)
          ·
            refine ⟨15752522294456702518865587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21003363059275603358487449 15752522294456702518865587)
            ·
              refine ⟨23628783441685053778298381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15752522294456702518865587 23628783441685053778298381)
              ·
                refine ⟨8860793790631895166861893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23628783441685053778298381 8860793790631895166861893)
                ·
                  refine ⟨1661398835743480343786605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8860793790631895166861893 1661398835743480343786605)
                  ·
                    refine ⟨623024563403805128919977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661398835743480343786605 623024563403805128919977)
                    ·
                      refine ⟨467268422552853846689983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623024563403805128919977 467268422552853846689983)
                      ·
                        rfl

theorem cell23_910002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_910002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910002 prefixEnd_910002 := by exact prefixLift 910002
  have htrace : WordTrace (prefixWord ++ tailWord_910002) baseStart_910002 baseEnd_910002 := by
    simpa [prefixWord, tailWord_910002, baseEnd_910002] using wordTrace_append hprefix tailTrace_910002
  have hstable : (prefixWord ++ tailWord_910002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910002).length < 2 ^ (prefixWord ++ tailWord_910002).sum := by decide
  have hdescent : baseEnd_910002 < baseStart_910002 := by decide
  rcases family_descends (prefixWord ++ tailWord_910002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910008 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_910008 : Nat := 118140960795 + 910008 * 2 ^ 59
def prefixEnd_910008 : Nat := 4983230072969 + 3 ^ 40 * 910008 * 2
def baseEnd_910008 : Nat := 155757167812260274404985

theorem tailTrace_910008 : CollatzResearch.WordTrace tailWord_910008 prefixEnd_910008 155757167812260274404985 := by
  unfold tailWord_910008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16595359243601953919065339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22127145658135938558753785 16595359243601953919065339)
  ·
    refine ⟨24893038865402930878598009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16595359243601953919065339 24893038865402930878598009)
    ·
      refine ⟨18669779149052198158948507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24893038865402930878598009 18669779149052198158948507)
      ·
        refine ⟨28004668723578297238422761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18669779149052198158948507 28004668723578297238422761)
        ·
          refine ⟨21003501542683722928817071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28004668723578297238422761 21003501542683722928817071)
          ·
            refine ⟨31505252314025584393225607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21003501542683722928817071 31505252314025584393225607)
            ·
              refine ⟨47257878471038376589838411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31505252314025584393225607 47257878471038376589838411)
              ·
                refine ⟨70886817706557564884757617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47257878471038376589838411 70886817706557564884757617)
                ·
                  refine ⟨53165113279918173663568213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70886817706557564884757617 53165113279918173663568213)
                  ·
                    refine ⟨155757167812260274404985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 53165113279918173663568213 155757167812260274404985)
                    ·
                      rfl

theorem cell23_910008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_910008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910008 prefixEnd_910008 := by exact prefixLift 910008
  have htrace : WordTrace (prefixWord ++ tailWord_910008) baseStart_910008 baseEnd_910008 := by
    simpa [prefixWord, tailWord_910008, baseEnd_910008] using wordTrace_append hprefix tailTrace_910008
  have hstable : (prefixWord ++ tailWord_910008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910008).length < 2 ^ (prefixWord ++ tailWord_910008).sum := by decide
  have hdescent : baseEnd_910008 < baseStart_910008 := by decide
  rcases family_descends (prefixWord ++ tailWord_910008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910052 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_910052 : Nat := 118140960795 + 910052 * 2 ^ 59
def prefixEnd_910052 : Nat := 4983230072969 + 3 ^ 40 * 910052 * 2
def baseEnd_910052 : Nat := 467294096585578651064753

theorem tailTrace_910052 : CollatzResearch.WordTrace tailWord_910052 prefixEnd_910052 467294096585578651064753 := by
  unfold tailWord_910052
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596161649522251676366205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22128215532696335568488273 16596161649522251676366205)
  ·
    refine ⟨6223560618570844378637327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16596161649522251676366205 6223560618570844378637327)
    ·
      refine ⟨9335340927856266567955991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223560618570844378637327 9335340927856266567955991)
      ·
        refine ⟨14003011391784399851933987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335340927856266567955991 14003011391784399851933987)
        ·
          refine ⟨21004517087676599777900981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14003011391784399851933987 21004517087676599777900981)
          ·
            refine ⟨1969173476969681229178217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21004517087676599777900981 1969173476969681229178217)
            ·
              refine ⟨1476880107727260921883663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969173476969681229178217 1476880107727260921883663)
              ·
                refine ⟨2215320161590891382825495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476880107727260921883663 2215320161590891382825495)
                ·
                  refine ⟨3322980242386337074238243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215320161590891382825495 3322980242386337074238243)
                  ·
                    refine ⟨4984470363579505611357365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322980242386337074238243 4984470363579505611357365)
                    ·
                      refine ⟨467294096585578651064753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4984470363579505611357365 467294096585578651064753)
                      ·
                        rfl

theorem cell23_910052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_910052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910052 prefixEnd_910052 := by exact prefixLift 910052
  have htrace : WordTrace (prefixWord ++ tailWord_910052) baseStart_910052 baseEnd_910052 := by
    simpa [prefixWord, tailWord_910052, baseEnd_910052] using wordTrace_append hprefix tailTrace_910052
  have hstable : (prefixWord ++ tailWord_910052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910052).length < 2 ^ (prefixWord ++ tailWord_910052).sum := by decide
  have hdescent : baseEnd_910052 < baseStart_910052 := by decide
  rcases family_descends (prefixWord ++ tailWord_910052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910066 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_910066 : Nat := 118140960795 + 910066 * 2 ^ 59
def prefixEnd_910066 : Nat := 4983230072969 + 3 ^ 40 * 910066 * 2
def baseEnd_910066 : Nat := 467301285314741596289689

theorem tailTrace_910066 : CollatzResearch.WordTrace tailWord_910066 prefixEnd_910066 467301285314741596289689 := by
  unfold tailWord_910066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298208480248445935935513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22128555947329189162494701 8298208480248445935935513)
  ·
    refine ⟨6223656360186334451951635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8298208480248445935935513 6223656360186334451951635)
    ·
      refine ⟨9335484540279501677927453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223656360186334451951635 9335484540279501677927453)
      ·
        refine ⟨3500806702604813129222795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9335484540279501677927453 3500806702604813129222795)
        ·
          refine ⟨5251210053907219693834193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500806702604813129222795 5251210053907219693834193)
          ·
            refine ⟨3938407540430414770375645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251210053907219693834193 3938407540430414770375645)
            ·
              refine ⟨1476902827661405538890867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938407540430414770375645 1476902827661405538890867)
              ·
                refine ⟨2215354241492108308336301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476902827661405538890867 2215354241492108308336301)
                ·
                  refine ⟨830757840559540615626113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2215354241492108308336301 830757840559540615626113)
                  ·
                    refine ⟨623068380419655461719585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 830757840559540615626113 623068380419655461719585)
                    ·
                      refine ⟨467301285314741596289689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623068380419655461719585 467301285314741596289689)
                      ·
                        rfl

theorem cell23_910066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_910066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910066 prefixEnd_910066 := by exact prefixLift 910066
  have htrace : WordTrace (prefixWord ++ tailWord_910066) baseStart_910066 baseEnd_910066 := by
    simpa [prefixWord, tailWord_910066, baseEnd_910066] using wordTrace_append hprefix tailTrace_910066
  have hstable : (prefixWord ++ tailWord_910066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910066).length < 2 ^ (prefixWord ++ tailWord_910066).sum := by decide
  have hdescent : baseEnd_910066 < baseStart_910066 := by decide
  rcases family_descends (prefixWord ++ tailWord_910066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910076 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_910076 : Nat := 118140960795 + 910076 * 2 ^ 59
def prefixEnd_910076 : Nat := 4983230072969 + 3 ^ 40 * 910076 * 2
def baseEnd_910076 : Nat := 155768806707095519054881

theorem tailTrace_910076 : CollatzResearch.WordTrace tailWord_910076 prefixEnd_910076 155768806707095519054881 := by
  unfold tailWord_910076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596599325478777725803041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22128799100638370301070721 16596599325478777725803041)
  ·
    refine ⟨12447449494109083294352281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16596599325478777725803041 12447449494109083294352281)
    ·
      refine ⟨9335587120581812470764211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12447449494109083294352281 9335587120581812470764211)
      ·
        refine ⟨14003380680872718706146317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335587120581812470764211 14003380680872718706146317)
        ·
          refine ⟨5251267755327269514804869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14003380680872718706146317 5251267755327269514804869)
          ·
            refine ⟨984612704123863034025913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5251267755327269514804869 984612704123863034025913)
            ·
              refine ⟨738459528092897275519435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984612704123863034025913 738459528092897275519435)
              ·
                refine ⟨1107689292139345913279153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738459528092897275519435 1107689292139345913279153)
                ·
                  refine ⟨830766969104509434959365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107689292139345913279153 830766969104509434959365)
                  ·
                    refine ⟨155768806707095519054881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830766969104509434959365 155768806707095519054881)
                    ·
                      rfl

theorem cell23_910076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_910076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910076 prefixEnd_910076 := by exact prefixLift 910076
  have htrace : WordTrace (prefixWord ++ tailWord_910076) baseStart_910076 baseEnd_910076 := by
    simpa [prefixWord, tailWord_910076, baseEnd_910076] using wordTrace_append hprefix tailTrace_910076
  have hstable : (prefixWord ++ tailWord_910076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910076).length < 2 ^ (prefixWord ++ tailWord_910076).sum := by decide
  have hdescent : baseEnd_910076 < baseStart_910076 := by decide
  rcases family_descends (prefixWord ++ tailWord_910076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910115 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 6]
def baseStart_910115 : Nat := 118140960795 + 910115 * 2 ^ 59
def prefixEnd_910115 : Nat := 4983230072969 + 3 ^ 40 * 910115 * 2
def baseEnd_910115 : Nat := 155775481955603968192321

theorem tailTrace_910115 : CollatzResearch.WordTrace tailWord_910115 prefixEnd_910115 155775481955603968192321 := by
  unfold tailWord_910115
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194621097816265112275799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22129747398544176741517199 33194621097816265112275799)
  ·
    refine ⟨49791931646724397668413699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33194621097816265112275799 49791931646724397668413699)
    ·
      refine ⟨74687897470086596502620549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49791931646724397668413699 74687897470086596502620549)
      ·
        refine ⟨14003980775641236844241353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74687897470086596502620549 14003980775641236844241353)
        ·
          refine ⟨10502985581730927633181015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003980775641236844241353 10502985581730927633181015)
          ·
            refine ⟨15754478372596391449771523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502985581730927633181015 15754478372596391449771523)
            ·
              refine ⟨23631717558894587174657285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15754478372596391449771523 23631717558894587174657285)
              ·
                refine ⟨4430947042292735095248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23631717558894587174657285 4430947042292735095248241)
                ·
                  refine ⟨3323210281719551321436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430947042292735095248241 3323210281719551321436181)
                  ·
                    refine ⟨155775481955603968192321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3323210281719551321436181 155775481955603968192321)
                    ·
                      rfl

theorem cell23_910115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_910115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910115 prefixEnd_910115 := by exact prefixLift 910115
  have htrace : WordTrace (prefixWord ++ tailWord_910115) baseStart_910115 baseEnd_910115 := by
    simpa [prefixWord, tailWord_910115, baseEnd_910115] using wordTrace_append hprefix tailTrace_910115
  have hstable : (prefixWord ++ tailWord_910115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910115).length < 2 ^ (prefixWord ++ tailWord_910115).sum := by decide
  have hdescent : baseEnd_910115 < baseStart_910115 := by decide
  rcases family_descends (prefixWord ++ tailWord_910115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910126 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_910126 : Nat := 118140960795 + 910126 * 2 ^ 59
def prefixEnd_910126 : Nat := 4983230072969 + 3 ^ 40 * 910126 * 2
def baseEnd_910126 : Nat := 467332094154011361539413

theorem tailTrace_910126 : CollatzResearch.WordTrace tailWord_910126 prefixEnd_910126 467332094154011361539413 := by
  unfold tailWord_910126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149377787597051748865779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22130014867184275993950821 4149377787597051748865779)
  ·
    refine ⟨6224066681395577623298669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149377787597051748865779 6224066681395577623298669)
    ·
      refine ⟨2334025005523341608737001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6224066681395577623298669 2334025005523341608737001)
      ·
        refine ⟨1750518754142506206552751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334025005523341608737001 1750518754142506206552751)
        ·
          refine ⟨2625778131213759309829127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750518754142506206552751 2625778131213759309829127)
          ·
            refine ⟨3938667196820638964743691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625778131213759309829127 3938667196820638964743691)
            ·
              refine ⟨5908000795230958447115537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938667196820638964743691 5908000795230958447115537)
              ·
                refine ⟨4431000596423218835336653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908000795230958447115537 4431000596423218835336653)
                ·
                  refine ⟨1661625223658707063251245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4431000596423218835336653 1661625223658707063251245)
                  ·
                    refine ⟨623109458872015148719217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661625223658707063251245 623109458872015148719217)
                    ·
                      refine ⟨467332094154011361539413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623109458872015148719217 467332094154011361539413)
                      ·
                        rfl

theorem cell23_910126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_910126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910126 prefixEnd_910126 := by exact prefixLift 910126
  have htrace : WordTrace (prefixWord ++ tailWord_910126) baseStart_910126 baseEnd_910126 := by
    simpa [prefixWord, tailWord_910126, baseEnd_910126] using wordTrace_append hprefix tailTrace_910126
  have hstable : (prefixWord ++ tailWord_910126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910126).length < 2 ^ (prefixWord ++ tailWord_910126).sum := by decide
  have hdescent : baseEnd_910126 < baseStart_910126 := by decide
  rcases family_descends (prefixWord ++ tailWord_910126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910179 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 5]
def baseStart_910179 : Nat := 118140960795 + 910179 * 2 ^ 59
def prefixEnd_910179 : Nat := 4983230072969 + 3 ^ 40 * 910179 * 2
def baseEnd_910179 : Nat := 51928812069855517130741

theorem tailTrace_910179 : CollatzResearch.WordTrace tailWord_910179 prefixEnd_910179 51928812069855517130741 := by
  unfold tailWord_910179
  simp only [CollatzResearch.WordTrace]
  refine ⟨33196955369584404042605591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22131303579722936028403727 33196955369584404042605591)
  ·
    refine ⟨49795433054376606063908387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33196955369584404042605591 49795433054376606063908387)
    ·
      refine ⟨74693149581564909095862581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49795433054376606063908387 74693149581564909095862581)
      ·
        refine ⟨7002482773271710227737117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74693149581564909095862581 7002482773271710227737117)
        ·
          refine ⟨2625931039976891335401419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7002482773271710227737117 2625931039976891335401419)
          ·
            refine ⟨3938896559965337003102129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625931039976891335401419 3938896559965337003102129)
            ·
              refine ⟨2954172419974002752326597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938896559965337003102129 2954172419974002752326597)
              ·
                refine ⟨553907328745125516061237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2954172419974002752326597 553907328745125516061237)
                ·
                  refine ⟨51928812069855517130741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553907328745125516061237 51928812069855517130741)
                  ·
                    rfl

theorem cell23_910179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 5].length) (baseStart_910179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910179 prefixEnd_910179 := by exact prefixLift 910179
  have htrace : WordTrace (prefixWord ++ tailWord_910179) baseStart_910179 baseEnd_910179 := by
    simpa [prefixWord, tailWord_910179, baseEnd_910179] using wordTrace_append hprefix tailTrace_910179
  have hstable : (prefixWord ++ tailWord_910179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910179).length < 2 ^ (prefixWord ++ tailWord_910179).sum := by decide
  have hdescent : baseEnd_910179 < baseStart_910179 := by decide
  rcases family_descends (prefixWord ++ tailWord_910179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910190 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_910190 : Nat := 118140960795 + 910190 * 2 ^ 59
def prefixEnd_910190 : Nat := 4983230072969 + 3 ^ 40 * 910190 * 2
def baseEnd_910190 : Nat := 467364956915899111139119

theorem tailTrace_910190 : CollatzResearch.WordTrace tailWord_910190 prefixEnd_910190 467364956915899111139119 := by
  unfold tailWord_910190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149669571568069115157003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22131571048363035280837349 4149669571568069115157003)
  ·
    refine ⟨6224504357352103672735505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149669571568069115157003 6224504357352103672735505)
    ·
      refine ⟨4668378268014077754551629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6224504357352103672735505 4668378268014077754551629)
      ·
        refine ⟨1750641850505279157956861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4668378268014077754551629 1750641850505279157956861)
        ·
          refine ⟨656490693939479684233823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1750641850505279157956861 656490693939479684233823)
          ·
            refine ⟨984736040909219526350735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656490693939479684233823 984736040909219526350735)
            ·
              refine ⟨1477104061363829289526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984736040909219526350735 1477104061363829289526103)
              ·
                refine ⟨2215656092045743934289155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477104061363829289526103 2215656092045743934289155)
                ·
                  refine ⟨3323484138068615901433733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215656092045743934289155 3323484138068615901433733)
                  ·
                    refine ⟨623153275887865481518825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323484138068615901433733 623153275887865481518825)
                    ·
                      refine ⟨467364956915899111139119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623153275887865481518825 467364956915899111139119)
                      ·
                        rfl

theorem cell23_910190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_910190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910190 prefixEnd_910190 := by exact prefixLift 910190
  have htrace : WordTrace (prefixWord ++ tailWord_910190) baseStart_910190 baseEnd_910190 := by
    simpa [prefixWord, tailWord_910190, baseEnd_910190] using wordTrace_append hprefix tailTrace_910190
  have hstable : (prefixWord ++ tailWord_910190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910190).length < 2 ^ (prefixWord ++ tailWord_910190).sum := by decide
  have hdescent : baseEnd_910190 < baseStart_910190 := by decide
  rcases family_descends (prefixWord ++ tailWord_910190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910226 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_910226 : Nat := 118140960795 + 910226 * 2 ^ 59
def prefixEnd_910226 : Nat := 4983230072969 + 3 ^ 40 * 910226 * 2
def baseEnd_910226 : Nat := 155794480739820323429651

theorem tailTrace_910226 : CollatzResearch.WordTrace tailWord_910226 prefixEnd_910226 155794480739820323429651 := by
  unfold tailWord_910226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8299667400103532767391633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22132446400276087379711021 8299667400103532767391633)
  ·
    refine ⟨6224750550077649575543725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8299667400103532767391633 6224750550077649575543725)
    ·
      refine ⟨2334281456279118590828897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6224750550077649575543725 2334281456279118590828897)
      ·
        refine ⟨1750711092209338943121673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334281456279118590828897 1750711092209338943121673)
        ·
          refine ⟨1313033319157004207341255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750711092209338943121673 1313033319157004207341255)
          ·
            refine ⟨1969549978735506311011883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313033319157004207341255 1969549978735506311011883)
            ·
              refine ⟨2954324968103259466517825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969549978735506311011883 2954324968103259466517825)
              ·
                refine ⟨2215743726077444599888369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954324968103259466517825 2215743726077444599888369)
                ·
                  refine ⟨1661807794558083449916277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2215743726077444599888369 1661807794558083449916277)
                  ·
                    refine ⟨155794480739820323429651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1661807794558083449916277 155794480739820323429651)
                    ·
                      rfl

theorem cell23_910226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_910226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910226 prefixEnd_910226 := by exact prefixLift 910226
  have htrace : WordTrace (prefixWord ++ tailWord_910226) baseStart_910226 baseEnd_910226 := by
    simpa [prefixWord, tailWord_910226, baseEnd_910226] using wordTrace_append hprefix tailTrace_910226
  have hstable : (prefixWord ++ tailWord_910226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910226).length < 2 ^ (prefixWord ++ tailWord_910226).sum := by decide
  have hdescent : baseEnd_910226 < baseStart_910226 := by decide
  rcases family_descends (prefixWord ++ tailWord_910226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910229 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_910229 : Nat := 118140960795 + 910229 * 2 ^ 59
def prefixEnd_910229 : Nat := 4983230072969 + 3 ^ 40 * 910229 * 2
def baseEnd_910229 : Nat := 467384982661424458551439

theorem tailTrace_910229 : CollatzResearch.WordTrace tailWord_910229 prefixEnd_910229 467384982661424458551439 := by
  unfold tailWord_910229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198779019403262581925741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22132519346268841721283827 33198779019403262581925741)
  ·
    refine ⟨12449542132276223468222153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33198779019403262581925741 12449542132276223468222153)
    ·
      refine ⟨9337156599207167601166615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12449542132276223468222153 9337156599207167601166615)
      ·
        refine ⟨14005734898810751401749923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9337156599207167601166615 14005734898810751401749923)
        ·
          refine ⟨21008602348216127102624885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005734898810751401749923 21008602348216127102624885)
          ·
            refine ⟨1969556470145261915871083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21008602348216127102624885 1969556470145261915871083)
            ·
              refine ⟨2954334705217892873806625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969556470145261915871083 2954334705217892873806625)
              ·
                refine ⟨2215751028913419655354969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954334705217892873806625 2215751028913419655354969)
                ·
                  refine ⟨1661813271685064741516227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2215751028913419655354969 1661813271685064741516227)
                  ·
                    refine ⟨2492719907527597112274341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1661813271685064741516227 2492719907527597112274341)
                    ·
                      refine ⟨467384982661424458551439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2492719907527597112274341 467384982661424458551439)
                      ·
                        rfl

theorem cell23_910229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_910229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910229 prefixEnd_910229 := by exact prefixLift 910229
  have htrace : WordTrace (prefixWord ++ tailWord_910229) baseStart_910229 baseEnd_910229 := by
    simpa [prefixWord, tailWord_910229, baseEnd_910229] using wordTrace_append hprefix tailTrace_910229
  have hstable : (prefixWord ++ tailWord_910229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910229).length < 2 ^ (prefixWord ++ tailWord_910229).sum := by decide
  have hdescent : baseEnd_910229 < baseStart_910229 := by decide
  rcases family_descends (prefixWord ++ tailWord_910229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910252 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 6]
def baseStart_910252 : Nat := 118140960795 + 910252 * 2 ^ 59
def prefixEnd_910252 : Nat := 4983230072969 + 3 ^ 40 * 910252 * 2
def baseEnd_910252 : Nat := 51932976968497540951537

theorem tailTrace_910252 : CollatzResearch.WordTrace tailWord_910252 prefixEnd_910252 51932976968497540951537 := by
  unfold tailWord_910252
  simp only [CollatzResearch.WordTrace]
  refine ⟨16599808949159968755006505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22133078598879958340008673 16599808949159968755006505)
  ·
    refine ⟨12449856711869976566254879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16599808949159968755006505 12449856711869976566254879)
    ·
      refine ⟨18674785067804964849382319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12449856711869976566254879 18674785067804964849382319)
      ·
        refine ⟨28012177601707447274073479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18674785067804964849382319 28012177601707447274073479)
        ·
          refine ⟨42018266402561170911110219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28012177601707447274073479 42018266402561170911110219)
          ·
            refine ⟨63027399603841756366665329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42018266402561170911110219 63027399603841756366665329)
            ·
              refine ⟨47270549702881317274998997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63027399603841756366665329 47270549702881317274998997)
              ·
                refine ⟨1107903508661280873632789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47270549702881317274998997 1107903508661280873632789)
                ·
                  refine ⟨51932976968497540951537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1107903508661280873632789 51932976968497540951537)
                  ·
                    rfl

theorem cell23_910252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_910252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910252 prefixEnd_910252 := by exact prefixLift 910252
  have htrace : WordTrace (prefixWord ++ tailWord_910252) baseStart_910252 baseEnd_910252 := by
    simpa [prefixWord, tailWord_910252, baseEnd_910252] using wordTrace_append hprefix tailTrace_910252
  have hstable : (prefixWord ++ tailWord_910252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910252).length < 2 ^ (prefixWord ++ tailWord_910252).sum := by decide
  have hdescent : baseEnd_910252 < baseStart_910252 := by decide
  rcases family_descends (prefixWord ++ tailWord_910252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910290 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_910290 : Nat := 118140960795 + 910290 * 2 ^ 59
def prefixEnd_910290 : Nat := 4983230072969 + 3 ^ 40 * 910290 * 2
def baseEnd_910290 : Nat := 155805434993782906629553

theorem tailTrace_910290 : CollatzResearch.WordTrace tailWord_910290 prefixEnd_910290 155805434993782906629553 := by
  unfold tailWord_910290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300250968045567499974081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22134002581454846666597549 8300250968045567499974081)
  ·
    refine ⟨6225188226034175624980561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8300250968045567499974081 6225188226034175624980561)
    ·
      refine ⟨4668891169525631718735421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6225188226034175624980561 4668891169525631718735421)
      ·
        refine ⟨1750834188572111894525783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4668891169525631718735421 1750834188572111894525783)
        ·
          refine ⟨2626251282858167841788675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750834188572111894525783 2626251282858167841788675)
          ·
            refine ⟨3939376924287251762683013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626251282858167841788675 3939376924287251762683013)
            ·
              refine ⟨738633173303859705503065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3939376924287251762683013 738633173303859705503065)
              ·
                refine ⟨553974879977894779127299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738633173303859705503065 553974879977894779127299)
                ·
                  refine ⟨830962319966842168690949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553974879977894779127299 830962319966842168690949)
                  ·
                    refine ⟨155805434993782906629553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830962319966842168690949 155805434993782906629553)
                    ·
                      rfl

theorem cell23_910290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_910290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910290 prefixEnd_910290 := by exact prefixLift 910290
  have htrace : WordTrace (prefixWord ++ tailWord_910290) baseStart_910290 baseEnd_910290 := by
    simpa [prefixWord, tailWord_910290, baseEnd_910290] using wordTrace_append hprefix tailTrace_910290
  have hstable : (prefixWord ++ tailWord_910290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910290).length < 2 ^ (prefixWord ++ tailWord_910290).sum := by decide
  have hdescent : baseEnd_910290 < baseStart_910290 := by decide
  rcases family_descends (prefixWord ++ tailWord_910290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910319 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_910319 : Nat := 118140960795 + 910319 * 2 ^ 59
def prefixEnd_910319 : Nat := 4983230072969 + 3 ^ 40 * 910319 * 2
def baseEnd_910319 : Nat := 467431195920329106426025

theorem tailTrace_910319 : CollatzResearch.WordTrace tailWord_910319 prefixEnd_910319 467431195920329106426025 := by
  unfold tailWord_910319
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202061589077207952702011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22134707726051471968468007 33202061589077207952702011)
  ·
    refine ⟨49803092383615811929053017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33202061589077207952702011 49803092383615811929053017)
    ·
      refine ⟨37352319287711858946789763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49803092383615811929053017 37352319287711858946789763)
      ·
        refine ⟨56028478931567788420184645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37352319287711858946789763 56028478931567788420184645)
        ·
          refine ⟨10505339799668960328784621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56028478931567788420184645 10505339799668960328784621)
          ·
            refine ⟨3939502424875860123294233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10505339799668960328784621 3939502424875860123294233)
            ·
              refine ⟨2954626818656895092470675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939502424875860123294233 2954626818656895092470675)
              ·
                refine ⟨4431940227985342638706013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954626818656895092470675 4431940227985342638706013)
                ·
                  refine ⟨1661977585494503489514755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4431940227985342638706013 1661977585494503489514755)
                  ·
                    refine ⟨2492966378241755234272133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1661977585494503489514755 2492966378241755234272133)
                    ·
                      refine ⟨467431195920329106426025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2492966378241755234272133 467431195920329106426025)
                      ·
                        rfl

theorem cell23_910319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_910319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910319 prefixEnd_910319 := by exact prefixLift 910319
  have htrace : WordTrace (prefixWord ++ tailWord_910319) baseStart_910319 baseEnd_910319 := by
    simpa [prefixWord, tailWord_910319, baseEnd_910319] using wordTrace_append hprefix tailTrace_910319
  have hstable : (prefixWord ++ tailWord_910319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910319).length < 2 ^ (prefixWord ++ tailWord_910319).sum := by decide
  have hdescent : baseEnd_910319 < baseStart_910319 := by decide
  rcases family_descends (prefixWord ++ tailWord_910319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910329 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_910329 : Nat := 118140960795 + 910329 * 2 ^ 59
def prefixEnd_910329 : Nat := 4983230072969 + 3 ^ 40 * 910329 * 2
def baseEnd_910329 : Nat := 155812110242291355766993

theorem tailTrace_910329 : CollatzResearch.WordTrace tailWord_910329 prefixEnd_910329 155812110242291355766993 := by
  unfold tailWord_910329
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202426319040979660566041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22134950879360653107044027 33202426319040979660566041)
  ·
    refine ⟨24901819739280734745424531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33202426319040979660566041 24901819739280734745424531)
    ·
      refine ⟨37352729608921102118136797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24901819739280734745424531 37352729608921102118136797)
      ·
        refine ⟨14007273603345413294301299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37352729608921102118136797 14007273603345413294301299)
        ·
          refine ⟨21010910405018119941451949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007273603345413294301299 21010910405018119941451949)
          ·
            refine ⟨7879091401881794978044481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21010910405018119941451949 7879091401881794978044481)
            ·
              refine ⟨5909318551411346233533361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7879091401881794978044481 5909318551411346233533361)
              ·
                refine ⟨4431988913558509675150021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909318551411346233533361 4431988913558509675150021)
                ·
                  refine ⟨830997921292220564090629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4431988913558509675150021 830997921292220564090629)
                  ·
                    refine ⟨155812110242291355766993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830997921292220564090629 155812110242291355766993)
                    ·
                      rfl

theorem cell23_910329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_910329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910329 prefixEnd_910329 := by exact prefixLift 910329
  have htrace : WordTrace (prefixWord ++ tailWord_910329) baseStart_910329 baseEnd_910329 := by
    simpa [prefixWord, tailWord_910329, baseEnd_910329] using wordTrace_append hprefix tailTrace_910329
  have hstable : (prefixWord ++ tailWord_910329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910329).length < 2 ^ (prefixWord ++ tailWord_910329).sum := by decide
  have hdescent : baseEnd_910329 < baseStart_910329 := by decide
  rcases family_descends (prefixWord ++ tailWord_910329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910346 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_910346 : Nat := 118140960795 + 910346 * 2 ^ 59
def prefixEnd_910346 : Nat := 4983230072969 + 3 ^ 40 * 910346 * 2
def baseEnd_910346 : Nat := 155815019966000166929467

theorem tailTrace_910346 : CollatzResearch.WordTrace tailWord_910346 prefixEnd_910346 155815019966000166929467 := by
  unfold tailWord_910346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300761589994847890983723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22135364239986261042623261 8300761589994847890983723)
  ·
    refine ⟨12451142384992271836475585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300761589994847890983723 12451142384992271836475585)
    ·
      refine ⟨9338356788744203877356689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12451142384992271836475585 9338356788744203877356689)
      ·
        refine ⟨7003767591558152908017517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9338356788744203877356689 7003767591558152908017517)
        ·
          refine ⟨2626412846834307340506569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7003767591558152908017517 2626412846834307340506569)
          ·
            refine ⟨1969809635125730505379927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626412846834307340506569 1969809635125730505379927)
            ·
              refine ⟨2954714452688595758069891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969809635125730505379927 2954714452688595758069891)
              ·
                refine ⟨4432071679032893637104837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954714452688595758069891 4432071679032893637104837)
                ·
                  refine ⟨831013439818667556957157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4432071679032893637104837 831013439818667556957157)
                  ·
                    refine ⟨155815019966000166929467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 831013439818667556957157 155815019966000166929467)
                    ·
                      rfl

theorem cell23_910346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_910346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910346 prefixEnd_910346 := by exact prefixLift 910346
  have htrace : WordTrace (prefixWord ++ tailWord_910346) baseStart_910346 baseEnd_910346 := by
    simpa [prefixWord, tailWord_910346, baseEnd_910346] using wordTrace_append hprefix tailTrace_910346
  have hstable : (prefixWord ++ tailWord_910346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910346).length < 2 ^ (prefixWord ++ tailWord_910346).sum := by decide
  have hdescent : baseEnd_910346 < baseStart_910346 := by decide
  rcases family_descends (prefixWord ++ tailWord_910346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910386 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_910386 : Nat := 118140960795 + 910386 * 2 ^ 59
def prefixEnd_910386 : Nat := 4983230072969 + 3 ^ 40 * 910386 * 2
def baseEnd_910386 : Nat := 467465599124180344288217

theorem tailTrace_910386 : CollatzResearch.WordTrace tailWord_910386 prefixEnd_910386 467465599124180344288217 := by
  unfold tailWord_910386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301126319958619598847753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22136336853222985596927341 8301126319958619598847753)
  ·
    refine ⟨6225844739968964699135815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8301126319958619598847753 6225844739968964699135815)
    ·
      refine ⟨9338767109953447048703723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225844739968964699135815 9338767109953447048703723)
      ·
        refine ⟨14008150664930170573055585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338767109953447048703723 14008150664930170573055585)
        ·
          refine ⟨10506112998697627929791689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14008150664930170573055585 10506112998697627929791689)
          ·
            refine ⟨7879584749023220947343767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10506112998697627929791689 7879584749023220947343767)
            ·
              refine ⟨11819377123534831421015651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879584749023220947343767 11819377123534831421015651)
              ·
                refine ⟨17729065685302247131523477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819377123534831421015651 17729065685302247131523477)
                ·
                  refine ⟨831049953998542834290163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17729065685302247131523477 831049953998542834290163)
                  ·
                    refine ⟨1246574930997814251435245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 831049953998542834290163 1246574930997814251435245)
                    ·
                      refine ⟨467465599124180344288217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246574930997814251435245 467465599124180344288217)
                      ·
                        rfl

theorem cell23_910386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_910386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910386 prefixEnd_910386 := by exact prefixLift 910386
  have htrace : WordTrace (prefixWord ++ tailWord_910386) baseStart_910386 baseEnd_910386 := by
    simpa [prefixWord, tailWord_910386, baseEnd_910386] using wordTrace_append hprefix tailTrace_910386
  have hstable : (prefixWord ++ tailWord_910386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910386).length < 2 ^ (prefixWord ++ tailWord_910386).sum := by decide
  have hdescent : baseEnd_910386 < baseStart_910386 := by decide
  rcases family_descends (prefixWord ++ tailWord_910386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910420 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_910420 : Nat := 118140960795 + 910420 * 2 ^ 59
def prefixEnd_910420 : Nat := 4983230072969 + 3 ^ 40 * 910420 * 2
def baseEnd_910420 : Nat := 467483057466433211263061

theorem tailTrace_910420 : CollatzResearch.WordTrace tailWord_910420 prefixEnd_910420 467483057466433211263061 := by
  unfold tailWord_910420
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602872680855651101064357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22137163574474201468085809 16602872680855651101064357)
  ·
    refine ⟨3113038627660434581449567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16602872680855651101064357 3113038627660434581449567)
    ·
      refine ⟨4669557941490651872174351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3113038627660434581449567 4669557941490651872174351)
      ·
        refine ⟨7004336912235977808261527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669557941490651872174351 7004336912235977808261527)
        ·
          refine ⟨10506505368353966712392291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004336912235977808261527 10506505368353966712392291)
          ·
            refine ⟨15759758052530950068588437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10506505368353966712392291 15759758052530950068588437)
            ·
              refine ⟨738738658712388284465083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15759758052530950068588437 738738658712388284465083)
              ·
                refine ⟨1108107988068582426697625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738738658712388284465083 1108107988068582426697625)
                ·
                  refine ⟨831080991051436820023219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108107988068582426697625 831080991051436820023219)
                  ·
                    refine ⟨1246621486577155230034829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 831080991051436820023219 1246621486577155230034829)
                    ·
                      refine ⟨467483057466433211263061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246621486577155230034829 467483057466433211263061)
                      ·
                        rfl

theorem cell23_910420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_910420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910420 prefixEnd_910420 := by exact prefixLift 910420
  have htrace : WordTrace (prefixWord ++ tailWord_910420) baseStart_910420 baseEnd_910420 := by
    simpa [prefixWord, tailWord_910420, baseEnd_910420] using wordTrace_append hprefix tailTrace_910420
  have hstable : (prefixWord ++ tailWord_910420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910420).length < 2 ^ (prefixWord ++ tailWord_910420).sum := by decide
  have hdescent : baseEnd_910420 < baseStart_910420 := by decide
  rcases family_descends (prefixWord ++ tailWord_910420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910446 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_910446 : Nat := 118140960795 + 910446 * 2 ^ 59
def prefixEnd_910446 : Nat := 4983230072969 + 3 ^ 40 * 910446 * 2
def baseEnd_910446 : Nat := 467496407963450109537941

theorem tailTrace_910446 : CollatzResearch.WordTrace tailWord_910446 prefixEnd_910446 467496407963450109537941 := by
  unfold tailWord_910446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150836707452138580321899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22137795773078072428383461 4150836707452138580321899)
  ·
    refine ⟨6226255061178207870482849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150836707452138580321899 6226255061178207870482849)
    ·
      refine ⟨4669691295883655902862137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6226255061178207870482849 4669691295883655902862137)
      ·
        refine ⟨3502268471912741927146603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4669691295883655902862137 3502268471912741927146603)
        ·
          refine ⟨5253402707869112890719905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502268471912741927146603 5253402707869112890719905)
          ·
            refine ⟨3940052030901834668039929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253402707869112890719905 3940052030901834668039929)
            ·
              refine ⟨2955039023176376001029947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940052030901834668039929 2955039023176376001029947)
              ·
                refine ⟨4432558534764564001544921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955039023176376001029947 4432558534764564001544921)
                ·
                  refine ⟨3324418901073423001158691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432558534764564001544921 3324418901073423001158691)
                  ·
                    refine ⟨4986628351610134501738037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3324418901073423001158691 4986628351610134501738037)
                    ·
                      refine ⟨467496407963450109537941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4986628351610134501738037 467496407963450109537941)
                      ·
                        rfl

theorem cell23_910446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_910446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910446 prefixEnd_910446 := by exact prefixLift 910446
  have htrace : WordTrace (prefixWord ++ tailWord_910446) baseStart_910446 baseEnd_910446 := by
    simpa [prefixWord, tailWord_910446, baseEnd_910446] using wordTrace_append hprefix tailTrace_910446
  have hstable : (prefixWord ++ tailWord_910446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910446).length < 2 ^ (prefixWord ++ tailWord_910446).sum := by decide
  have hdescent : baseEnd_910446 < baseStart_910446 := by decide
  rcases family_descends (prefixWord ++ tailWord_910446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910459 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3]
def baseStart_910459 : Nat := 118140960795 + 910459 * 2 ^ 59
def prefixEnd_910459 : Nat := 4983230072969 + 3 ^ 40 * 910459 * 2
def baseEnd_910459 : Nat := 467503083211958558675381

theorem tailTrace_910459 : CollatzResearch.WordTrace tailWord_910459 prefixEnd_910459 467503083211958558675381 := by
  unfold tailWord_910459
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207167808570011862798431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22138111872380007908532287 33207167808570011862798431)
  ·
    refine ⟨49810751712855017794197647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33207167808570011862798431 49810751712855017794197647)
    ·
      refine ⟨74716127569282526691296471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49810751712855017794197647 74716127569282526691296471)
      ·
        refine ⟨112074191353923790036944707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74716127569282526691296471 112074191353923790036944707)
        ·
          refine ⟨168111287030885685055417061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112074191353923790036944707 168111287030885685055417061)
          ·
            refine ⟨31520866318291065947890699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168111287030885685055417061 31520866318291065947890699)
            ·
              refine ⟨47281299477436598921836049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31520866318291065947890699 47281299477436598921836049)
              ·
                refine ⟨35460974608077449191377037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47281299477436598921836049 35460974608077449191377037)
                ·
                  refine ⟨13297865478029043446766389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35460974608077449191377037 13297865478029043446766389)
                  ·
                    refine ⟨1246674888565222823134349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297865478029043446766389 1246674888565222823134349)
                    ·
                      refine ⟨467503083211958558675381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246674888565222823134349 467503083211958558675381)
                      ·
                        rfl

theorem cell23_910459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].length) (baseStart_910459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910459 prefixEnd_910459 := by exact prefixLift 910459
  have htrace : WordTrace (prefixWord ++ tailWord_910459) baseStart_910459 baseEnd_910459 := by
    simpa [prefixWord, tailWord_910459, baseEnd_910459] using wordTrace_append hprefix tailTrace_910459
  have hstable : (prefixWord ++ tailWord_910459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910459).length < 2 ^ (prefixWord ++ tailWord_910459).sum := by decide
  have hdescent : baseEnd_910459 < baseStart_910459 := by decide
  rcases family_descends (prefixWord ++ tailWord_910459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910460 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_910460 : Nat := 118140960795 + 910460 * 2 ^ 59
def prefixEnd_910460 : Nat := 4983230072969 + 3 ^ 40 * 910460 * 2
def baseEnd_910460 : Nat := 467503596692613054762877

theorem tailTrace_910460 : CollatzResearch.WordTrace tailWord_910460 prefixEnd_910460 467503596692613054762877 := by
  unfold tailWord_910460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16603602140783194516792417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22138136187710926022389889 16603602140783194516792417)
  ·
    refine ⟨12452701605587395887594313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16603602140783194516792417 12452701605587395887594313)
    ·
      refine ⟨9339526204190546915695735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12452701605587395887594313 9339526204190546915695735)
      ·
        refine ⟨14009289306285820373543603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339526204190546915695735 14009289306285820373543603)
        ·
          refine ⟨21013933959428730560315405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009289306285820373543603 21013933959428730560315405)
          ·
            refine ⟨7880225234785773960118277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21013933959428730560315405 7880225234785773960118277)
            ·
              refine ⟨1477542231522332617522177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7880225234785773960118277 1477542231522332617522177)
              ·
                refine ⟨1108156673641749463141633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477542231522332617522177 1108156673641749463141633)
                ·
                  refine ⟨831117505231312097356225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108156673641749463141633 831117505231312097356225)
                  ·
                    refine ⟨623338128923484073017169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831117505231312097356225 623338128923484073017169)
                    ·
                      refine ⟨467503596692613054762877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623338128923484073017169 467503596692613054762877)
                      ·
                        rfl

theorem cell23_910460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_910460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910460 prefixEnd_910460 := by exact prefixLift 910460
  have htrace : WordTrace (prefixWord ++ tailWord_910460) baseStart_910460 baseEnd_910460 := by
    simpa [prefixWord, tailWord_910460, baseEnd_910460] using wordTrace_append hprefix tailTrace_910460
  have hstable : (prefixWord ++ tailWord_910460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910460).length < 2 ^ (prefixWord ++ tailWord_910460).sum := by decide
  have hdescent : baseEnd_910460 < baseStart_910460 := by decide
  rcases family_descends (prefixWord ++ tailWord_910460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910536 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_910536 : Nat := 118140960795 + 910536 * 2 ^ 59
def prefixEnd_910536 : Nat := 4983230072969 + 3 ^ 40 * 910536 * 2
def baseEnd_910536 : Nat := 467542621222354757412527

theorem tailTrace_910536 : CollatzResearch.WordTrace tailWord_910536 prefixEnd_910536 467542621222354757412527 := by
  unfold tailWord_910536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16604988114645527006675731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22139984152860702675567641 16604988114645527006675731)
  ·
    refine ⟨24907482171968290510013597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16604988114645527006675731 24907482171968290510013597)
    ·
      refine ⟨9340305814488108941255099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24907482171968290510013597 9340305814488108941255099)
      ·
        refine ⟨14010458721732163411882649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340305814488108941255099 14010458721732163411882649)
        ·
          refine ⟨10507844041299122558911987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14010458721732163411882649 10507844041299122558911987)
          ·
            refine ⟨15761766061948683838367981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507844041299122558911987 15761766061948683838367981)
            ·
              refine ⟨5910662273230756439387993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15761766061948683838367981 5910662273230756439387993)
              ·
                refine ⟨4432996704923067329540995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910662273230756439387993 4432996704923067329540995)
                ·
                  refine ⟨6649495057384600994311493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432996704923067329540995 6649495057384600994311493)
                  ·
                    refine ⟨1246780323259612686433405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649495057384600994311493 1246780323259612686433405)
                    ·
                      refine ⟨467542621222354757412527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246780323259612686433405 467542621222354757412527)
                      ·
                        rfl

theorem cell23_910536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_910536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910536 prefixEnd_910536 := by exact prefixLift 910536
  have htrace : WordTrace (prefixWord ++ tailWord_910536) baseStart_910536 baseEnd_910536 := by
    simpa [prefixWord, tailWord_910536, baseEnd_910536] using wordTrace_append hprefix tailTrace_910536
  have hstable : (prefixWord ++ tailWord_910536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910536).length < 2 ^ (prefixWord ++ tailWord_910536).sum := by decide
  have hdescent : baseEnd_910536 < baseStart_910536 := by decide
  rcases family_descends (prefixWord ++ tailWord_910536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910546 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_910546 : Nat := 118140960795 + 910546 * 2 ^ 59
def prefixEnd_910546 : Nat := 4983230072969 + 3 ^ 40 * 910546 * 2
def baseEnd_910546 : Nat := 467547756028899718287481

theorem tailTrace_910546 : CollatzResearch.WordTrace tailWord_910546 prefixEnd_910546 467547756028899718287481 := by
  unfold tailWord_910546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302585239813706430303873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22140227306169883814143661 8302585239813706430303873)
  ·
    refine ⟨6226938929860279822727905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8302585239813706430303873 6226938929860279822727905)
    ·
      refine ⟨4670204197395209867045929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6226938929860279822727905 4670204197395209867045929)
      ·
        refine ⟨3502653148046407400284447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4670204197395209867045929 3502653148046407400284447)
        ·
          refine ⟨5253979722069611100426671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502653148046407400284447 5253979722069611100426671)
          ·
            refine ⟨7880969583104416650640007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253979722069611100426671 7880969583104416650640007)
            ·
              refine ⟨11821454374656624975960011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880969583104416650640007 11821454374656624975960011)
              ·
                refine ⟨17732181561984937463940017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11821454374656624975960011 17732181561984937463940017)
                ·
                  refine ⟨13299136171488703097955013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17732181561984937463940017 13299136171488703097955013)
                  ·
                    refine ⟨2493588032154131830866565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13299136171488703097955013 2493588032154131830866565)
                    ·
                      refine ⟨467547756028899718287481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2493588032154131830866565 467547756028899718287481)
                      ·
                        rfl

theorem cell23_910546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_910546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910546 prefixEnd_910546 := by exact prefixLift 910546
  have htrace : WordTrace (prefixWord ++ tailWord_910546) baseStart_910546 baseEnd_910546 := by
    simpa [prefixWord, tailWord_910546, baseEnd_910546] using wordTrace_append hprefix tailTrace_910546
  have hstable : (prefixWord ++ tailWord_910546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910546).length < 2 ^ (prefixWord ++ tailWord_910546).sum := by decide
  have hdescent : baseEnd_910546 < baseStart_910546 := by decide
  rcases family_descends (prefixWord ++ tailWord_910546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910560 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 1, 4]
def baseStart_910560 : Nat := 118140960795 + 910560 * 2 ^ 59
def prefixEnd_910560 : Nat := 4983230072969 + 3 ^ 40 * 910560 * 2
def baseEnd_910560 : Nat := 155851648252687554504139

theorem tailTrace_910560 : CollatzResearch.WordTrace tailWord_910560 prefixEnd_910560 155851648252687554504139 := by
  unfold tailWord_910560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605425790602053056112567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22140567720802737408150089 16605425790602053056112567)
  ·
    refine ⟨24908138685903079584168851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16605425790602053056112567 24908138685903079584168851)
    ·
      refine ⟨37362208028854619376253277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24908138685903079584168851 37362208028854619376253277)
      ·
        refine ⟨14010828010820482266094979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37362208028854619376253277 14010828010820482266094979)
        ·
          refine ⟨21016242016230723399142469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010828010820482266094979 21016242016230723399142469)
          ·
            refine ⟨3940545378043260637339213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21016242016230723399142469 3940545378043260637339213)
            ·
              refine ⟨1477704516766222739002205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3940545378043260637339213 1477704516766222739002205)
              ·
                refine ⟨554139193787333527125827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477704516766222739002205 554139193787333527125827)
                ·
                  refine ⟨831208790681000290688741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554139193787333527125827 831208790681000290688741)
                  ·
                    refine ⟨155851648252687554504139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 831208790681000290688741 155851648252687554504139)
                    ·
                      rfl

theorem cell23_910560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_910560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910560 prefixEnd_910560 := by exact prefixLift 910560
  have htrace : WordTrace (prefixWord ++ tailWord_910560) baseStart_910560 baseEnd_910560 := by
    simpa [prefixWord, tailWord_910560, baseEnd_910560] using wordTrace_append hprefix tailTrace_910560
  have hstable : (prefixWord ++ tailWord_910560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910560).length < 2 ^ (prefixWord ++ tailWord_910560).sum := by decide
  have hdescent : baseEnd_910560 < baseStart_910560 := by decide
  rcases family_descends (prefixWord ++ tailWord_910560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910586 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_910586 : Nat := 118140960795 + 910586 * 2 ^ 59
def prefixEnd_910586 : Nat := 4983230072969 + 3 ^ 40 * 910586 * 2
def baseEnd_910586 : Nat := 155856098418359853929099

theorem tailTrace_910586 : CollatzResearch.WordTrace tailWord_910586 prefixEnd_910586 155856098418359853929099 := by
  unfold tailWord_910586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302949969777478138167903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22141199919406608368447741 8302949969777478138167903)
  ·
    refine ⟨12454424954666217207251855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8302949969777478138167903 12454424954666217207251855)
    ·
      refine ⟨18681637431999325810877783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454424954666217207251855 18681637431999325810877783)
      ·
        refine ⟨28022456147998988716316675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18681637431999325810877783 28022456147998988716316675)
        ·
          refine ⟨42033684221998483074475013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28022456147998988716316675 42033684221998483074475013)
          ·
            refine ⟨7881315791624715576464065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42033684221998483074475013 7881315791624715576464065)
            ·
              refine ⟨5910986843718536682348049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881315791624715576464065 5910986843718536682348049)
              ·
                refine ⟨4433240132788902511761037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910986843718536682348049 4433240132788902511761037)
                ·
                  refine ⟨1662465049795838441910389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4433240132788902511761037 1662465049795838441910389)
                  ·
                    refine ⟨155856098418359853929099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1662465049795838441910389 155856098418359853929099)
                    ·
                      rfl

theorem cell23_910586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_910586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910586 prefixEnd_910586 := by exact prefixLift 910586
  have htrace : WordTrace (prefixWord ++ tailWord_910586) baseStart_910586 baseEnd_910586 := by
    simpa [prefixWord, tailWord_910586, baseEnd_910586] using wordTrace_append hprefix tailTrace_910586
  have hstable : (prefixWord ++ tailWord_910586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910586).length < 2 ^ (prefixWord ++ tailWord_910586).sum := by decide
  have hdescent : baseEnd_910586 < baseStart_910586 := by decide
  rcases family_descends (prefixWord ++ tailWord_910586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910590 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_910590 : Nat := 118140960795 + 910590 * 2 ^ 59
def prefixEnd_910590 : Nat := 4983230072969 + 3 ^ 40 * 910590 * 2
def baseEnd_910590 : Nat := 51952261019744171793031

theorem tailTrace_910590 : CollatzResearch.WordTrace tailWord_910590 prefixEnd_910590 51952261019744171793031 := by
  unfold tailWord_910590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151493221386927654477153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22141297180730280823878149 4151493221386927654477153)
  ·
    refine ⟨3113619916040195740857865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4151493221386927654477153 3113619916040195740857865)
    ·
      refine ⟨2335214937030146805643399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3113619916040195740857865 2335214937030146805643399)
      ·
        refine ⟨3502822405545220208465099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335214937030146805643399 3502822405545220208465099)
        ·
          refine ⟨5254233608317830312697649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502822405545220208465099 5254233608317830312697649)
          ·
            refine ⟨3940675206238372734523237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254233608317830312697649 3940675206238372734523237)
            ·
              refine ⟨738876601169694887723107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3940675206238372734523237 738876601169694887723107)
              ·
                refine ⟨1108314901754542331584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738876601169694887723107 1108314901754542331584661)
                ·
                  refine ⟨51952261019744171793031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1108314901754542331584661 51952261019744171793031)
                  ·
                    rfl

theorem cell23_910590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_910590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910590 prefixEnd_910590 := by exact prefixLift 910590
  have htrace : WordTrace (prefixWord ++ tailWord_910590) baseStart_910590 baseEnd_910590 := by
    simpa [prefixWord, tailWord_910590, baseEnd_910590] using wordTrace_append hprefix tailTrace_910590
  have hstable : (prefixWord ++ tailWord_910590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910590).length < 2 ^ (prefixWord ++ tailWord_910590).sum := by decide
  have hdescent : baseEnd_910590 < baseStart_910590 := by decide
  rcases family_descends (prefixWord ++ tailWord_910590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910603 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 1, 5]
def baseStart_910603 : Nat := 118140960795 + 910603 * 2 ^ 59
def prefixEnd_910603 : Nat := 4983230072969 + 3 ^ 40 * 910603 * 2
def baseEnd_910603 : Nat := 155859008142068665091573

theorem tailTrace_910603 : CollatzResearch.WordTrace tailWord_910603 prefixEnd_910603 155859008142068665091573 := by
  unfold tailWord_910603
  simp only [CollatzResearch.WordTrace]
  refine ⟨33212419920048324456040463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22141613280032216304026975 33212419920048324456040463)
  ·
    refine ⟨49818629880072486684060695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33212419920048324456040463 49818629880072486684060695)
    ·
      refine ⟨74727944820108730026091043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49818629880072486684060695 74727944820108730026091043)
      ·
        refine ⟨112091917230163095039136565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74727944820108730026091043 112091917230163095039136565)
        ·
          refine ⟨10508617240327790159919053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112091917230163095039136565 10508617240327790159919053)
          ·
            refine ⟨3940731465122921309969645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10508617240327790159919053 3940731465122921309969645)
            ·
              refine ⟨1477774299421095491238617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3940731465122921309969645 1477774299421095491238617)
              ·
                refine ⟨1108330724565821618428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477774299421095491238617 1108330724565821618428963)
                ·
                  refine ⟨1662496086848732427643445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108330724565821618428963 1662496086848732427643445)
                  ·
                    refine ⟨155859008142068665091573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1662496086848732427643445 155859008142068665091573)
                    ·
                      rfl

theorem cell23_910603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 5].length) (baseStart_910603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910603 prefixEnd_910603 := by exact prefixLift 910603
  have htrace : WordTrace (prefixWord ++ tailWord_910603) baseStart_910603 baseEnd_910603 := by
    simpa [prefixWord, tailWord_910603, baseEnd_910603] using wordTrace_append hprefix tailTrace_910603
  have hstable : (prefixWord ++ tailWord_910603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910603).length < 2 ^ (prefixWord ++ tailWord_910603).sum := by decide
  have hdescent : baseEnd_910603 < baseStart_910603 := by decide
  rcases family_descends (prefixWord ++ tailWord_910603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910616 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_910616 : Nat := 118140960795 + 910616 * 2 ^ 59
def prefixEnd_910616 : Nat := 4983230072969 + 3 ^ 40 * 910616 * 2
def baseEnd_910616 : Nat := 155861233224904814804053

theorem tailTrace_910616 : CollatzResearch.WordTrace tailWord_910616 prefixEnd_910616 155861233224904814804053 := by
  unfold tailWord_910616
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606447034500613838131851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22141929379334151784175801 16606447034500613838131851)
  ·
    refine ⟨24909670551750920757197777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16606447034500613838131851 24909670551750920757197777)
    ·
      refine ⟨18682252913813190567898333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24909670551750920757197777 18682252913813190567898333)
      ·
        refine ⟨7005844842679946462961875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18682252913813190567898333 7005844842679946462961875)
        ·
          refine ⟨10508767264019919694442813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005844842679946462961875 10508767264019919694442813)
          ·
            refine ⟨3940787724007469885416055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10508767264019919694442813 3940787724007469885416055)
            ·
              refine ⟨5911181586011204828124083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940787724007469885416055 5911181586011204828124083)
              ·
                refine ⟨8866772379016807242186125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911181586011204828124083 8866772379016807242186125)
                ·
                  refine ⟨3325039642131302715819797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8866772379016807242186125 3325039642131302715819797)
                  ·
                    refine ⟨155861233224904814804053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3325039642131302715819797 155861233224904814804053)
                    ·
                      rfl

theorem cell23_910616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_910616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910616 prefixEnd_910616 := by exact prefixLift 910616
  have htrace : WordTrace (prefixWord ++ tailWord_910616) baseStart_910616 baseEnd_910616 := by
    simpa [prefixWord, tailWord_910616, baseEnd_910616] using wordTrace_append hprefix tailTrace_910616
  have hstable : (prefixWord ++ tailWord_910616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910616).length < 2 ^ (prefixWord ++ tailWord_910616).sum := by decide
  have hdescent : baseEnd_910616 < baseStart_910616 := by decide
  rcases family_descends (prefixWord ++ tailWord_910616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910634 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_910634 : Nat := 118140960795 + 910634 * 2 ^ 59
def prefixEnd_910634 : Nat := 4983230072969 + 3 ^ 40 * 910634 * 2
def baseEnd_910634 : Nat := 467592942326495373987077

theorem tailTrace_910634 : CollatzResearch.WordTrace tailWord_910634 prefixEnd_910634 467592942326495373987077 := by
  unfold tailWord_910634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303387645734004187604739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22142367055290677833612637 8303387645734004187604739)
  ·
    refine ⟨12455081468601006281407109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303387645734004187604739 12455081468601006281407109)
    ·
      refine ⟨2335327775362688677763833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12455081468601006281407109 2335327775362688677763833)
      ·
        refine ⟨1751495831522016508322875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335327775362688677763833 1751495831522016508322875)
        ·
          refine ⟨2627243747283024762484313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751495831522016508322875 2627243747283024762484313)
          ·
            refine ⟨1970432810462268571863235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627243747283024762484313 1970432810462268571863235)
            ·
              refine ⟨2955649215693402857794853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970432810462268571863235 2955649215693402857794853)
              ·
                refine ⟨554184227942513035836535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2955649215693402857794853 554184227942513035836535)
                ·
                  refine ⟨831276341913769553754803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554184227942513035836535 831276341913769553754803)
                  ·
                    refine ⟨1246914512870654330632205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 831276341913769553754803 1246914512870654330632205)
                    ·
                      refine ⟨467592942326495373987077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246914512870654330632205 467592942326495373987077)
                      ·
                        rfl

theorem cell23_910634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_910634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910634 prefixEnd_910634 := by exact prefixLift 910634
  have htrace : WordTrace (prefixWord ++ tailWord_910634) baseStart_910634 baseEnd_910634 := by
    simpa [prefixWord, tailWord_910634, baseEnd_910634] using wordTrace_append hprefix tailTrace_910634
  have hstable : (prefixWord ++ tailWord_910634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910634).length < 2 ^ (prefixWord ++ tailWord_910634).sum := by decide
  have hdescent : baseEnd_910634 < baseStart_910634 := by decide
  rcases family_descends (prefixWord ++ tailWord_910634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910636 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_910636 : Nat := 118140960795 + 910636 * 2 ^ 59
def prefixEnd_910636 : Nat := 4983230072969 + 3 ^ 40 * 910636 * 2
def baseEnd_910636 : Nat := 467593969287804366162067

theorem tailTrace_910636 : CollatzResearch.WordTrace tailWord_910636 prefixEnd_910636 467593969287804366162067 := by
  unfold tailWord_910636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606811764464385545995881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22142415685952514061327841 16606811764464385545995881)
  ·
    refine ⟨12455108823348289159496911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16606811764464385545995881 12455108823348289159496911)
    ·
      refine ⟨18682663235022433739245367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455108823348289159496911 18682663235022433739245367)
      ·
        refine ⟨28023994852533650608868051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18682663235022433739245367 28023994852533650608868051)
        ·
          refine ⟨42035992278800475913302077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28023994852533650608868051 42035992278800475913302077)
          ·
            refine ⟨15763497104550178467488279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42035992278800475913302077 15763497104550178467488279)
            ·
              refine ⟨23645245656825267701232419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15763497104550178467488279 23645245656825267701232419)
              ·
                refine ⟨35467868485237901551848629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23645245656825267701232419 35467868485237901551848629)
                ·
                  refine ⟨3325112670491053270485809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35467868485237901551848629 3325112670491053270485809)
                  ·
                    refine ⟨2493834502868289952864357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325112670491053270485809 2493834502868289952864357)
                    ·
                      refine ⟨467593969287804366162067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2493834502868289952864357 467593969287804366162067)
                      ·
                        rfl

theorem cell23_910636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_910636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910636 prefixEnd_910636 := by exact prefixLift 910636
  have htrace : WordTrace (prefixWord ++ tailWord_910636) baseStart_910636 baseEnd_910636 := by
    simpa [prefixWord, tailWord_910636, baseEnd_910636] using wordTrace_append hprefix tailTrace_910636
  have hstable : (prefixWord ++ tailWord_910636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910636).length < 2 ^ (prefixWord ++ tailWord_910636).sum := by decide
  have hdescent : baseEnd_910636 < baseStart_910636 := by decide
  rcases family_descends (prefixWord ++ tailWord_910636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910640 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2]
def baseStart_910640 : Nat := 118140960795 + 910640 * 2 ^ 59
def prefixEnd_910640 : Nat := 4983230072969 + 3 ^ 40 * 910640 * 2
def baseEnd_910640 : Nat := 467596023210422350512049

theorem tailTrace_910640 : CollatzResearch.WordTrace tailWord_910640 prefixEnd_910640 467596023210422350512049 := by
  unfold tailWord_910640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606884710457139887568687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22142512947276186516758249 16606884710457139887568687)
  ·
    refine ⟨24910327065685709831353031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16606884710457139887568687 24910327065685709831353031)
    ·
      refine ⟨37365490598528564747029547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24910327065685709831353031 37365490598528564747029547)
      ·
        refine ⟨56048235897792847120544321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37365490598528564747029547 56048235897792847120544321)
        ·
          refine ⟨42036176923344635340408241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56048235897792847120544321 42036176923344635340408241)
          ·
            refine ⟨31527132692508476505306181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42036176923344635340408241 31527132692508476505306181)
            ·
              refine ⟨5911337379845339344744909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31527132692508476505306181 5911337379845339344744909)
              ·
                refine ⟨2216751517442002254279341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5911337379845339344744909 2216751517442002254279341)
                ·
                  refine ⟨831281819040750845354753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2216751517442002254279341 831281819040750845354753)
                  ·
                    refine ⟨623461364280563134016065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831281819040750845354753 623461364280563134016065)
                    ·
                      refine ⟨467596023210422350512049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623461364280563134016065 467596023210422350512049)
                      ·
                        rfl

theorem cell23_910640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2].length) (baseStart_910640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910640 prefixEnd_910640 := by exact prefixLift 910640
  have htrace : WordTrace (prefixWord ++ tailWord_910640) baseStart_910640 baseEnd_910640 := by
    simpa [prefixWord, tailWord_910640, baseEnd_910640] using wordTrace_append hprefix tailTrace_910640
  have hstable : (prefixWord ++ tailWord_910640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910640).length < 2 ^ (prefixWord ++ tailWord_910640).sum := by decide
  have hdescent : baseEnd_910640 < baseStart_910640 := by decide
  rcases family_descends (prefixWord ++ tailWord_910640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910643 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3]
def baseStart_910643 : Nat := 118140960795 + 910643 * 2 ^ 59
def prefixEnd_910643 : Nat := 4983230072969 + 3 ^ 40 * 910643 * 2
def baseEnd_910643 : Nat := 467597563652385838774535

theorem tailTrace_910643 : CollatzResearch.WordTrace tailWord_910643 prefixEnd_910643 467597563652385838774535 := by
  unfold tailWord_910643
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213878839903411287496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22142585893268940858331055 33213878839903411287496583)
  ·
    refine ⟨49820818259855116931244875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33213878839903411287496583 49820818259855116931244875)
    ·
      refine ⟨74731227389782675396867313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49820818259855116931244875 74731227389782675396867313)
      ·
        refine ⟨56048420542337006547650485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74731227389782675396867313 56048420542337006547650485)
        ·
          refine ⟨5254539425844094363842233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56048420542337006547650485 5254539425844094363842233)
          ·
            refine ⟨3940904569383070772881675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254539425844094363842233 3940904569383070772881675)
            ·
              refine ⟨5911356854074606159322513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940904569383070772881675 5911356854074606159322513)
              ·
                refine ⟨4433517640555954619491885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911356854074606159322513 4433517640555954619491885)
                ·
                  refine ⟨1662569115208482982309457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4433517640555954619491885 1662569115208482982309457)
                  ·
                    refine ⟨1246926836406362236732093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662569115208482982309457 1246926836406362236732093)
                    ·
                      refine ⟨467597563652385838774535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246926836406362236732093 467597563652385838774535)
                      ·
                        rfl

theorem cell23_910643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_910643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910643 prefixEnd_910643 := by exact prefixLift 910643
  have htrace : WordTrace (prefixWord ++ tailWord_910643) baseStart_910643 baseEnd_910643 := by
    simpa [prefixWord, tailWord_910643, baseEnd_910643] using wordTrace_append hprefix tailTrace_910643
  have hstable : (prefixWord ++ tailWord_910643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910643).length < 2 ^ (prefixWord ++ tailWord_910643).sum := by decide
  have hdescent : baseEnd_910643 < baseStart_910643 := by decide
  rcases family_descends (prefixWord ++ tailWord_910643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910657 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_910657 : Nat := 118140960795 + 910657 * 2 ^ 59
def prefixEnd_910657 : Nat := 4983230072969 + 3 ^ 40 * 910657 * 2
def baseEnd_910657 : Nat := 467604752381548783999471

theorem tailTrace_910657 : CollatzResearch.WordTrace tailWord_910657 prefixEnd_910657 467604752381548783999471 := by
  unfold tailWord_910657
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214389461852691678506225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22142926307901794452337483 33214389461852691678506225)
  ·
    refine ⟨24910792096389518758879669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33214389461852691678506225 24910792096389518758879669)
    ·
      refine ⟨2335386759036517383644969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24910792096389518758879669 2335386759036517383644969)
      ·
        refine ⟨1751540069277388037733727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335386759036517383644969 1751540069277388037733727)
        ·
          refine ⟨2627310103916082056600591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751540069277388037733727 2627310103916082056600591)
          ·
            refine ⟨3940965155874123084900887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627310103916082056600591 3940965155874123084900887)
            ·
              refine ⟨5911447733811184627351331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940965155874123084900887 5911447733811184627351331)
              ·
                refine ⟨8867171600716776941026997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911447733811184627351331 8867171600716776941026997)
                ·
                  refine ⟨831297337567197838221281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8867171600716776941026997 831297337567197838221281)
                  ·
                    refine ⟨623473003175398378665961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831297337567197838221281 623473003175398378665961)
                    ·
                      refine ⟨467604752381548783999471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623473003175398378665961 467604752381548783999471)
                      ·
                        rfl

theorem cell23_910657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_910657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910657 prefixEnd_910657 := by exact prefixLift 910657
  have htrace : WordTrace (prefixWord ++ tailWord_910657) baseStart_910657 baseEnd_910657 := by
    simpa [prefixWord, tailWord_910657, baseEnd_910657] using wordTrace_append hprefix tailTrace_910657
  have hstable : (prefixWord ++ tailWord_910657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910657).length < 2 ^ (prefixWord ++ tailWord_910657).sum := by decide
  have hdescent : baseEnd_910657 < baseStart_910657 := by decide
  rcases family_descends (prefixWord ++ tailWord_910657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910663 : List Nat := [1, 1, 4, 1, 2, 4, 3, 7]
def baseStart_910663 : Nat := 118140960795 + 910663 * 2 ^ 59
def prefixEnd_910663 : Nat := 4983230072969 + 3 ^ 40 * 910663 * 2
def baseEnd_910663 : Nat := 17318808639462065204609

theorem tailTrace_910663 : CollatzResearch.WordTrace tailWord_910663 prefixEnd_910663 17318808639462065204609 := by
  unfold tailWord_910663
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214608299830954703224643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22143072199887303135483095 33214608299830954703224643)
  ·
    refine ⟨49821912449746432054836965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33214608299830954703224643 49821912449746432054836965)
    ·
      refine ⟨9341608584327456010281931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49821912449746432054836965 9341608584327456010281931)
      ·
        refine ⟨14012412876491184015422897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9341608584327456010281931 14012412876491184015422897)
        ·
          refine ⟨10509309657368388011567173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14012412876491184015422897 10509309657368388011567173)
          ·
            refine ⟨1970495560756572752168845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10509309657368388011567173 1970495560756572752168845)
            ·
              refine ⟨738935835283714782063317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970495560756572752168845 738935835283714782063317)
              ·
                refine ⟨17318808639462065204609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 738935835283714782063317 17318808639462065204609)
                ·
                  rfl

theorem cell23_910663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 7].length) (baseStart_910663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910663 prefixEnd_910663 := by exact prefixLift 910663
  have htrace : WordTrace (prefixWord ++ tailWord_910663) baseStart_910663 baseEnd_910663 := by
    simpa [prefixWord, tailWord_910663, baseEnd_910663] using wordTrace_append hprefix tailTrace_910663
  have hstable : (prefixWord ++ tailWord_910663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910663).length < 2 ^ (prefixWord ++ tailWord_910663).sum := by decide
  have hdescent : baseEnd_910663 < baseStart_910663 := by decide
  rcases family_descends (prefixWord ++ tailWord_910663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910673 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_910673 : Nat := 118140960795 + 910673 * 2 ^ 59
def prefixEnd_910673 : Nat := 4983230072969 + 3 ^ 40 * 910673 * 2
def baseEnd_910673 : Nat := 467612968072020721399397

theorem tailTrace_910673 : CollatzResearch.WordTrace tailWord_910673 prefixEnd_910673 467612968072020721399397 := by
  unfold tailWord_910673
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214973029794726411088673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22143315353196484274059115 33214973029794726411088673)
  ·
    refine ⟨24911229772346044808316505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33214973029794726411088673 24911229772346044808316505)
    ·
      refine ⟨18683422329259533606237379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24911229772346044808316505 18683422329259533606237379)
      ·
        refine ⟨28025133493889300409356069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683422329259533606237379 28025133493889300409356069)
        ·
          refine ⟨5254712530104243826754263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28025133493889300409356069 5254712530104243826754263)
          ·
            refine ⟨7882068795156365740131395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254712530104243826754263 7882068795156365740131395)
            ·
              refine ⟨11823103192734548610197093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882068795156365740131395 11823103192734548610197093)
              ·
                refine ⟨2216831848637727864411955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11823103192734548610197093 2216831848637727864411955)
                ·
                  refine ⟨3325247772956591796617933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216831848637727864411955 3325247772956591796617933)
                  ·
                    refine ⟨1246967914858721923731725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325247772956591796617933 1246967914858721923731725)
                    ·
                      refine ⟨467612968072020721399397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246967914858721923731725 467612968072020721399397)
                      ·
                        rfl

theorem cell23_910673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_910673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910673 prefixEnd_910673 := by exact prefixLift 910673
  have htrace : WordTrace (prefixWord ++ tailWord_910673) baseStart_910673 baseEnd_910673 := by
    simpa [prefixWord, tailWord_910673, baseEnd_910673] using wordTrace_append hprefix tailTrace_910673
  have hstable : (prefixWord ++ tailWord_910673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910673).length < 2 ^ (prefixWord ++ tailWord_910673).sum := by decide
  have hdescent : baseEnd_910673 < baseStart_910673 := by decide
  rcases family_descends (prefixWord ++ tailWord_910673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910677 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_910677 : Nat := 118140960795 + 910677 * 2 ^ 59
def prefixEnd_910677 : Nat := 4983230072969 + 3 ^ 40 * 910677 * 2
def baseEnd_910677 : Nat := 467615021994638705749379

theorem tailTrace_910677 : CollatzResearch.WordTrace tailWord_910677 prefixEnd_910677 467615021994638705749379 := by
  unfold tailWord_910677
  simp only [CollatzResearch.WordTrace]
  refine ⟨33215118921780235094234285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22143412614520156729489523 33215118921780235094234285)
  ·
    refine ⟨12455669595667588160337857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33215118921780235094234285 12455669595667588160337857)
    ·
      refine ⟨9341752196750691120253393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12455669595667588160337857 9341752196750691120253393)
      ·
        refine ⟨7006314147563018340190045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9341752196750691120253393 7006314147563018340190045)
        ·
          refine ⟨2627367805336131877571267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7006314147563018340190045 2627367805336131877571267)
          ·
            refine ⟨3941051708004197816356901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627367805336131877571267 3941051708004197816356901)
            ·
              refine ⟨738947195250787090566919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3941051708004197816356901 738947195250787090566919)
              ·
                refine ⟨1108420792876180635850379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738947195250787090566919 1108420792876180635850379)
                ·
                  refine ⟨1662631189314270953775569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108420792876180635850379 1662631189314270953775569)
                  ·
                    refine ⟨1246973391985703215331677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662631189314270953775569 1246973391985703215331677)
                    ·
                      refine ⟨467615021994638705749379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1246973391985703215331677 467615021994638705749379)
                      ·
                        rfl

theorem cell23_910677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_910677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910677 prefixEnd_910677 := by exact prefixLift 910677
  have htrace : WordTrace (prefixWord ++ tailWord_910677) baseStart_910677 baseEnd_910677 := by
    simpa [prefixWord, tailWord_910677, baseEnd_910677] using wordTrace_append hprefix tailTrace_910677
  have hstable : (prefixWord ++ tailWord_910677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910677).length < 2 ^ (prefixWord ++ tailWord_910677).sum := by decide
  have hdescent : baseEnd_910677 < baseStart_910677 := by decide
  rcases family_descends (prefixWord ++ tailWord_910677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910717 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_910717 : Nat := 118140960795 + 910717 * 2 ^ 59
def prefixEnd_910717 : Nat := 4983230072969 + 3 ^ 40 * 910717 * 2
def baseEnd_910717 : Nat := 467635561220818549249195

theorem tailTrace_910717 : CollatzResearch.WordTrace tailWord_910717 prefixEnd_910717 467635561220818549249195 := by
  unfold tailWord_910717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33216577841635321925690405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22144385227756881283793603 33216577841635321925690405)
  ·
    refine ⟨6228108345306622861066951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33216577841635321925690405 6228108345306622861066951)
    ·
      refine ⟨9342162517959934291600427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228108345306622861066951 9342162517959934291600427)
      ·
        refine ⟨14013243776939901437400641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342162517959934291600427 14013243776939901437400641)
        ·
          refine ⟨10509932832704926078050481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14013243776939901437400641 10509932832704926078050481)
          ·
            refine ⟨7882449624528694558537861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10509932832704926078050481 7882449624528694558537861)
            ·
              refine ⟨1477959304599130229725849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7882449624528694558537861 1477959304599130229725849)
              ·
                refine ⟨1108469478449347672294387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477959304599130229725849 1108469478449347672294387)
                ·
                  refine ⟨1662704217674021508441581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108469478449347672294387 1662704217674021508441581)
                  ·
                    refine ⟨623514081627758065665593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662704217674021508441581 623514081627758065665593)
                    ·
                      refine ⟨467635561220818549249195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623514081627758065665593 467635561220818549249195)
                      ·
                        rfl

theorem cell23_910717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_910717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910717 prefixEnd_910717 := by exact prefixLift 910717
  have htrace : WordTrace (prefixWord ++ tailWord_910717) baseStart_910717 baseEnd_910717 := by
    simpa [prefixWord, tailWord_910717, baseEnd_910717] using wordTrace_append hprefix tailTrace_910717
  have hstable : (prefixWord ++ tailWord_910717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910717).length < 2 ^ (prefixWord ++ tailWord_910717).sum := by decide
  have hdescent : baseEnd_910717 < baseStart_910717 := by decide
  rcases family_descends (prefixWord ++ tailWord_910717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910764 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_910764 : Nat := 118140960795 + 910764 * 2 ^ 59
def prefixEnd_910764 : Nat := 4983230072969 + 3 ^ 40 * 910764 * 2
def baseEnd_910764 : Nat := 467659694811579865361479

theorem tailTrace_910764 : CollatzResearch.WordTrace tailWord_910764 prefixEnd_910764 467659694811579865361479 := by
  unfold tailWord_910764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609146036232524476325673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22145528048310032635100897 16609146036232524476325673)
  ·
    refine ⟨12456859527174393357244255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16609146036232524476325673 12456859527174393357244255)
    ·
      refine ⟨18685289290761590035866383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12456859527174393357244255 18685289290761590035866383)
      ·
        refine ⟨28027933936142385053799575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18685289290761590035866383 28027933936142385053799575)
        ·
          refine ⟨42041900904213577580699363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28027933936142385053799575 42041900904213577580699363)
          ·
            refine ⟨63062851356320366371049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42041900904213577580699363 63062851356320366371049045)
            ·
              refine ⟨739017789331879293410731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 63062851356320366371049045 739017789331879293410731)
              ·
                refine ⟨1108526683997818940116097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739017789331879293410731 1108526683997818940116097)
                ·
                  refine ⟨831395012998364205087073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108526683997818940116097 831395012998364205087073)
                  ·
                    refine ⟨623546259748773153815305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831395012998364205087073 623546259748773153815305)
                    ·
                      refine ⟨467659694811579865361479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623546259748773153815305 467659694811579865361479)
                      ·
                        rfl

theorem cell23_910764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_910764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910764 prefixEnd_910764 := by exact prefixLift 910764
  have htrace : WordTrace (prefixWord ++ tailWord_910764) baseStart_910764 baseEnd_910764 := by
    simpa [prefixWord, tailWord_910764, baseEnd_910764] using wordTrace_append hprefix tailTrace_910764
  have hstable : (prefixWord ++ tailWord_910764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910764).length < 2 ^ (prefixWord ++ tailWord_910764).sum := by decide
  have hdescent : baseEnd_910764 < baseStart_910764 := by decide
  rcases family_descends (prefixWord ++ tailWord_910764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910837 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_910837 : Nat := 118140960795 + 910837 * 2 ^ 59
def prefixEnd_910837 : Nat := 4983230072969 + 3 ^ 40 * 910837 * 2
def baseEnd_910837 : Nat := 467697178899358079748643

theorem tailTrace_910837 : CollatzResearch.WordTrace tailWord_910837 prefixEnd_910837 467697178899358079748643 := by
  unfold tailWord_910837
  simp only [CollatzResearch.WordTrace]
  refine ⟨33220954601200582420058765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22147303067467054946705843 33220954601200582420058765)
  ·
    refine ⟨12457857975450218407522037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33220954601200582420058765 12457857975450218407522037)
    ·
      refine ⟨1167924185198457975705191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12457857975450218407522037 1167924185198457975705191)
      ·
        refine ⟨1751886277797686963557787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167924185198457975705191 1751886277797686963557787)
        ·
          refine ⟨2627829416696530445336681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751886277797686963557787 2627829416696530445336681)
          ·
            refine ⟨1970872062522397834002511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627829416696530445336681 1970872062522397834002511)
            ·
              refine ⟨2956308093783596751003767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970872062522397834002511 2956308093783596751003767)
              ·
                refine ⟨4434462140675395126505651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956308093783596751003767 4434462140675395126505651)
                ·
                  refine ⟨6651693211013092689758477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434462140675395126505651 6651693211013092689758477)
                  ·
                    refine ⟨2494384954129909758659429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6651693211013092689758477 2494384954129909758659429)
                    ·
                      refine ⟨467697178899358079748643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2494384954129909758659429 467697178899358079748643)
                      ·
                        rfl

theorem cell23_910837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_910837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910837 prefixEnd_910837 := by exact prefixLift 910837
  have htrace : WordTrace (prefixWord ++ tailWord_910837) baseStart_910837 baseEnd_910837 := by
    simpa [prefixWord, tailWord_910837, baseEnd_910837] using wordTrace_append hprefix tailTrace_910837
  have hstable : (prefixWord ++ tailWord_910837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910837).length < 2 ^ (prefixWord ++ tailWord_910837).sum := by decide
  have hdescent : baseEnd_910837 < baseStart_910837 := by decide
  rcases family_descends (prefixWord ++ tailWord_910837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910840 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_910840 : Nat := 118140960795 + 910840 * 2 ^ 59
def prefixEnd_910840 : Nat := 4983230072969 + 3 ^ 40 * 910840 * 2
def baseEnd_910840 : Nat := 467698719341321568011129

theorem tailTrace_910840 : CollatzResearch.WordTrace tailWord_910840 prefixEnd_910840 467698719341321568011129 := by
  unfold tailWord_910840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610532010094856966208987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22147376013459809288278649 16610532010094856966208987)
  ·
    refine ⟨24915798015142285449313481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16610532010094856966208987 24915798015142285449313481)
    ·
      refine ⟨18686848511356714086985111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24915798015142285449313481 18686848511356714086985111)
      ·
        refine ⟨28030272767035071130477667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686848511356714086985111 28030272767035071130477667)
        ·
          refine ⟨42045409150552606695716501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28030272767035071130477667 42045409150552606695716501)
          ·
            refine ⟨1970878553932153438861711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42045409150552606695716501 1970878553932153438861711)
            ·
              refine ⟨2956317830898230158292567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970878553932153438861711 2956317830898230158292567)
              ·
                refine ⟨4434476746347345237438851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956317830898230158292567 4434476746347345237438851)
                ·
                  refine ⟨6651715119521017856158277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434476746347345237438851 6651715119521017856158277)
                  ·
                    refine ⟨1247196584910190848029677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6651715119521017856158277 1247196584910190848029677)
                    ·
                      refine ⟨467698719341321568011129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1247196584910190848029677 467698719341321568011129)
                      ·
                        rfl

theorem cell23_910840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_910840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910840 prefixEnd_910840 := by exact prefixLift 910840
  have htrace : WordTrace (prefixWord ++ tailWord_910840) baseStart_910840 baseEnd_910840 := by
    simpa [prefixWord, tailWord_910840, baseEnd_910840] using wordTrace_append hprefix tailTrace_910840
  have hstable : (prefixWord ++ tailWord_910840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910840).length < 2 ^ (prefixWord ++ tailWord_910840).sum := by decide
  have hdescent : baseEnd_910840 < baseStart_910840 := by decide
  rcases family_descends (prefixWord ++ tailWord_910840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910860 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 8]
def baseStart_910860 : Nat := 118140960795 + 910860 * 2 ^ 59
def prefixEnd_910860 : Nat := 4983230072969 + 3 ^ 40 * 910860 * 2
def baseEnd_910860 : Nat := 51967665439379054417893

theorem tailTrace_910860 : CollatzResearch.WordTrace tailWord_910860 prefixEnd_910860 51967665439379054417893 := by
  unfold tailWord_910860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610896740058628674073017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22147862320078171565430689 16610896740058628674073017)
  ·
    refine ⟨12458172555043971505554763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16610896740058628674073017 12458172555043971505554763)
    ·
      refine ⟨18687258832565957258332145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458172555043971505554763 18687258832565957258332145)
      ·
        refine ⟨14015444124424467943749109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18687258832565957258332145 14015444124424467943749109)
        ·
          refine ⟨1313947886664793869726479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14015444124424467943749109 1313947886664793869726479)
          ·
            refine ⟨1970921829997190804589719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313947886664793869726479 1970921829997190804589719)
            ·
              refine ⟨2956382744995786206884579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970921829997190804589719 2956382744995786206884579)
              ·
                refine ⟨4434574117493679310326869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956382744995786206884579 4434574117493679310326869)
                ·
                  refine ⟨51967665439379054417893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4434574117493679310326869 51967665439379054417893)
                  ·
                    rfl

theorem cell23_910860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_910860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910860 prefixEnd_910860 := by exact prefixLift 910860
  have htrace : WordTrace (prefixWord ++ tailWord_910860) baseStart_910860 baseEnd_910860 := by
    simpa [prefixWord, tailWord_910860, baseEnd_910860] using wordTrace_append hprefix tailTrace_910860
  have hstable : (prefixWord ++ tailWord_910860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910860).length < 2 ^ (prefixWord ++ tailWord_910860).sum := by decide
  have hdescent : baseEnd_910860 < baseStart_910860 := by decide
  rcases family_descends (prefixWord ++ tailWord_910860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910877 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 6]
def baseStart_910877 : Nat := 118140960795 + 910877 * 2 ^ 59
def prefixEnd_910877 : Nat := 4983230072969 + 3 ^ 40 * 910877 * 2
def baseEnd_910877 : Nat := 51968635347281991472051

theorem tailTrace_910877 : CollatzResearch.WordTrace tailWord_910877 prefixEnd_910877 51968635347281991472051 := by
  unfold tailWord_910877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33222413521055669251514885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22148275680703779501009923 33222413521055669251514885)
  ·
    refine ⟨6229202535197937984659041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33222413521055669251514885 6229202535197937984659041)
    ·
      refine ⟨4671901901398453488494281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229202535197937984659041 4671901901398453488494281)
      ·
        refine ⟨3503926426048840116370711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4671901901398453488494281 3503926426048840116370711)
        ·
          refine ⟨5255889639073260174556067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503926426048840116370711 5255889639073260174556067)
          ·
            refine ⟨7883834458609890261834101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255889639073260174556067 7883834458609890261834101)
            ·
              refine ⟨739109480494677212046947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7883834458609890261834101 739109480494677212046947)
              ·
                refine ⟨1108664220742015818070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739109480494677212046947 1108664220742015818070421)
                ·
                  refine ⟨51968635347281991472051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1108664220742015818070421 51968635347281991472051)
                  ·
                    rfl

theorem cell23_910877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_910877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910877 prefixEnd_910877 := by exact prefixLift 910877
  have htrace : WordTrace (prefixWord ++ tailWord_910877) baseStart_910877 baseEnd_910877 := by
    simpa [prefixWord, tailWord_910877, baseEnd_910877] using wordTrace_append hprefix tailTrace_910877
  have hstable : (prefixWord ++ tailWord_910877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910877).length < 2 ^ (prefixWord ++ tailWord_910877).sum := by decide
  have hdescent : baseEnd_910877 < baseStart_910877 := by decide
  rcases family_descends (prefixWord ++ tailWord_910877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910897 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_910897 : Nat := 118140960795 + 910897 * 2 ^ 59
def prefixEnd_910897 : Nat := 4983230072969 + 3 ^ 40 * 910897 * 2
def baseEnd_910897 : Nat := 467727987738627844998367

theorem tailTrace_910897 : CollatzResearch.WordTrace tailWord_910897 prefixEnd_910897 467727987738627844998367 := by
  unfold tailWord_910897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33223142980983212667242945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22148761987322141778161963 33223142980983212667242945)
  ·
    refine ⟨24917357235737409500432209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33223142980983212667242945 24917357235737409500432209)
    ·
      refine ⟨18688017926803057125324157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24917357235737409500432209 18688017926803057125324157)
      ·
        refine ⟨7008006722551146421996559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688017926803057125324157 7008006722551146421996559)
        ·
          refine ⟨10512010083826719632994839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008006722551146421996559 10512010083826719632994839)
          ·
            refine ⟨15768015125740079449492259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512010083826719632994839 15768015125740079449492259)
            ·
              refine ⟨23652022688610119174238389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15768015125740079449492259 23652022688610119174238389)
              ·
                refine ⟨2217377127057198672584849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23652022688610119174238389 2217377127057198672584849)
                ·
                  refine ⟨1663032845292899004438637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217377127057198672584849 1663032845292899004438637)
                  ·
                    refine ⟨623637316984837126664489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663032845292899004438637 623637316984837126664489)
                    ·
                      refine ⟨467727987738627844998367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623637316984837126664489 467727987738627844998367)
                      ·
                        rfl

theorem cell23_910897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_910897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910897 prefixEnd_910897 := by exact prefixLift 910897
  have htrace : WordTrace (prefixWord ++ tailWord_910897) baseStart_910897 baseEnd_910897 := by
    simpa [prefixWord, tailWord_910897, baseEnd_910897] using wordTrace_append hprefix tailTrace_910897
  have hstable : (prefixWord ++ tailWord_910897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910897).length < 2 ^ (prefixWord ++ tailWord_910897).sum := by decide
  have hdescent : baseEnd_910897 < baseStart_910897 := by decide
  rcases family_descends (prefixWord ++ tailWord_910897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910947 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3]
def baseStart_910947 : Nat := 118140960795 + 910947 * 2 ^ 59
def prefixEnd_910947 : Nat := 4983230072969 + 3 ^ 40 * 910947 * 2
def baseEnd_910947 : Nat := 467753661771352649373137

theorem tailTrace_910947 : CollatzResearch.WordTrace tailWord_910947 prefixEnd_910947 467753661771352649373137 := by
  unfold tailWord_910947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224966630802071206563095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22149977753868047471042063 33224966630802071206563095)
  ·
    refine ⟨49837449946203106809844643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33224966630802071206563095 49837449946203106809844643)
    ·
      refine ⟨74756174919304660214766965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49837449946203106809844643 74756174919304660214766965)
      ·
        refine ⟨7008391398684811895134403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74756174919304660214766965 7008391398684811895134403)
        ·
          refine ⟨10512587098027217842701605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008391398684811895134403 10512587098027217842701605)
          ·
            refine ⟨1971110080880103345506551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10512587098027217842701605 1971110080880103345506551)
            ·
              refine ⟨2956665121320155018259827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971110080880103345506551 2956665121320155018259827)
              ·
                refine ⟨4434997681980232527389741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956665121320155018259827 4434997681980232527389741)
                ·
                  refine ⟨1663124130742587197771153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4434997681980232527389741 1663124130742587197771153)
                  ·
                    refine ⟨1247343098056940398328365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1663124130742587197771153 1247343098056940398328365)
                    ·
                      refine ⟨467753661771352649373137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1247343098056940398328365 467753661771352649373137)
                      ·
                        rfl

theorem cell23_910947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_910947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910947 prefixEnd_910947 := by exact prefixLift 910947
  have htrace : WordTrace (prefixWord ++ tailWord_910947) baseStart_910947 baseEnd_910947 := by
    simpa [prefixWord, tailWord_910947, baseEnd_910947] using wordTrace_append hprefix tailTrace_910947
  have hstable : (prefixWord ++ tailWord_910947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910947).length < 2 ^ (prefixWord ++ tailWord_910947).sum := by decide
  have hdescent : baseEnd_910947 < baseStart_910947 := by decide
  rcases family_descends (prefixWord ++ tailWord_910947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910984 : List Nat := [2, 1, 3, 5, 1, 2, 1, 8]
def baseStart_910984 : Nat := 118140960795 + 910984 * 2 ^ 59
def prefixEnd_910984 : Nat := 4983230072969 + 3 ^ 40 * 910984 * 2
def baseEnd_910984 : Nat := 17324913353909963133721

theorem tailTrace_910984 : CollatzResearch.WordTrace tailWord_910984 prefixEnd_910984 17324913353909963133721 := by
  unfold tailWord_910984
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613158065834013262830003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22150877421112017683773337 16613158065834013262830003)
  ·
    refine ⟨24919737098751019894245005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613158065834013262830003 24919737098751019894245005)
    ·
      refine ⟨9344901412031632460341877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24919737098751019894245005 9344901412031632460341877)
      ·
        refine ⟨876084507377965543157051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9344901412031632460341877 876084507377965543157051)
        ·
          refine ⟨1314126761066948314735577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876084507377965543157051 1314126761066948314735577)
          ·
            refine ⟨985595070800211236051683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314126761066948314735577 985595070800211236051683)
            ·
              refine ⟨1478392606200316854077525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985595070800211236051683 1478392606200316854077525)
              ·
                refine ⟨17324913353909963133721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1478392606200316854077525 17324913353909963133721)
                ·
                  rfl

theorem cell23_910984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 8].length) (baseStart_910984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910984 prefixEnd_910984 := by exact prefixLift 910984
  have htrace : WordTrace (prefixWord ++ tailWord_910984) baseStart_910984 baseEnd_910984 := by
    simpa [prefixWord, tailWord_910984, baseEnd_910984] using wordTrace_append hprefix tailTrace_910984
  have hstable : (prefixWord ++ tailWord_910984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910984).length < 2 ^ (prefixWord ++ tailWord_910984).sum := by decide
  have hdescent : baseEnd_910984 < baseStart_910984 := by decide
  rcases family_descends (prefixWord ++ tailWord_910984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910987 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 5, 3, 2]
def baseStart_910987 : Nat := 118140960795 + 910987 * 2 ^ 59
def prefixEnd_910987 : Nat := 4983230072969 + 3 ^ 40 * 910987 * 2
def baseEnd_910987 : Nat := 467774200997532492872953

theorem tailTrace_910987 : CollatzResearch.WordTrace tailWord_910987 prefixEnd_910987 467774200997532492872953 := by
  unfold tailWord_910987
  simp only [CollatzResearch.WordTrace]
  refine ⟨33226425550657158038019215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22150950367104772025346143 33226425550657158038019215)
  ·
    refine ⟨49839638325985737057028823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33226425550657158038019215 49839638325985737057028823)
    ·
      refine ⟨74759457488978605585543235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49839638325985737057028823 74759457488978605585543235)
      ·
        refine ⟨112139186233467908378314853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74759457488978605585543235 112139186233467908378314853)
        ·
          refine ⟨21026097418775232820934035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112139186233467908378314853 21026097418775232820934035)
          ·
            refine ⟨31539146128162849231401053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21026097418775232820934035 31539146128162849231401053)
            ·
              refine ⟨11827179798061068461775395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31539146128162849231401053 11827179798061068461775395)
              ·
                refine ⟨17740769697091602692663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11827179798061068461775395 17740769697091602692663093)
                ·
                  refine ⟨1663197159102337752437165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17740769697091602692663093 1663197159102337752437165)
                  ·
                    refine ⟨623698934663376657163937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663197159102337752437165 623698934663376657163937)
                    ·
                      refine ⟨467774200997532492872953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623698934663376657163937 467774200997532492872953)
                      ·
                        rfl

theorem cell23_910987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3, 2].length) (baseStart_910987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_910987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_910987 prefixEnd_910987 := by exact prefixLift 910987
  have htrace : WordTrace (prefixWord ++ tailWord_910987) baseStart_910987 baseEnd_910987 := by
    simpa [prefixWord, tailWord_910987, baseEnd_910987] using wordTrace_append hprefix tailTrace_910987
  have hstable : (prefixWord ++ tailWord_910987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910987).length < 2 ^ (prefixWord ++ tailWord_910987).sum := by decide
  have hdescent : baseEnd_910987 < baseStart_910987 := by decide
  rcases family_descends (prefixWord ++ tailWord_910987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911021 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_911021 : Nat := 118140960795 + 911021 * 2 ^ 59
def prefixEnd_911021 : Nat := 4983230072969 + 3 ^ 40 * 911021 * 2
def baseEnd_911021 : Nat := 467791659339785359847797

theorem tailTrace_911021 : CollatzResearch.WordTrace tailWord_911021 prefixEnd_911021 467791659339785359847797 := by
  unfold tailWord_911021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33227665632533981844756917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22151777088355987896504611 33227665632533981844756917)
  ·
    refine ⟨3115093653050060797945961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33227665632533981844756917 3115093653050060797945961)
    ·
      refine ⟨2336320239787545598459471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115093653050060797945961 2336320239787545598459471)
      ·
        refine ⟨3504480359681318397689207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336320239787545598459471 3504480359681318397689207)
        ·
          refine ⟨5256720539521977596533811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504480359681318397689207 5256720539521977596533811)
          ·
            refine ⟨7885080809282966394800717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256720539521977596533811 7885080809282966394800717)
            ·
              refine ⟨2956905303481112398050269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885080809282966394800717 2956905303481112398050269)
              ·
                refine ⟨1108839488805417149268851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956905303481112398050269 1108839488805417149268851)
                ·
                  refine ⟨1663259233208125723903277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108839488805417149268851 1663259233208125723903277)
                  ·
                    refine ⟨623722212453047146463729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663259233208125723903277 623722212453047146463729)
                    ·
                      refine ⟨467791659339785359847797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623722212453047146463729 467791659339785359847797)
                      ·
                        rfl

theorem cell23_911021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_911021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911021 prefixEnd_911021 := by exact prefixLift 911021
  have htrace : WordTrace (prefixWord ++ tailWord_911021) baseStart_911021 baseEnd_911021 := by
    simpa [prefixWord, tailWord_911021, baseEnd_911021] using wordTrace_append hprefix tailTrace_911021
  have hstable : (prefixWord ++ tailWord_911021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911021).length < 2 ^ (prefixWord ++ tailWord_911021).sum := by decide
  have hdescent : baseEnd_911021 < baseStart_911021 := by decide
  rcases family_descends (prefixWord ++ tailWord_911021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911087 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 2, 5]
def baseStart_911087 : Nat := 118140960795 + 911087 * 2 ^ 59
def prefixEnd_911087 : Nat := 4983230072969 + 3 ^ 40 * 911087 * 2
def baseEnd_911087 : Nat := 155941849687660700540831

theorem tailTrace_911087 : CollatzResearch.WordTrace tailWord_911087 prefixEnd_911087 155941849687660700540831 := by
  unfold tailWord_911087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33230072850294875116659515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22153381900196583411106343 33230072850294875116659515)
  ·
    refine ⟨49845109275442312674989273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33230072850294875116659515 49845109275442312674989273)
    ·
      refine ⟨37383831956581734506241955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49845109275442312674989273 37383831956581734506241955)
      ·
        refine ⟨56075747934872601759362933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37383831956581734506241955 56075747934872601759362933)
        ·
          refine ⟨5257101368894306414940275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56075747934872601759362933 5257101368894306414940275)
          ·
            refine ⟨7885652053341459622410413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257101368894306414940275 7885652053341459622410413)
            ·
              refine ⟨2957119520003047358403905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885652053341459622410413 2957119520003047358403905)
              ·
                refine ⟨2217839640002285518802929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957119520003047358403905 2217839640002285518802929)
                ·
                  refine ⟨1663379730001714139102197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217839640002285518802929 1663379730001714139102197)
                  ·
                    refine ⟨155941849687660700540831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1663379730001714139102197 155941849687660700540831)
                    ·
                      rfl

theorem cell23_911087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_911087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911087 prefixEnd_911087 := by exact prefixLift 911087
  have htrace : WordTrace (prefixWord ++ tailWord_911087) baseStart_911087 baseEnd_911087 := by
    simpa [prefixWord, tailWord_911087, baseEnd_911087] using wordTrace_append hprefix tailTrace_911087
  have hstable : (prefixWord ++ tailWord_911087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911087).length < 2 ^ (prefixWord ++ tailWord_911087).sum := by decide
  have hdescent : baseEnd_911087 < baseStart_911087 := by decide
  rcases family_descends (prefixWord ++ tailWord_911087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911102 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_911102 : Nat := 118140960795 + 911102 * 2 ^ 59
def prefixEnd_911102 : Nat := 4983230072969 + 3 ^ 40 * 911102 * 2
def baseEnd_911102 : Nat := 467833251272799542934925

theorem tailTrace_911102 : CollatzResearch.WordTrace tailWord_911102 prefixEnd_911102 467833251272799542934925 := by
  unfold tailWord_911102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153827493155066584806945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22153746630160355118970373 4153827493155066584806945)
  ·
    refine ⟨3115370619866299938605209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153827493155066584806945 3115370619866299938605209)
    ·
      refine ⟨2336527964899724953953907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115370619866299938605209 2336527964899724953953907)
      ·
        refine ⟨3504791947349587430930861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336527964899724953953907 3504791947349587430930861)
        ·
          refine ⟨1314296980256095286599073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3504791947349587430930861 1314296980256095286599073)
          ·
            refine ⟨985722735192071464949305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314296980256095286599073 985722735192071464949305)
            ·
              refine ⟨739292051394053598711979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985722735192071464949305 739292051394053598711979)
              ·
                refine ⟨1108938077091080398067969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739292051394053598711979 1108938077091080398067969)
                ·
                  refine ⟨831703557818310298550977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108938077091080398067969 831703557818310298550977)
                  ·
                    refine ⟨623777668363732723913233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 831703557818310298550977 623777668363732723913233)
                    ·
                      refine ⟨467833251272799542934925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623777668363732723913233 467833251272799542934925)
                      ·
                        rfl

theorem cell23_911102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_911102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911102 prefixEnd_911102 := by exact prefixLift 911102
  have htrace : WordTrace (prefixWord ++ tailWord_911102) baseStart_911102 baseEnd_911102 := by
    simpa [prefixWord, tailWord_911102, baseEnd_911102] using wordTrace_append hprefix tailTrace_911102
  have hstable : (prefixWord ++ tailWord_911102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911102).length < 2 ^ (prefixWord ++ tailWord_911102).sum := by decide
  have hdescent : baseEnd_911102 < baseStart_911102 := by decide
  rcases family_descends (prefixWord ++ tailWord_911102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911158 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_911158 : Nat := 118140960795 + 911158 * 2 ^ 59
def prefixEnd_911158 : Nat := 4983230072969 + 3 ^ 40 * 911158 * 2
def baseEnd_911158 : Nat := 467862006189451323834667

theorem tailTrace_911158 : CollatzResearch.WordTrace tailWord_911158 prefixEnd_911158 467862006189451323834667 := by
  unfold tailWord_911158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077041402064853390155883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22155108288691769494996085 2077041402064853390155883)
  ·
    refine ⟨3115562103097280085233825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077041402064853390155883 3115562103097280085233825)
    ·
      refine ⟨2336671577322960063925369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115562103097280085233825 2336671577322960063925369)
      ·
        refine ⟨1752503682992220047944027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2336671577322960063925369 1752503682992220047944027)
        ·
          refine ⟨2628755524488330071916041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752503682992220047944027 2628755524488330071916041)
          ·
            refine ⟨1971566643366247553937031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628755524488330071916041 1971566643366247553937031)
            ·
              refine ⟨2957349965049371330905547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971566643366247553937031 2957349965049371330905547)
              ·
                refine ⟨4436024947574056996358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957349965049371330905547 4436024947574056996358321)
                ·
                  refine ⟨3327018710680542747268741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436024947574056996358321 3327018710680542747268741)
                  ·
                    refine ⟨623816008252601765112889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327018710680542747268741 623816008252601765112889)
                    ·
                      refine ⟨467862006189451323834667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623816008252601765112889 467862006189451323834667)
                      ·
                        rfl

theorem cell23_911158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_911158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911158 prefixEnd_911158 := by exact prefixLift 911158
  have htrace : WordTrace (prefixWord ++ tailWord_911158) baseStart_911158 baseEnd_911158 := by
    simpa [prefixWord, tailWord_911158, baseEnd_911158] using wordTrace_append hprefix tailTrace_911158
  have hstable : (prefixWord ++ tailWord_911158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911158).length < 2 ^ (prefixWord ++ tailWord_911158).sum := by decide
  have hdescent : baseEnd_911158 < baseStart_911158 := by decide
  rcases family_descends (prefixWord ++ tailWord_911158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911177 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_911177 : Nat := 118140960795 + 911177 * 2 ^ 59
def prefixEnd_911177 : Nat := 4983230072969 + 3 ^ 40 * 911177 * 2
def baseEnd_911177 : Nat := 155957254107295583165693

theorem tailTrace_911177 : CollatzResearch.WordTrace tailWord_911177 prefixEnd_911177 155957254107295583165693 := by
  unfold tailWord_911177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33233355419968820487435785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22155570279979213658290523 33233355419968820487435785)
  ·
    refine ⟨24925016564976615365576839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33233355419968820487435785 24925016564976615365576839)
    ·
      refine ⟨37387524847464923048365259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24925016564976615365576839 37387524847464923048365259)
      ·
        refine ⟨56081287271197384572547889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37387524847464923048365259 56081287271197384572547889)
        ·
          refine ⟨42060965453398038429410917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56081287271197384572547889 42060965453398038429410917)
          ·
            refine ⟨7886431022512132205514547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42060965453398038429410917 7886431022512132205514547)
            ·
              refine ⟨11829646533768198308271821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886431022512132205514547 11829646533768198308271821)
              ·
                refine ⟨4436117450163074365601933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11829646533768198308271821 4436117450163074365601933)
                ·
                  refine ⟨1663544043811152887100725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4436117450163074365601933 1663544043811152887100725)
                  ·
                    refine ⟨155957254107295583165693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1663544043811152887100725 155957254107295583165693)
                    ·
                      rfl

theorem cell23_911177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_911177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911177 prefixEnd_911177 := by exact prefixLift 911177
  have htrace : WordTrace (prefixWord ++ tailWord_911177) baseStart_911177 baseEnd_911177 := by
    simpa [prefixWord, tailWord_911177, baseEnd_911177] using wordTrace_append hprefix tailTrace_911177
  have hstable : (prefixWord ++ tailWord_911177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911177).length < 2 ^ (prefixWord ++ tailWord_911177).sum := by decide
  have hdescent : baseEnd_911177 < baseStart_911177 := by decide
  rcases family_descends (prefixWord ++ tailWord_911177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911194 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_911194 : Nat := 118140960795 + 911194 * 2 ^ 59
def prefixEnd_911194 : Nat := 4983230072969 + 3 ^ 40 * 911194 * 2
def baseEnd_911194 : Nat := 155960163831004394328167

theorem tailTrace_911194 : CollatzResearch.WordTrace tailWord_911194 prefixEnd_911194 155960163831004394328167 := by
  unfold tailWord_911194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308493865226808097701159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22155983640604821593869757 8308493865226808097701159)
  ·
    refine ⟨12462740797840212146551739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8308493865226808097701159 12462740797840212146551739)
    ·
      refine ⟨18694111196760318219827609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462740797840212146551739 18694111196760318219827609)
      ·
        refine ⟨14020583397570238664870707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18694111196760318219827609 14020583397570238664870707)
        ·
          refine ⟨21030875096355357997306061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14020583397570238664870707 21030875096355357997306061)
          ·
            refine ⟨7886578161133259248989773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21030875096355357997306061 7886578161133259248989773)
            ·
              refine ⟨2957466810424972218371165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7886578161133259248989773 2957466810424972218371165)
              ·
                refine ⟨1109050053909364581889187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2957466810424972218371165 1109050053909364581889187)
                ·
                  refine ⟨1663575080864046872833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109050053909364581889187 1663575080864046872833781)
                  ·
                    refine ⟨155960163831004394328167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1663575080864046872833781 155960163831004394328167)
                    ·
                      rfl

theorem cell23_911194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_911194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911194 prefixEnd_911194 := by exact prefixLift 911194
  have htrace : WordTrace (prefixWord ++ tailWord_911194) baseStart_911194 baseEnd_911194 := by
    simpa [prefixWord, tailWord_911194, baseEnd_911194] using wordTrace_append hprefix tailTrace_911194
  have hstable : (prefixWord ++ tailWord_911194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911194).length < 2 ^ (prefixWord ++ tailWord_911194).sum := by decide
  have hdescent : baseEnd_911194 < baseStart_911194 := by decide
  rcases family_descends (prefixWord ++ tailWord_911194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911208 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_911208 : Nat := 118140960795 + 911208 * 2 ^ 59
def prefixEnd_911208 : Nat := 4983230072969 + 3 ^ 40 * 911208 * 2
def baseEnd_911208 : Nat := 467887680222176128209437

theorem tailTrace_911208 : CollatzResearch.WordTrace tailWord_911208 prefixEnd_911208 467887680222176128209437 := by
  unfold tailWord_911208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16617243041428256390907139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22156324055237675187876185 16617243041428256390907139)
  ·
    refine ⟨24925864562142384586360709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16617243041428256390907139 24925864562142384586360709)
    ·
      refine ⟨4673599605401697109942633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24925864562142384586360709 4673599605401697109942633)
      ·
        refine ⟨3505199704051272832456975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4673599605401697109942633 3505199704051272832456975)
        ·
          refine ⟨5257799556076909248685463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505199704051272832456975 5257799556076909248685463)
          ·
            refine ⟨7886699334115363873028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257799556076909248685463 7886699334115363873028195)
            ·
              refine ⟨11830049001173045809542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886699334115363873028195 11830049001173045809542293)
              ·
                refine ⟨554533546929986522322295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11830049001173045809542293 554533546929986522322295)
                ·
                  refine ⟨831800320394979783483443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554533546929986522322295 831800320394979783483443)
                  ·
                    refine ⟨1247700480592469675225165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 831800320394979783483443 1247700480592469675225165)
                    ·
                      refine ⟨467887680222176128209437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1247700480592469675225165 467887680222176128209437)
                      ·
                        rfl

theorem cell23_911208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_911208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911208 prefixEnd_911208 := by exact prefixLift 911208
  have htrace : WordTrace (prefixWord ++ tailWord_911208) baseStart_911208 baseEnd_911208 := by
    simpa [prefixWord, tailWord_911208, baseEnd_911208] using wordTrace_append hprefix tailTrace_911208
  have hstable : (prefixWord ++ tailWord_911208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911208).length < 2 ^ (prefixWord ++ tailWord_911208).sum := by decide
  have hdescent : baseEnd_911208 < baseStart_911208 := by decide
  rcases family_descends (prefixWord ++ tailWord_911208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911237 : List Nat := [1, 3, 1, 1, 3, 2, 3, 9]
def baseStart_911237 : Nat := 118140960795 + 911237 * 2 ^ 59
def prefixEnd_911237 : Nat := 4983230072969 + 3 ^ 40 * 911237 * 2
def baseEnd_911237 : Nat := 17329724857820611657289

theorem tailTrace_911237 : CollatzResearch.WordTrace tailWord_911237 prefixEnd_911237 17329724857820611657289 := by
  unfold tailWord_911237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33235543799751450734619965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22157029199834300489746643 33235543799751450734619965)
  ·
    refine ⟨12463328924906794025482487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33235543799751450734619965 12463328924906794025482487)
    ·
      refine ⟨18694993387360191038223731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12463328924906794025482487 18694993387360191038223731)
      ·
        refine ⟨28042490081040286557335597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18694993387360191038223731 28042490081040286557335597)
        ·
          refine ⟨10515933780390107459000849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28042490081040286557335597 10515933780390107459000849)
          ·
            refine ⟨7886950335292580594250637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10515933780390107459000849 7886950335292580594250637)
            ·
              refine ⟨2957606375734717722843989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7886950335292580594250637 2957606375734717722843989)
              ·
                refine ⟨17329724857820611657289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2957606375734717722843989 17329724857820611657289)
                ·
                  rfl

theorem cell23_911237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 9].length) (baseStart_911237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911237 prefixEnd_911237 := by exact prefixLift 911237
  have htrace : WordTrace (prefixWord ++ tailWord_911237) baseStart_911237 baseEnd_911237 := by
    simpa [prefixWord, tailWord_911237, baseEnd_911237] using wordTrace_append hprefix tailTrace_911237
  have hstable : (prefixWord ++ tailWord_911237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911237).length < 2 ^ (prefixWord ++ tailWord_911237).sum := by decide
  have hdescent : baseEnd_911237 < baseStart_911237 := by decide
  rcases family_descends (prefixWord ++ tailWord_911237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911242 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_911242 : Nat := 118140960795 + 911242 * 2 ^ 59
def prefixEnd_911242 : Nat := 4983230072969 + 3 ^ 40 * 911242 * 2
def baseEnd_911242 : Nat := 467905138564428995184281

theorem tailTrace_911242 : CollatzResearch.WordTrace tailWord_911242 prefixEnd_911242 467905138564428995184281 := by
  unfold tailWord_911242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308931541183334147137995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22157150776488891059034653 8308931541183334147137995)
  ·
    refine ⟨12463397311775001220706993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8308931541183334147137995 12463397311775001220706993)
    ·
      refine ⟨9347547983831250915530245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12463397311775001220706993 9347547983831250915530245)
      ·
        refine ⟨1752665246968359546661921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9347547983831250915530245 1752665246968359546661921)
        ·
          refine ⟨1314498935226269659996441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1752665246968359546661921 1314498935226269659996441)
          ·
            refine ⟨985874201419702244997331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314498935226269659996441 985874201419702244997331)
            ·
              refine ⟨1478811302129553367495997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985874201419702244997331 1478811302129553367495997)
              ·
                refine ⟨554554238298582512810999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478811302129553367495997 554554238298582512810999)
                ·
                  refine ⟨831831357447873769216499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554554238298582512810999 831831357447873769216499)
                  ·
                    refine ⟨1247747036171810653824749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 831831357447873769216499 1247747036171810653824749)
                    ·
                      refine ⟨467905138564428995184281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1247747036171810653824749 467905138564428995184281)
                      ·
                        rfl

theorem cell23_911242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_911242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911242 prefixEnd_911242 := by exact prefixLift 911242
  have htrace : WordTrace (prefixWord ++ tailWord_911242) baseStart_911242 baseEnd_911242 := by
    simpa [prefixWord, tailWord_911242, baseEnd_911242] using wordTrace_append hprefix tailTrace_911242
  have hstable : (prefixWord ++ tailWord_911242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911242).length < 2 ^ (prefixWord ++ tailWord_911242).sum := by decide
  have hdescent : baseEnd_911242 < baseStart_911242 := by decide
  rcases family_descends (prefixWord ++ tailWord_911242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911267 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 7]
def baseStart_911267 : Nat := 118140960795 + 911267 * 2 ^ 59
def prefixEnd_911267 : Nat := 4983230072969 + 3 ^ 40 * 911267 * 2
def baseEnd_911267 : Nat := 155972658526930465790555

theorem tailTrace_911267 : CollatzResearch.WordTrace tailWord_911267 prefixEnd_911267 155972658526930465790555 := by
  unfold tailWord_911267
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236637989642765858212055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22157758659761843905474703 33236637989642765858212055)
  ·
    refine ⟨49854956984464148787318083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33236637989642765858212055 49854956984464148787318083)
    ·
      refine ⟨74782435476696223180977125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49854956984464148787318083 74782435476696223180977125)
      ·
        refine ⟨14021706651880541846433211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74782435476696223180977125 14021706651880541846433211)
        ·
          refine ⟨21032559977820812769649817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021706651880541846433211 21032559977820812769649817)
          ·
            refine ⟨15774419983365609577237363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21032559977820812769649817 15774419983365609577237363)
            ·
              refine ⟨23661629975048414365856045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774419983365609577237363 23661629975048414365856045)
              ·
                refine ⟨8873111240643155387196017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23661629975048414365856045 8873111240643155387196017)
                ·
                  refine ⟨6654833430482366540397013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873111240643155387196017 6654833430482366540397013)
                  ·
                    refine ⟨155972658526930465790555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6654833430482366540397013 155972658526930465790555)
                    ·
                      rfl

theorem cell23_911267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_911267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911267 prefixEnd_911267 := by exact prefixLift 911267
  have htrace : WordTrace (prefixWord ++ tailWord_911267) baseStart_911267 baseEnd_911267 := by
    simpa [prefixWord, tailWord_911267, baseEnd_911267] using wordTrace_append hprefix tailTrace_911267
  have hstable : (prefixWord ++ tailWord_911267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911267).length < 2 ^ (prefixWord ++ tailWord_911267).sum := by decide
  have hdescent : baseEnd_911267 < baseStart_911267 := by decide
  rcases family_descends (prefixWord ++ tailWord_911267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911287 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_911287 : Nat := 118140960795 + 911287 * 2 ^ 59
def prefixEnd_911287 : Nat := 4983230072969 + 3 ^ 40 * 911287 * 2
def baseEnd_911287 : Nat := 467928245193881319121573

theorem tailTrace_911287 : CollatzResearch.WordTrace tailWord_911287 prefixEnd_911287 467928245193881319121573 := by
  unfold tailWord_911287
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237367449570309273940115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22158244966380206182626743 33237367449570309273940115)
  ·
    refine ⟨49856051174355463910910173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33237367449570309273940115 49856051174355463910910173)
    ·
      refine ⟨18696019190383298966591315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49856051174355463910910173 18696019190383298966591315)
      ·
        refine ⟨28044028785574948449886973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18696019190383298966591315 28044028785574948449886973)
        ·
          refine ⟨10516510794590605668707615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28044028785574948449886973 10516510794590605668707615)
          ·
            refine ⟨15774766191885908503061423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10516510794590605668707615 15774766191885908503061423)
            ·
              refine ⟨23662149287828862754592135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774766191885908503061423 23662149287828862754592135)
              ·
                refine ⟨35493223931743294131888203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23662149287828862754592135 35493223931743294131888203)
                ·
                  refine ⟨53239835897614941197832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35493223931743294131888203 53239835897614941197832305)
                  ·
                    refine ⟨39929876923211205898374229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53239835897614941197832305 39929876923211205898374229)
                    ·
                      refine ⟨467928245193881319121573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39929876923211205898374229 467928245193881319121573)
                      ·
                        rfl

theorem cell23_911287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_911287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911287 prefixEnd_911287 := by exact prefixLift 911287
  have htrace : WordTrace (prefixWord ++ tailWord_911287) baseStart_911287 baseEnd_911287 := by
    simpa [prefixWord, tailWord_911287, baseEnd_911287] using wordTrace_append hprefix tailTrace_911287
  have hstable : (prefixWord ++ tailWord_911287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911287).length < 2 ^ (prefixWord ++ tailWord_911287).sum := by decide
  have hdescent : baseEnd_911287 < baseStart_911287 := by decide
  rcases family_descends (prefixWord ++ tailWord_911287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911338 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_911338 : Nat := 118140960795 + 911338 * 2 ^ 59
def prefixEnd_911338 : Nat := 4983230072969 + 3 ^ 40 * 911338 * 2
def baseEnd_911338 : Nat := 467954432707260619583839

theorem tailTrace_911338 : CollatzResearch.WordTrace tailWord_911338 prefixEnd_911338 467954432707260619583839 := by
  unfold tailWord_911338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309806893096386246011667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22159485048257029989364445 8309806893096386246011667)
  ·
    refine ⟨12464710339644579369017501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309806893096386246011667 12464710339644579369017501)
    ·
      refine ⟨4674266377366717263381563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12464710339644579369017501 4674266377366717263381563)
      ·
        refine ⟨7011399566050075895072345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674266377366717263381563 7011399566050075895072345)
        ·
          refine ⟨5258549674537556921304259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011399566050075895072345 5258549674537556921304259)
          ·
            refine ⟨7887824511806335381956389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258549674537556921304259 7887824511806335381956389)
            ·
              refine ⟨1478967095963687884116823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7887824511806335381956389 1478967095963687884116823)
              ·
                refine ⟨2218450643945531826175235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478967095963687884116823 2218450643945531826175235)
                ·
                  refine ⟨3327675965918297739262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218450643945531826175235 3327675965918297739262853)
                  ·
                    refine ⟨623939243609680826111785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327675965918297739262853 623939243609680826111785)
                    ·
                      refine ⟨467954432707260619583839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623939243609680826111785 467954432707260619583839)
                      ·
                        rfl

theorem cell23_911338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_911338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911338 prefixEnd_911338 := by exact prefixLift 911338
  have htrace : WordTrace (prefixWord ++ tailWord_911338) baseStart_911338 baseEnd_911338 := by
    simpa [prefixWord, tailWord_911338, baseEnd_911338] using wordTrace_append hprefix tailTrace_911338
  have hstable : (prefixWord ++ tailWord_911338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911338).length < 2 ^ (prefixWord ++ tailWord_911338).sum := by decide
  have hdescent : baseEnd_911338 < baseStart_911338 := by decide
  rcases family_descends (prefixWord ++ tailWord_911338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911384 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_911384 : Nat := 118140960795 + 911384 * 2 ^ 59
def prefixEnd_911384 : Nat := 4983230072969 + 3 ^ 40 * 911384 * 2
def baseEnd_911384 : Nat := 467978052817367439608627

theorem tailTrace_911384 : CollatzResearch.WordTrace tailWord_911384 prefixEnd_911384 467978052817367439608627 := by
  unfold tailWord_911384
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620452665109447420110603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22160603553479263226814137 16620452665109447420110603)
  ·
    refine ⟨24930678997664171130165905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16620452665109447420110603 24930678997664171130165905)
    ·
      refine ⟨18698009248248128347624429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24930678997664171130165905 18698009248248128347624429)
      ·
        refine ⟨7011753468093048130359161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18698009248248128347624429 7011753468093048130359161)
        ·
          refine ⟨5258815101069786097769371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011753468093048130359161 5258815101069786097769371)
          ·
            refine ⟨7888222651604679146654057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258815101069786097769371 7888222651604679146654057)
            ·
              refine ⟨5916166988703509359990543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888222651604679146654057 5916166988703509359990543)
              ·
                refine ⟨8874250483055264039985815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916166988703509359990543 8874250483055264039985815)
                ·
                  refine ⟨13311375724582896059978723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874250483055264039985815 13311375724582896059978723)
                  ·
                    refine ⟨19967063586874344089968085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13311375724582896059978723 19967063586874344089968085)
                    ·
                      refine ⟨467978052817367439608627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19967063586874344089968085 467978052817367439608627)
                      ·
                        rfl

theorem cell23_911384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_911384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911384 prefixEnd_911384 := by exact prefixLift 911384
  have htrace : WordTrace (prefixWord ++ tailWord_911384) baseStart_911384 baseEnd_911384 := by
    simpa [prefixWord, tailWord_911384, baseEnd_911384] using wordTrace_append hprefix tailTrace_911384
  have hstable : (prefixWord ++ tailWord_911384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911384).length < 2 ^ (prefixWord ++ tailWord_911384).sum := by decide
  have hdescent : baseEnd_911384 < baseStart_911384 := by decide
  rcases family_descends (prefixWord ++ tailWord_911384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911411 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 6, 2]
def baseStart_911411 : Nat := 118140960795 + 911411 * 2 ^ 59
def prefixEnd_911411 : Nat := 4983230072969 + 3 ^ 40 * 911411 * 2
def baseEnd_911411 : Nat := 467991916795038833971003

theorem tailTrace_911411 : CollatzResearch.WordTrace tailWord_911411 prefixEnd_911411 467991916795038833971003 := by
  unfold tailWord_911411
  simp only [CollatzResearch.WordTrace]
  refine ⟨33241890101121078451454087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22161260067414052300969391 33241890101121078451454087)
  ·
    refine ⟨49862835151681617677181131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33241890101121078451454087 49862835151681617677181131)
    ·
      refine ⟨74794252727522426515771697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49862835151681617677181131 74794252727522426515771697)
      ·
        refine ⟨56095689545641819886828773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74794252727522426515771697 56095689545641819886828773)
        ·
          refine ⟨10517941789807841228780395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56095689545641819886828773 10517941789807841228780395)
          ·
            refine ⟨15776912684711761843170593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517941789807841228780395 15776912684711761843170593)
            ·
              refine ⟨11832684513533821382377945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15776912684711761843170593 11832684513533821382377945)
              ·
                refine ⟨8874513385150366036783459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832684513533821382377945 8874513385150366036783459)
                ·
                  refine ⟨13311770077725549055175189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874513385150366036783459 13311770077725549055175189)
                  ·
                    refine ⟨623989222393385111961337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13311770077725549055175189 623989222393385111961337)
                    ·
                      refine ⟨467991916795038833971003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 623989222393385111961337 467991916795038833971003)
                      ·
                        rfl

theorem cell23_911411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6, 2].length) (baseStart_911411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911411 prefixEnd_911411 := by exact prefixLift 911411
  have htrace : WordTrace (prefixWord ++ tailWord_911411) baseStart_911411 baseEnd_911411 := by
    simpa [prefixWord, tailWord_911411, baseEnd_911411] using wordTrace_append hprefix tailTrace_911411
  have hstable : (prefixWord ++ tailWord_911411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911411).length < 2 ^ (prefixWord ++ tailWord_911411).sum := by decide
  have hdescent : baseEnd_911411 < baseStart_911411 := by decide
  rcases family_descends (prefixWord ++ tailWord_911411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911412 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 5]
def baseStart_911412 : Nat := 118140960795 + 911412 * 2 ^ 59
def prefixEnd_911412 : Nat := 4983230072969 + 3 ^ 40 * 911412 * 2
def baseEnd_911412 : Nat := 51999158919521481117611

theorem tailTrace_911412 : CollatzResearch.WordTrace tailWord_911412 prefixEnd_911412 51999158919521481117611 := by
  unfold tailWord_911412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620963287058727811120245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22161284382744970414826993 16620963287058727811120245)
  ·
    refine ⟨1558215308161755732292523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16620963287058727811120245 1558215308161755732292523)
    ·
      refine ⟨2337322962242633598438785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558215308161755732292523 2337322962242633598438785)
      ·
        refine ⟨1752992221681975198829089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337322962242633598438785 1752992221681975198829089)
        ·
          refine ⟨1314744166261481399121817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1752992221681975198829089 1314744166261481399121817)
          ·
            refine ⟨986058124696111049341363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314744166261481399121817 986058124696111049341363)
            ·
              refine ⟨1479087187044166574012045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986058124696111049341363 1479087187044166574012045)
              ·
                refine ⟨554657695141562465254517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479087187044166574012045 554657695141562465254517)
                ·
                  refine ⟨51999158919521481117611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554657695141562465254517 51999158919521481117611)
                  ·
                    rfl

theorem cell23_911412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_911412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911412 prefixEnd_911412 := by exact prefixLift 911412
  have htrace : WordTrace (prefixWord ++ tailWord_911412) baseStart_911412 baseEnd_911412 := by
    simpa [prefixWord, tailWord_911412, baseEnd_911412] using wordTrace_append hprefix tailTrace_911412
  have hstable : (prefixWord ++ tailWord_911412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911412).length < 2 ^ (prefixWord ++ tailWord_911412).sum := by decide
  have hdescent : baseEnd_911412 < baseStart_911412 := by decide
  rcases family_descends (prefixWord ++ tailWord_911412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911438 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_911438 : Nat := 118140960795 + 911438 * 2 ^ 59
def prefixEnd_911438 : Nat := 4983230072969 + 3 ^ 40 * 911438 * 2
def baseEnd_911438 : Nat := 156001926924236742777793

theorem tailTrace_911438 : CollatzResearch.WordTrace tailWord_911438 prefixEnd_911438 156001926924236742777793 := by
  unfold tailWord_911438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155359359002907757835871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22161916581348841375124645 4155359359002907757835871)
  ·
    refine ⟨6233039038504361636753807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155359359002907757835871 6233039038504361636753807)
    ·
      refine ⟨9349558557756542455130711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233039038504361636753807 9349558557756542455130711)
      ·
        refine ⟨14024337836634813682696067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349558557756542455130711 14024337836634813682696067)
        ·
          refine ⟨21036506754952220524044101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024337836634813682696067 21036506754952220524044101)
          ·
            refine ⟨3944345016553541348258269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21036506754952220524044101 3944345016553541348258269)
            ·
              refine ⟨1479129381207578005596851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3944345016553541348258269 1479129381207578005596851)
              ·
                refine ⟨2218694071811367008395277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479129381207578005596851 2218694071811367008395277)
                ·
                  refine ⟨832010276929262628148229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2218694071811367008395277 832010276929262628148229)
                  ·
                    refine ⟨156001926924236742777793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832010276929262628148229 156001926924236742777793)
                    ·
                      rfl

theorem cell23_911438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_911438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911438 prefixEnd_911438 := by exact prefixLift 911438
  have htrace : WordTrace (prefixWord ++ tailWord_911438) baseStart_911438 baseEnd_911438 := by
    simpa [prefixWord, tailWord_911438, baseEnd_911438] using wordTrace_append hprefix tailTrace_911438
  have hstable : (prefixWord ++ tailWord_911438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911438).length < 2 ^ (prefixWord ++ tailWord_911438).sum := by decide
  have hdescent : baseEnd_911438 < baseStart_911438 := by decide
  rcases family_descends (prefixWord ++ tailWord_911438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911489 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 1, 4]
def baseStart_911489 : Nat := 118140960795 + 911489 * 2 ^ 59
def prefixEnd_911489 : Nat := 4983230072969 + 3 ^ 40 * 911489 * 2
def baseEnd_911489 : Nat := 156010656095363176265215

theorem tailTrace_911489 : CollatzResearch.WordTrace tailWord_911489 prefixEnd_911489 156010656095363176265215 := by
  unfold tailWord_911489
  simp only [CollatzResearch.WordTrace]
  refine ⟨33244734994838497772793521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22163156663225665181862347 33244734994838497772793521)
  ·
    refine ⟨24933551246128873329595141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33244734994838497772793521 24933551246128873329595141)
    ·
      refine ⟨4675040858649163749299089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24933551246128873329595141 4675040858649163749299089)
      ·
        refine ⟨3506280643986872811974317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4675040858649163749299089 3506280643986872811974317)
        ·
          refine ⟨1314855241495077304490369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3506280643986872811974317 1314855241495077304490369)
          ·
            refine ⟨986141431121307978367777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314855241495077304490369 986141431121307978367777)
            ·
              refine ⟨739606073340980983775833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986141431121307978367777 739606073340980983775833)
              ·
                refine ⟨554704555005735737831875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739606073340980983775833 554704555005735737831875)
                ·
                  refine ⟨832056832508603606747813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554704555005735737831875 832056832508603606747813)
                  ·
                    refine ⟨156010656095363176265215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832056832508603606747813 156010656095363176265215)
                    ·
                      rfl

theorem cell23_911489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_911489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911489 prefixEnd_911489 := by exact prefixLift 911489
  have htrace : WordTrace (prefixWord ++ tailWord_911489) baseStart_911489 baseEnd_911489 := by
    simpa [prefixWord, tailWord_911489, baseEnd_911489] using wordTrace_append hprefix tailTrace_911489
  have hstable : (prefixWord ++ tailWord_911489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911489).length < 2 ^ (prefixWord ++ tailWord_911489).sum := by decide
  have hdescent : baseEnd_911489 < baseStart_911489 := by decide
  rcases family_descends (prefixWord ++ tailWord_911489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911522 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_911522 : Nat := 118140960795 + 911522 * 2 ^ 59
def prefixEnd_911522 : Nat := 4983230072969 + 3 ^ 40 * 911522 * 2
def baseEnd_911522 : Nat := 468048913147687899682993

theorem tailTrace_911522 : CollatzResearch.WordTrace tailWord_911522 prefixEnd_911522 468048913147687899682993 := by
  unfold tailWord_911522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311484650929736102186205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22163959069145962939163213 8311484650929736102186205)
  ·
    refine ⟨3116806744098651038319827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8311484650929736102186205 3116806744098651038319827)
    ·
      refine ⟨4675210116147976557479741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116806744098651038319827 4675210116147976557479741)
      ·
        refine ⟨1753203793555491209054903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4675210116147976557479741 1753203793555491209054903)
        ·
          refine ⟨2629805690333236813582355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753203793555491209054903 2629805690333236813582355)
          ·
            refine ⟨3944708535499855220373533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629805690333236813582355 3944708535499855220373533)
            ·
              refine ⟨1479265700812445707640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3944708535499855220373533 1479265700812445707640075)
              ·
                refine ⟨2218898551218668561460113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479265700812445707640075 2218898551218668561460113)
                ·
                  refine ⟨1664173913414001421095085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218898551218668561460113 1664173913414001421095085)
                  ·
                    refine ⟨624065217530250532910657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664173913414001421095085 624065217530250532910657)
                    ·
                      refine ⟨468048913147687899682993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624065217530250532910657 468048913147687899682993)
                      ·
                        rfl

theorem cell23_911522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_911522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911522 prefixEnd_911522 := by exact prefixLift 911522
  have htrace : WordTrace (prefixWord ++ tailWord_911522) baseStart_911522 baseEnd_911522 := by
    simpa [prefixWord, tailWord_911522, baseEnd_911522] using wordTrace_append hprefix tailTrace_911522
  have hstable : (prefixWord ++ tailWord_911522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911522).length < 2 ^ (prefixWord ++ tailWord_911522).sum := by decide
  have hdescent : baseEnd_911522 < baseStart_911522 := by decide
  rcases family_descends (prefixWord ++ tailWord_911522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911552 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2]
def baseStart_911552 : Nat := 118140960795 + 911552 * 2 ^ 59
def prefixEnd_911552 : Nat := 4983230072969 + 3 ^ 40 * 911552 * 2
def baseEnd_911552 : Nat := 468064317567322782307855

theorem tailTrace_911552 : CollatzResearch.WordTrace tailWord_911552 prefixEnd_911552 468064317567322782307855 := by
  unfold tailWord_911552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623516396805129766168455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22164688529073506354891273 16623516396805129766168455)
  ·
    refine ⟨24935274595207694649252683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623516396805129766168455 24935274595207694649252683)
    ·
      refine ⟨37402911892811541973879025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24935274595207694649252683 37402911892811541973879025)
      ·
        refine ⟨28052183919608656480409269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37402911892811541973879025 28052183919608656480409269)
        ·
          refine ⟨2629892242463311545038369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28052183919608656480409269 2629892242463311545038369)
          ·
            refine ⟨1972419181847483658778777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629892242463311545038369 1972419181847483658778777)
            ·
              refine ⟨1479314386385612744084083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972419181847483658778777 1479314386385612744084083)
              ·
                refine ⟨2218971579578419116126125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479314386385612744084083 2218971579578419116126125)
                ·
                  refine ⟨832114342341907168547297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2218971579578419116126125 832114342341907168547297)
                  ·
                    refine ⟨624085756756430376410473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832114342341907168547297 624085756756430376410473)
                    ·
                      refine ⟨468064317567322782307855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624085756756430376410473 468064317567322782307855)
                      ·
                        rfl

theorem cell23_911552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_911552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911552 prefixEnd_911552 := by exact prefixLift 911552
  have htrace : WordTrace (prefixWord ++ tailWord_911552) baseStart_911552 baseEnd_911552 := by
    simpa [prefixWord, tailWord_911552, baseEnd_911552] using wordTrace_append hprefix tailTrace_911552
  have hstable : (prefixWord ++ tailWord_911552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911552).length < 2 ^ (prefixWord ++ tailWord_911552).sum := by decide
  have hdescent : baseEnd_911552 < baseStart_911552 := by decide
  rcases family_descends (prefixWord ++ tailWord_911552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911595 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 1, 3, 2]
def baseStart_911595 : Nat := 118140960795 + 911595 * 2 ^ 59
def prefixEnd_911595 : Nat := 4983230072969 + 3 ^ 40 * 911595 * 2
def baseEnd_911595 : Nat := 468086397235466114070157

theorem tailTrace_911595 : CollatzResearch.WordTrace tailWord_911595 prefixEnd_911595 468086397235466114070157 := by
  unfold tailWord_911595
  simp only [CollatzResearch.WordTrace]
  refine ⟨33248601132454477876152239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22165734088302985250768159 33248601132454477876152239)
  ·
    refine ⟨49872901698681716814228359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33248601132454477876152239 49872901698681716814228359)
    ·
      refine ⟨74809352548022575221342539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49872901698681716814228359 74809352548022575221342539)
      ·
        refine ⟨112214028822033862832013809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74809352548022575221342539 112214028822033862832013809)
        ·
          refine ⟨84160521616525397124010357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112214028822033862832013809 84160521616525397124010357)
          ·
            refine ⟨7890048901549255980375971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84160521616525397124010357 7890048901549255980375971)
            ·
              refine ⟨11835073352323883970563957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890048901549255980375971 11835073352323883970563957)
              ·
                refine ⟨1109538126780364122240371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11835073352323883970563957 1109538126780364122240371)
                ·
                  refine ⟨1664307190170546183360557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109538126780364122240371 1664307190170546183360557)
                  ·
                    refine ⟨624115196313954818760209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664307190170546183360557 624115196313954818760209)
                    ·
                      refine ⟨468086397235466114070157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624115196313954818760209 468086397235466114070157)
                      ·
                        rfl

theorem cell23_911595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3, 2].length) (baseStart_911595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911595 prefixEnd_911595 := by exact prefixLift 911595
  have htrace : WordTrace (prefixWord ++ tailWord_911595) baseStart_911595 baseEnd_911595 := by
    simpa [prefixWord, tailWord_911595, baseEnd_911595] using wordTrace_append hprefix tailTrace_911595
  have hstable : (prefixWord ++ tailWord_911595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911595).length < 2 ^ (prefixWord ++ tailWord_911595).sum := by decide
  have hdescent : baseEnd_911595 < baseStart_911595 := by decide
  rcases family_descends (prefixWord ++ tailWord_911595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911601 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_911601 : Nat := 118140960795 + 911601 * 2 ^ 59
def prefixEnd_911601 : Nat := 4983230072969 + 3 ^ 40 * 911601 * 2
def baseEnd_911601 : Nat := 156029826039797696865043

theorem tailTrace_911601 : CollatzResearch.WordTrace tailWord_911601 prefixEnd_911601 156029826039797696865043 := by
  unfold tailWord_911601
  simp only [CollatzResearch.WordTrace]
  refine ⟨33248819970432740900870657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22165879980288493933913771 33248819970432740900870657)
  ·
    refine ⟨24936614977824555675652993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33248819970432740900870657 24936614977824555675652993)
    ·
      refine ⟨18702461233368416756739745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24936614977824555675652993 18702461233368416756739745)
      ·
        refine ⟨14026845925026312567554809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18702461233368416756739745 14026845925026312567554809)
        ·
          refine ⟨10520134443769734425666107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026845925026312567554809 10520134443769734425666107)
          ·
            refine ⟨15780201665654601638499161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520134443769734425666107 15780201665654601638499161)
            ·
              refine ⟨11835151249240951228874371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780201665654601638499161 11835151249240951228874371)
              ·
                refine ⟨17752726873861426843311557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835151249240951228874371 17752726873861426843311557)
                ·
                  refine ⟨3328636288849017533120917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17752726873861426843311557 3328636288849017533120917)
                  ·
                    refine ⟨156029826039797696865043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3328636288849017533120917 156029826039797696865043)
                    ·
                      rfl

theorem cell23_911601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_911601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911601 prefixEnd_911601 := by exact prefixLift 911601
  have htrace : WordTrace (prefixWord ++ tailWord_911601) baseStart_911601 baseEnd_911601 := by
    simpa [prefixWord, tailWord_911601, baseEnd_911601] using wordTrace_append hprefix tailTrace_911601
  have hstable : (prefixWord ++ tailWord_911601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911601).length < 2 ^ (prefixWord ++ tailWord_911601).sum := by decide
  have hdescent : baseEnd_911601 < baseStart_911601 := by decide
  rcases family_descends (prefixWord ++ tailWord_911601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911631 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 7]
def baseStart_911631 : Nat := 118140960795 + 911631 * 2 ^ 59
def prefixEnd_911631 : Nat := 4983230072969 + 3 ^ 40 * 911631 * 2
def baseEnd_911631 : Nat := 52011653615447552579999

theorem tailTrace_911631 : CollatzResearch.WordTrace tailWord_911631 prefixEnd_911631 52011653615447552579999 := by
  unfold tailWord_911631
  simp only [CollatzResearch.WordTrace]
  refine ⟨33249914160324056024462747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22166609440216037349641831 33249914160324056024462747)
  ·
    refine ⟨49874871240486084036694121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33249914160324056024462747 49874871240486084036694121)
    ·
      refine ⟨37406153430364563027520591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49874871240486084036694121 37406153430364563027520591)
      ·
        refine ⟨56109230145546844541280887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37406153430364563027520591 56109230145546844541280887)
        ·
          refine ⟨84163845218320266811921331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56109230145546844541280887 84163845218320266811921331)
          ·
            refine ⟨126245767827480400217881997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84163845218320266811921331 126245767827480400217881997)
            ·
              refine ⟨47342162935305150081705749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126245767827480400217881997 47342162935305150081705749)
              ·
                refine ⟨2219163887592428910079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47342162935305150081705749 2219163887592428910079957)
                ·
                  refine ⟨52011653615447552579999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2219163887592428910079957 52011653615447552579999)
                  ·
                    rfl

theorem cell23_911631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 7].length) (baseStart_911631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911631 prefixEnd_911631 := by exact prefixLift 911631
  have htrace : WordTrace (prefixWord ++ tailWord_911631) baseStart_911631 baseEnd_911631 := by
    simpa [prefixWord, tailWord_911631, baseEnd_911631] using wordTrace_append hprefix tailTrace_911631
  have hstable : (prefixWord ++ tailWord_911631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911631).length < 2 ^ (prefixWord ++ tailWord_911631).sum := by decide
  have hdescent : baseEnd_911631 < baseStart_911631 := by decide
  rcases family_descends (prefixWord ++ tailWord_911631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911642 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_911642 : Nat := 118140960795 + 911642 * 2 ^ 59
def prefixEnd_911642 : Nat := 4983230072969 + 3 ^ 40 * 911642 * 2
def baseEnd_911642 : Nat := 468110530826227430182441

theorem tailTrace_911642 : CollatzResearch.WordTrace tailWord_911642 prefixEnd_911642 468110530826227430182441 := by
  unfold tailWord_911642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312578840821051225778295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22166876908856136602075453 8312578840821051225778295)
  ·
    refine ⟨12468868261231576838667443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312578840821051225778295 12468868261231576838667443)
    ·
      refine ⟨18703302391847365258001165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468868261231576838667443 18703302391847365258001165)
      ·
        refine ⟨7013738396942761971750437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18703302391847365258001165 7013738396942761971750437)
        ·
          refine ⟨1315075949426767869703207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7013738396942761971750437 1315075949426767869703207)
          ·
            refine ⟨1972613924140151804554811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315075949426767869703207 1972613924140151804554811)
            ·
              refine ⟨2958920886210227706832217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972613924140151804554811 2958920886210227706832217)
              ·
                refine ⟨2219190664657670780124163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958920886210227706832217 2219190664657670780124163)
                ·
                  refine ⟨3328785996986506170186245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219190664657670780124163 3328785996986506170186245)
                  ·
                    refine ⟨624147374434969906909921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328785996986506170186245 624147374434969906909921)
                    ·
                      refine ⟨468110530826227430182441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624147374434969906909921 468110530826227430182441)
                      ·
                        rfl

theorem cell23_911642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_911642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911642 prefixEnd_911642 := by exact prefixLift 911642
  have htrace : WordTrace (prefixWord ++ tailWord_911642) baseStart_911642 baseEnd_911642 := by
    simpa [prefixWord, tailWord_911642, baseEnd_911642] using wordTrace_append hprefix tailTrace_911642
  have hstable : (prefixWord ++ tailWord_911642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911642).length < 2 ^ (prefixWord ++ tailWord_911642).sum := by decide
  have hdescent : baseEnd_911642 < baseStart_911642 := by decide
  rcases family_descends (prefixWord ++ tailWord_911642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911691 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 10]
def baseStart_911691 : Nat := 118140960795 + 911691 * 2 ^ 59
def prefixEnd_911691 : Nat := 4983230072969 + 3 ^ 40 * 911691 * 2
def baseEnd_911691 : Nat := 156045230459432579489905

theorem tailTrace_911691 : CollatzResearch.WordTrace tailWord_911691 prefixEnd_911691 156045230459432579489905 := by
  unfold tailWord_911691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252102540106686271646927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22168068360071124181097951 33252102540106686271646927)
  ·
    refine ⟨49878153810160029407470391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252102540106686271646927 49878153810160029407470391)
    ·
      refine ⟨74817230715240044111205587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49878153810160029407470391 74817230715240044111205587)
      ·
        refine ⟨112225846072860066166808381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74817230715240044111205587 112225846072860066166808381)
        ·
          refine ⟨42084692277322524812553143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112225846072860066166808381 42084692277322524812553143)
          ·
            refine ⟨63127038415983787218829715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42084692277322524812553143 63127038415983787218829715)
            ·
              refine ⟨94690557623975680828244573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63127038415983787218829715 94690557623975680828244573)
              ·
                refine ⟨35508959108990880310591715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94690557623975680828244573 35508959108990880310591715)
                ·
                  refine ⟨53263438663486320465887573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35508959108990880310591715 53263438663486320465887573)
                  ·
                    refine ⟨156045230459432579489905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 53263438663486320465887573 156045230459432579489905)
                    ·
                      rfl

theorem cell23_911691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_911691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911691 prefixEnd_911691 := by exact prefixLift 911691
  have htrace : WordTrace (prefixWord ++ tailWord_911691) baseStart_911691 baseEnd_911691 := by
    simpa [prefixWord, tailWord_911691, baseEnd_911691] using wordTrace_append hprefix tailTrace_911691
  have hstable : (prefixWord ++ tailWord_911691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911691).length < 2 ^ (prefixWord ++ tailWord_911691).sum := by decide
  have hdescent : baseEnd_911691 < baseStart_911691 := by decide
  rcases family_descends (prefixWord ++ tailWord_911691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911710 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_911710 : Nat := 118140960795 + 911710 * 2 ^ 59
def prefixEnd_911710 : Nat := 4983230072969 + 3 ^ 40 * 911710 * 2
def baseEnd_911710 : Nat := 468145447510733164132129

theorem tailTrace_911710 : CollatzResearch.WordTrace tailWord_911710 prefixEnd_911710 468145447510733164132129 := by
  unfold tailWord_911710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156599440879731564573573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22168530351358568344392389 4156599440879731564573573)
  ·
    refine ⟨779362395164949668357545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4156599440879731564573573 779362395164949668357545)
    ·
      refine ⟨584521796373712251268159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 779362395164949668357545 584521796373712251268159)
      ·
        refine ⟨876782694560568376902239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584521796373712251268159 876782694560568376902239)
        ·
          refine ⟨1315174041840852565353359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876782694560568376902239 1315174041840852565353359)
          ·
            refine ⟨1972761062761278848030039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315174041840852565353359 1972761062761278848030039)
            ·
              refine ⟨2959141594141918272045059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972761062761278848030039 2959141594141918272045059)
              ·
                refine ⟨4438712391212877408067589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959141594141918272045059 4438712391212877408067589)
                ·
                  refine ⟨832258573352414514012673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4438712391212877408067589 832258573352414514012673)
                  ·
                    refine ⟨624193930014310885509505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832258573352414514012673 624193930014310885509505)
                    ·
                      refine ⟨468145447510733164132129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624193930014310885509505 468145447510733164132129)
                      ·
                        rfl

theorem cell23_911710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_911710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911710 prefixEnd_911710 := by exact prefixLift 911710
  have htrace : WordTrace (prefixWord ++ tailWord_911710) baseStart_911710 baseEnd_911710 := by
    simpa [prefixWord, tailWord_911710, baseEnd_911710] using wordTrace_append hprefix tailTrace_911710
  have hstable : (prefixWord ++ tailWord_911710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911710).length < 2 ^ (prefixWord ++ tailWord_911710).sum := by decide
  have hdescent : baseEnd_911710 < baseStart_911710 := by decide
  rcases family_descends (prefixWord ++ tailWord_911710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911715 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 4, 2]
def baseStart_911715 : Nat := 118140960795 + 911715 * 2 ^ 59
def prefixEnd_911715 : Nat := 4983230072969 + 3 ^ 40 * 911715 * 2
def baseEnd_911715 : Nat := 468148014914005644569605

theorem tailTrace_911715 : CollatzResearch.WordTrace tailWord_911715 prefixEnd_911715 468148014914005644569605 := by
  unfold tailWord_911715
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252977892019738370520599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22168651928013158913680399 33252977892019738370520599)
  ·
    refine ⟨49879466838029607555780899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252977892019738370520599 49879466838029607555780899)
    ·
      refine ⟨74819200257044411333671349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49879466838029607555780899 74819200257044411333671349)
      ·
        refine ⟨7014300024097913562531689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74819200257044411333671349 7014300024097913562531689)
        ·
          refine ⟨5260725018073435171898767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7014300024097913562531689 5260725018073435171898767)
          ·
            refine ⟨7891087527110152757848151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260725018073435171898767 7891087527110152757848151)
            ·
              refine ⟨11836631290665229136772227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891087527110152757848151 11836631290665229136772227)
              ·
                refine ⟨17754946935997843705158341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836631290665229136772227 17754946935997843705158341)
                ·
                  refine ⟨3329052550499595694717189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17754946935997843705158341 3329052550499595694717189)
                  ·
                    refine ⟨624197353218674192759473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3329052550499595694717189 624197353218674192759473)
                    ·
                      refine ⟨468148014914005644569605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624197353218674192759473 468148014914005644569605)
                      ·
                        rfl

theorem cell23_911715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_911715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911715 prefixEnd_911715 := by exact prefixLift 911715
  have htrace : WordTrace (prefixWord ++ tailWord_911715) baseStart_911715 baseEnd_911715 := by
    simpa [prefixWord, tailWord_911715, baseEnd_911715] using wordTrace_append hprefix tailTrace_911715
  have hstable : (prefixWord ++ tailWord_911715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911715).length < 2 ^ (prefixWord ++ tailWord_911715).sum := by decide
  have hdescent : baseEnd_911715 < baseStart_911715 := by decide
  rcases family_descends (prefixWord ++ tailWord_911715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911788 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_911788 : Nat := 118140960795 + 911788 * 2 ^ 59
def prefixEnd_911788 : Nat := 4983230072969 + 3 ^ 40 * 911788 * 2
def baseEnd_911788 : Nat := 468185499001783858956769

theorem tailTrace_911788 : CollatzResearch.WordTrace tailWord_911788 prefixEnd_911788 468185499001783858956769 := by
  unfold tailWord_911788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16627820210377635918964009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22170426947170181225285345 16627820210377635918964009)
  ·
    refine ⟨12470865157783226939223007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16627820210377635918964009 12470865157783226939223007)
    ·
      refine ⟨18706297736674840408834511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12470865157783226939223007 18706297736674840408834511)
      ·
        refine ⟨28059446605012260613251767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18706297736674840408834511 28059446605012260613251767)
        ·
          refine ⟨42089169907518390919877651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28059446605012260613251767 42089169907518390919877651)
          ·
            refine ⟨63133754861277586379816477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42089169907518390919877651 63133754861277586379816477)
            ·
              refine ⟨23675158072979094892431179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63133754861277586379816477 23675158072979094892431179)
              ·
                refine ⟨35512737109468642338646769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23675158072979094892431179 35512737109468642338646769)
                ·
                  refine ⟨26634552832101481753985077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35512737109468642338646769 26634552832101481753985077)
                  ·
                    refine ⟨2496989328009513914436101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26634552832101481753985077 2496989328009513914436101)
                    ·
                      refine ⟨468185499001783858956769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2496989328009513914436101 468185499001783858956769)
                      ·
                        rfl

theorem cell23_911788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_911788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911788 prefixEnd_911788 := by exact prefixLift 911788
  have htrace : WordTrace (prefixWord ++ tailWord_911788) baseStart_911788 baseEnd_911788 := by
    simpa [prefixWord, tailWord_911788, baseEnd_911788] using wordTrace_append hprefix tailTrace_911788
  have hstable : (prefixWord ++ tailWord_911788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911788).length < 2 ^ (prefixWord ++ tailWord_911788).sum := by decide
  have hdescent : baseEnd_911788 < baseStart_911788 := by decide
  rcases family_descends (prefixWord ++ tailWord_911788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911815 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 6]
def baseStart_911815 : Nat := 118140960795 + 911815 * 2 ^ 59
def prefixEnd_911815 : Nat := 4983230072969 + 3 ^ 40 * 911815 * 2
def baseEnd_911815 : Nat := 156066454326485084439715

theorem tailTrace_911815 : CollatzResearch.WordTrace tailWord_911815 prefixEnd_911815 156066454326485084439715 := by
  unfold tailWord_911815
  simp only [CollatzResearch.WordTrace]
  refine ⟨33256625191657455449160899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22171083461104970299440599 33256625191657455449160899)
  ·
    refine ⟨49884937787486183173741349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33256625191657455449160899 49884937787486183173741349)
    ·
      refine ⟨9353425835153659345076503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49884937787486183173741349 9353425835153659345076503)
      ·
        refine ⟨14030138752730489017614755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353425835153659345076503 14030138752730489017614755)
        ·
          refine ⟨21045208129095733526422133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030138752730489017614755 21045208129095733526422133)
          ·
            refine ⟨1972988262102725018102075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21045208129095733526422133 1972988262102725018102075)
            ·
              refine ⟨2959482393154087527153113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972988262102725018102075 2959482393154087527153113)
              ·
                refine ⟨2219611794865565645364835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959482393154087527153113 2219611794865565645364835)
                ·
                  refine ⟨3329417692298348468047253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219611794865565645364835 3329417692298348468047253)
                  ·
                    refine ⟨156066454326485084439715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3329417692298348468047253 156066454326485084439715)
                    ·
                      rfl

theorem cell23_911815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_911815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911815 prefixEnd_911815 := by exact prefixLift 911815
  have htrace : WordTrace (prefixWord ++ tailWord_911815) baseStart_911815 baseEnd_911815 := by
    simpa [prefixWord, tailWord_911815, baseEnd_911815] using wordTrace_append hprefix tailTrace_911815
  have hstable : (prefixWord ++ tailWord_911815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911815).length < 2 ^ (prefixWord ++ tailWord_911815).sum := by decide
  have hdescent : baseEnd_911815 < baseStart_911815 := by decide
  rcases family_descends (prefixWord ++ tailWord_911815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911862 : List Nat := [5, 1, 1, 1, 2, 1, 5, 7]
def baseStart_911862 : Nat := 118140960795 + 911862 * 2 ^ 59
def prefixEnd_911862 : Nat := 4983230072969 + 3 ^ 40 * 911862 * 2
def baseEnd_911862 : Nat := 17341610984082095164127

theorem tailTrace_911862 : CollatzResearch.WordTrace tailWord_911862 prefixEnd_911862 17341610984082095164127 := by
  unfold tailWord_911862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078646213905448904757615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22172226281658121650747893 2078646213905448904757615)
  ·
    refine ⟨3117969320858173357136423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078646213905448904757615 3117969320858173357136423)
    ·
      refine ⟨4676953981287260035704635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117969320858173357136423 4676953981287260035704635)
      ·
        refine ⟨7015430971930890053556953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676953981287260035704635 7015430971930890053556953)
        ·
          refine ⟨5261573228948167540167715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015430971930890053556953 5261573228948167540167715)
          ·
            refine ⟨7892359843422251310251573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261573228948167540167715 7892359843422251310251573)
            ·
              refine ⟨739908735320836060336085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7892359843422251310251573 739908735320836060336085)
              ·
                refine ⟨17341610984082095164127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 739908735320836060336085 17341610984082095164127)
                ·
                  rfl

theorem cell23_911862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_911862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911862 prefixEnd_911862 := by exact prefixLift 911862
  have htrace : WordTrace (prefixWord ++ tailWord_911862) baseStart_911862 baseEnd_911862 := by
    simpa [prefixWord, tailWord_911862, baseEnd_911862] using wordTrace_append hprefix tailTrace_911862
  have hstable : (prefixWord ++ tailWord_911862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911862).length < 2 ^ (prefixWord ++ tailWord_911862).sum := by decide
  have hdescent : baseEnd_911862 < baseStart_911862 := by decide
  rcases family_descends (prefixWord ++ tailWord_911862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911873 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_911873 : Nat := 118140960795 + 911873 * 2 ^ 59
def prefixEnd_911873 : Nat := 4983230072969 + 3 ^ 40 * 911873 * 2
def baseEnd_911873 : Nat := 468229144857416026393879

theorem tailTrace_911873 : CollatzResearch.WordTrace tailWord_911873 prefixEnd_911873 468229144857416026393879 := by
  unfold tailWord_911873
  simp only [CollatzResearch.WordTrace]
  refine ⟨33258740625447331354772273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22172493750298220903181515 33258740625447331354772273)
  ·
    refine ⟨24944055469085498516079205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33258740625447331354772273 24944055469085498516079205)
    ·
      refine ⟨4677010400453530971764851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24944055469085498516079205 4677010400453530971764851)
      ·
        refine ⟨7015515600680296457647277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677010400453530971764851 7015515600680296457647277)
        ·
          refine ⟨2630818350255111171617729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015515600680296457647277 2630818350255111171617729)
          ·
            refine ⟨1973113762691333378713297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630818350255111171617729 1973113762691333378713297)
            ·
              refine ⟨1479835322018500034034973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973113762691333378713297 1479835322018500034034973)
              ·
                refine ⟨554938245756937512763115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479835322018500034034973 554938245756937512763115)
                ·
                  refine ⟨832407368635406269144673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554938245756937512763115 832407368635406269144673)
                  ·
                    refine ⟨624305526476554701858505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832407368635406269144673 624305526476554701858505)
                    ·
                      refine ⟨468229144857416026393879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624305526476554701858505 468229144857416026393879)
                      ·
                        rfl

theorem cell23_911873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_911873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911873 prefixEnd_911873 := by exact prefixLift 911873
  have htrace : WordTrace (prefixWord ++ tailWord_911873) baseStart_911873 baseEnd_911873 := by
    simpa [prefixWord, tailWord_911873, baseEnd_911873] using wordTrace_append hprefix tailTrace_911873
  have hstable : (prefixWord ++ tailWord_911873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911873).length < 2 ^ (prefixWord ++ tailWord_911873).sum := by decide
  have hdescent : baseEnd_911873 < baseStart_911873 := by decide
  rcases family_descends (prefixWord ++ tailWord_911873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911876 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_911876 : Nat := 118140960795 + 911876 * 2 ^ 59
def prefixEnd_911876 : Nat := 4983230072969 + 3 ^ 40 * 911876 * 2
def baseEnd_911876 : Nat := 468230685299379514656365

theorem tailTrace_911876 : CollatzResearch.WordTrace tailWord_911876 prefixEnd_911876 468230685299379514656365 := by
  unfold tailWord_911876
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629425022218231433565741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22172566696290975244754321 16629425022218231433565741)
  ·
    refine ⟨6236034383331836787587153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16629425022218231433565741 6236034383331836787587153)
    ·
      refine ⟨4677025787498877590690365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6236034383331836787587153 4677025787498877590690365)
      ·
        refine ⟨1753884670312079096508887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4677025787498877590690365 1753884670312079096508887)
        ·
          refine ⟨2630827005468118644763331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753884670312079096508887 2630827005468118644763331)
          ·
            refine ⟨3946240508202177967144997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630827005468118644763331 3946240508202177967144997)
            ·
              refine ⟨739920095287908368839687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3946240508202177967144997 739920095287908368839687)
              ·
                refine ⟨1109880142931862553259531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739920095287908368839687 1109880142931862553259531)
                ·
                  refine ⟨1664820214397793829889297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109880142931862553259531 1664820214397793829889297)
                  ·
                    refine ⟨1248615160798345372416973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1664820214397793829889297 1248615160798345372416973)
                    ·
                      refine ⟨468230685299379514656365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1248615160798345372416973 468230685299379514656365)
                      ·
                        rfl

theorem cell23_911876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_911876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911876 prefixEnd_911876 := by exact prefixLift 911876
  have htrace : WordTrace (prefixWord ++ tailWord_911876) baseStart_911876 baseEnd_911876 := by
    simpa [prefixWord, tailWord_911876, baseEnd_911876] using wordTrace_append hprefix tailTrace_911876
  have hstable : (prefixWord ++ tailWord_911876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911876).length < 2 ^ (prefixWord ++ tailWord_911876).sum := by decide
  have hdescent : baseEnd_911876 < baseStart_911876 := by decide
  rcases family_descends (prefixWord ++ tailWord_911876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911905 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_911905 : Nat := 118140960795 + 911905 * 2 ^ 59
def prefixEnd_911905 : Nat := 4983230072969 + 3 ^ 40 * 911905 * 2
def baseEnd_911905 : Nat := 156081858746119967064577

theorem tailTrace_911905 : CollatzResearch.WordTrace tailWord_911905 prefixEnd_911905 156081858746119967064577 := by
  unfold tailWord_911905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259907761331400819937169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173271840887600546624779 33259907761331400819937169)
  ·
    refine ⟨24944930820998550614952877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33259907761331400819937169 24944930820998550614952877)
    ·
      refine ⟨9354349057874456480607329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24944930820998550614952877 9354349057874456480607329)
      ·
        refine ⟨7015761793405842360455497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354349057874456480607329 7015761793405842360455497)
        ·
          refine ⟨5261821345054381770341623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015761793405842360455497 5261821345054381770341623)
          ·
            refine ⟨7892732017581572655512435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261821345054381770341623 7892732017581572655512435)
            ·
              refine ⟨11839098026372358983268653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892732017581572655512435 11839098026372358983268653)
              ·
                refine ⟨4439661759889634618725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11839098026372358983268653 4439661759889634618725745)
                ·
                  refine ⟨3329746319917225964044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439661759889634618725745 3329746319917225964044309)
                  ·
                    refine ⟨156081858746119967064577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3329746319917225964044309 156081858746119967064577)
                    ·
                      rfl

theorem cell23_911905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_911905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911905 prefixEnd_911905 := by exact prefixLift 911905
  have htrace : WordTrace (prefixWord ++ tailWord_911905) baseStart_911905 baseEnd_911905 := by
    simpa [prefixWord, tailWord_911905, baseEnd_911905] using wordTrace_append hprefix tailTrace_911905
  have hstable : (prefixWord ++ tailWord_911905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911905).length < 2 ^ (prefixWord ++ tailWord_911905).sum := by decide
  have hdescent : baseEnd_911905 < baseStart_911905 := by decide
  rcases family_descends (prefixWord ++ tailWord_911905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911915 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3]
def baseStart_911915 : Nat := 118140960795 + 911915 * 2 ^ 59
def prefixEnd_911915 : Nat := 4983230072969 + 3 ^ 40 * 911915 * 2
def baseEnd_911915 : Nat := 468250711044904862068685

theorem tailTrace_911915 : CollatzResearch.WordTrace tailWord_911915 prefixEnd_911915 468250711044904862068685 := by
  unfold tailWord_911915
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260272491295172527801199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173514994196781685200799 33260272491295172527801199)
  ·
    refine ⟨49890408736942758791701799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33260272491295172527801199 49890408736942758791701799)
    ·
      refine ⟨74835613105414138187552699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49890408736942758791701799 74835613105414138187552699)
      ·
        refine ⟨112253419658121207281329049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74835613105414138187552699 112253419658121207281329049)
        ·
          refine ⟨84190064743590905460996787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112253419658121207281329049 84190064743590905460996787)
          ·
            refine ⟨126285097115386358191495181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84190064743590905460996787 126285097115386358191495181)
            ·
              refine ⟨47356911418269884321810693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126285097115386358191495181 47356911418269884321810693)
              ·
                refine ⟨8879420890925603310339505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47356911418269884321810693 8879420890925603310339505)
                ·
                  refine ⟨6659565668194202482754629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879420890925603310339505 6659565668194202482754629)
                  ·
                    refine ⟨1248668562786412965516493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659565668194202482754629 1248668562786412965516493)
                    ·
                      refine ⟨468250711044904862068685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1248668562786412965516493 468250711044904862068685)
                      ·
                        rfl

theorem cell23_911915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].length) (baseStart_911915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911915 prefixEnd_911915 := by exact prefixLift 911915
  have htrace : WordTrace (prefixWord ++ tailWord_911915) baseStart_911915 baseEnd_911915 := by
    simpa [prefixWord, tailWord_911915, baseEnd_911915] using wordTrace_append hprefix tailTrace_911915
  have hstable : (prefixWord ++ tailWord_911915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911915).length < 2 ^ (prefixWord ++ tailWord_911915).sum := by decide
  have hdescent : baseEnd_911915 < baseStart_911915 := by decide
  rcases family_descends (prefixWord ++ tailWord_911915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911924 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_911924 : Nat := 118140960795 + 911924 * 2 ^ 59
def prefixEnd_911924 : Nat := 4983230072969 + 3 ^ 40 * 911924 * 2
def baseEnd_911924 : Nat := 468255332370795326856145

theorem tailTrace_911924 : CollatzResearch.WordTrace tailWord_911924 prefixEnd_911924 468255332370795326856145 := by
  unfold tailWord_911924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630300374131283532439413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22173733832175044709919217 16630300374131283532439413)
  ·
    refine ⟨1559090660074807831166195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16630300374131283532439413 1559090660074807831166195)
    ·
      refine ⟨2338635990112211746749293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559090660074807831166195 2338635990112211746749293)
      ·
        refine ⟨876988496292079405030985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2338635990112211746749293 876988496292079405030985)
        ·
          refine ⟨657741372219059553773239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876988496292079405030985 657741372219059553773239)
          ·
            refine ⟨986612058328589330659859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657741372219059553773239 986612058328589330659859)
            ·
              refine ⟨1479918087492883995989789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986612058328589330659859 1479918087492883995989789)
              ·
                refine ⟨554969282809831498496171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479918087492883995989789 554969282809831498496171)
                ·
                  refine ⟨832453924214747247744257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554969282809831498496171 832453924214747247744257)
                  ·
                    refine ⟨624340443161060435808193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832453924214747247744257 624340443161060435808193)
                    ·
                      refine ⟨468255332370795326856145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624340443161060435808193 468255332370795326856145)
                      ·
                        rfl

theorem cell23_911924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_911924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911924 prefixEnd_911924 := by exact prefixLift 911924
  have htrace : WordTrace (prefixWord ++ tailWord_911924) baseStart_911924 baseEnd_911924 := by
    simpa [prefixWord, tailWord_911924, baseEnd_911924] using wordTrace_append hprefix tailTrace_911924
  have hstable : (prefixWord ++ tailWord_911924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911924).length < 2 ^ (prefixWord ++ tailWord_911924).sum := by decide
  have hdescent : baseEnd_911924 < baseStart_911924 := by decide
  rcases family_descends (prefixWord ++ tailWord_911924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911929 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 6, 2, 2]
def baseStart_911929 : Nat := 118140960795 + 911929 * 2 ^ 59
def prefixEnd_911929 : Nat := 4983230072969 + 3 ^ 40 * 911929 * 2
def baseEnd_911929 : Nat := 468257899774067807293621

theorem tailTrace_911929 : CollatzResearch.WordTrace tailWord_911929 prefixEnd_911929 468257899774067807293621 := by
  unfold tailWord_911929
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260783113244452918810841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173855408829635279207227 33260783113244452918810841)
  ·
    refine ⟨24945587334933339689108131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33260783113244452918810841 24945587334933339689108131)
    ·
      refine ⟨37418381002400009533662197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24945587334933339689108131 37418381002400009533662197)
      ·
        refine ⟨3507973218975000893780831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37418381002400009533662197 3507973218975000893780831)
        ·
          refine ⟨5261959828462501340671247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507973218975000893780831 5261959828462501340671247)
          ·
            refine ⟨7892939742693752011006871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261959828462501340671247 7892939742693752011006871)
            ·
              refine ⟨11839409614040628016510307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892939742693752011006871 11839409614040628016510307)
              ·
                refine ⟨17759114421060942024765461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839409614040628016510307 17759114421060942024765461)
                ·
                  refine ⟨832458488487231657410881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17759114421060942024765461 832458488487231657410881)
                  ·
                    refine ⟨624343866365423743058161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832458488487231657410881 624343866365423743058161)
                    ·
                      refine ⟨468257899774067807293621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624343866365423743058161 468257899774067807293621)
                      ·
                        rfl

theorem cell23_911929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_911929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911929 prefixEnd_911929 := by exact prefixLift 911929
  have htrace : WordTrace (prefixWord ++ tailWord_911929) baseStart_911929 baseEnd_911929 := by
    simpa [prefixWord, tailWord_911929, baseEnd_911929] using wordTrace_append hprefix tailTrace_911929
  have hstable : (prefixWord ++ tailWord_911929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911929).length < 2 ^ (prefixWord ++ tailWord_911929).sum := by decide
  have hdescent : baseEnd_911929 < baseStart_911929 := by decide
  rcases family_descends (prefixWord ++ tailWord_911929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911932 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_911932 : Nat := 118140960795 + 911932 * 2 ^ 59
def prefixEnd_911932 : Nat := 4983230072969 + 3 ^ 40 * 911932 * 2
def baseEnd_911932 : Nat := 468259440216031295556107

theorem tailTrace_911932 : CollatzResearch.WordTrace tailWord_911932 prefixEnd_911932 468259440216031295556107 := by
  unfold tailWord_911932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630446266116792215585025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22173928354822389620780033 16630446266116792215585025)
  ·
    refine ⟨12472834699587594161688769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16630446266116792215585025 12472834699587594161688769)
    ·
      refine ⟨9354626024690695621266577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12472834699587594161688769 9354626024690695621266577)
      ·
        refine ⟨7015969518518021715949933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354626024690695621266577 7015969518518021715949933)
        ·
          refine ⟨2630988569444258143481225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015969518518021715949933 2630988569444258143481225)
          ·
            refine ⟨1973241427083193607610919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630988569444258143481225 1973241427083193607610919)
            ·
              refine ⟨2959862140624790411416379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973241427083193607610919 2959862140624790411416379)
              ·
                refine ⟨4439793210937185617124569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959862140624790411416379 4439793210937185617124569)
                ·
                  refine ⟨3329844908202889212843427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439793210937185617124569 3329844908202889212843427)
                  ·
                    refine ⟨4994767362304333819265141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329844908202889212843427 4994767362304333819265141)
                    ·
                      refine ⟨468259440216031295556107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4994767362304333819265141 468259440216031295556107)
                      ·
                        rfl

theorem cell23_911932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_911932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911932 prefixEnd_911932 := by exact prefixLift 911932
  have htrace : WordTrace (prefixWord ++ tailWord_911932) baseStart_911932 baseEnd_911932 := by
    simpa [prefixWord, tailWord_911932, baseEnd_911932] using wordTrace_append hprefix tailTrace_911932
  have hstable : (prefixWord ++ tailWord_911932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911932).length < 2 ^ (prefixWord ++ tailWord_911932).sum := by decide
  have hdescent : baseEnd_911932 < baseStart_911932 := by decide
  rcases family_descends (prefixWord ++ tailWord_911932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911975 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_911975 : Nat := 118140960795 + 911975 * 2 ^ 59
def prefixEnd_911975 : Nat := 4983230072969 + 3 ^ 40 * 911975 * 2
def baseEnd_911975 : Nat := 468281519884174627318409

theorem tailTrace_911975 : CollatzResearch.WordTrace tailWord_911975 prefixEnd_911975 468281519884174627318409 := by
  unfold tailWord_911975
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262460871077802774985379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22174973914051868516656919 33262460871077802774985379)
  ·
    refine ⟨49893691306616704162478069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262460871077802774985379 49893691306616704162478069)
    ·
      refine ⟨4677533559995316015232319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49893691306616704162478069 4677533559995316015232319)
      ·
        refine ⟨7016300339992974022848479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677533559995316015232319 7016300339992974022848479)
        ·
          refine ⟨10524450509989461034272719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016300339992974022848479 10524450509989461034272719)
          ·
            refine ⟨15786675764984191551409079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524450509989461034272719 15786675764984191551409079)
            ·
              refine ⟨23680013647476287327113619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786675764984191551409079 23680013647476287327113619)
              ·
                refine ⟨35520020471214430990670429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23680013647476287327113619 35520020471214430990670429)
                ·
                  refine ⟨13320007676705411621501411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35520020471214430990670429 13320007676705411621501411)
                  ·
                    refine ⟨19980011515058117432252117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13320007676705411621501411 19980011515058117432252117)
                    ·
                      refine ⟨468281519884174627318409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19980011515058117432252117 468281519884174627318409)
                      ·
                        rfl

theorem cell23_911975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_911975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_911975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_911975 prefixEnd_911975 := by exact prefixLift 911975
  have htrace : WordTrace (prefixWord ++ tailWord_911975) baseStart_911975 baseEnd_911975 := by
    simpa [prefixWord, tailWord_911975, baseEnd_911975] using wordTrace_append hprefix tailTrace_911975
  have hstable : (prefixWord ++ tailWord_911975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911975).length < 2 ^ (prefixWord ++ tailWord_911975).sum := by decide
  have hdescent : baseEnd_911975 < baseStart_911975 := by decide
  rcases family_descends (prefixWord ++ tailWord_911975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912015 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_912015 : Nat := 118140960795 + 912015 * 2 ^ 59
def prefixEnd_912015 : Nat := 4983230072969 + 3 ^ 40 * 912015 * 2
def baseEnd_912015 : Nat := 468302059110354470818225

theorem tailTrace_912015 : CollatzResearch.WordTrace tailWord_912015 prefixEnd_912015 468302059110354470818225 := by
  unfold tailWord_912015
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263919790932889606441499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22175946527288593070960999 33263919790932889606441499)
  ·
    refine ⟨49895879686399334409662249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33263919790932889606441499 49895879686399334409662249)
    ·
      refine ⟨37421909764799500807246687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49895879686399334409662249 37421909764799500807246687)
      ·
        refine ⟨56132864647199251210870031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37421909764799500807246687 56132864647199251210870031)
        ·
          refine ⟨84199296970798876816305047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56132864647199251210870031 84199296970798876816305047)
          ·
            refine ⟨126298945456198315224457571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84199296970798876816305047 126298945456198315224457571)
            ·
              refine ⟨189448418184297472836686357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126298945456198315224457571 189448418184297472836686357)
              ·
                refine ⟨8880394602388944039219673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189448418184297472836686357 8880394602388944039219673)
                ·
                  refine ⟨6660295951791708029414755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880394602388944039219673 6660295951791708029414755)
                  ·
                    refine ⟨9990443927687562044122133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6660295951791708029414755 9990443927687562044122133)
                    ·
                      refine ⟨468302059110354470818225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9990443927687562044122133 468302059110354470818225)
                      ·
                        rfl

theorem cell23_912015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_912015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912015 prefixEnd_912015 := by exact prefixLift 912015
  have htrace : WordTrace (prefixWord ++ tailWord_912015) baseStart_912015 baseEnd_912015 := by
    simpa [prefixWord, tailWord_912015, baseEnd_912015] using wordTrace_append hprefix tailTrace_912015
  have hstable : (prefixWord ++ tailWord_912015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912015).length < 2 ^ (prefixWord ++ tailWord_912015).sum := by decide
  have hdescent : baseEnd_912015 < baseStart_912015 := by decide
  rcases family_descends (prefixWord ++ tailWord_912015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912062 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_912062 : Nat := 118140960795 + 912062 * 2 ^ 59
def prefixEnd_912062 : Nat := 4983230072969 + 3 ^ 40 * 912062 * 2
def baseEnd_912062 : Nat := 468326192701115786930509

theorem tailTrace_912062 : CollatzResearch.WordTrace tailWord_912062 prefixEnd_912062 468326192701115786930509 := by
  unfold tailWord_912062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158204252720327079175305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22177089347841744422268293 4158204252720327079175305)
  ·
    refine ⟨3118653189540245309381479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4158204252720327079175305 3118653189540245309381479)
    ·
      refine ⟨4677979784310367964072219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3118653189540245309381479 4677979784310367964072219)
      ·
        refine ⟨7016969676465551946108329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677979784310367964072219 7016969676465551946108329)
        ·
          refine ⟨5262727257349163959581247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016969676465551946108329 5262727257349163959581247)
          ·
            refine ⟨7894090886023745939371871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262727257349163959581247 7894090886023745939371871)
            ·
              refine ⟨11841136329035618909057807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894090886023745939371871 11841136329035618909057807)
              ·
                refine ⟨17761704493553428363586711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841136329035618909057807 17761704493553428363586711)
                ·
                  refine ⟨26642556740330142545380067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17761704493553428363586711 26642556740330142545380067)
                  ·
                    refine ⟨39963835110495213818070101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26642556740330142545380067 39963835110495213818070101)
                    ·
                      refine ⟨468326192701115786930509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39963835110495213818070101 468326192701115786930509)
                      ·
                        rfl

theorem cell23_912062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_912062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912062 prefixEnd_912062 := by exact prefixLift 912062
  have htrace : WordTrace (prefixWord ++ tailWord_912062) baseStart_912062 baseEnd_912062 := by
    simpa [prefixWord, tailWord_912062, baseEnd_912062] using wordTrace_append hprefix tailTrace_912062
  have hstable : (prefixWord ++ tailWord_912062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912062).length < 2 ^ (prefixWord ++ tailWord_912062).sum := by decide
  have hdescent : baseEnd_912062 < baseStart_912062 := by decide
  rcases family_descends (prefixWord ++ tailWord_912062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912076 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 6]
def baseStart_912076 : Nat := 118140960795 + 912076 * 2 ^ 59
def prefixEnd_912076 : Nat := 4983230072969 + 3 ^ 40 * 912076 * 2
def baseEnd_912076 : Nat := 52037042381142081350605

theorem tailTrace_912076 : CollatzResearch.WordTrace tailWord_912076 prefixEnd_912076 52037042381142081350605 := by
  unfold tailWord_912076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16633072321855948512206041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22177429762474598016274721 16633072321855948512206041)
  ·
    refine ⟨12474804241391961384154531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16633072321855948512206041 12474804241391961384154531)
    ·
      refine ⟨18712206362087942076231797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474804241391961384154531 18712206362087942076231797)
      ·
        refine ⟨1754269346445744569646731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18712206362087942076231797 1754269346445744569646731)
        ·
          refine ⟨2631404019668616854470097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754269346445744569646731 2631404019668616854470097)
          ·
            refine ⟨1973553014751462640852573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631404019668616854470097 1973553014751462640852573)
            ·
              refine ⟨740082380531798490319715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1973553014751462640852573 740082380531798490319715)
              ·
                refine ⟨1110123570797697735479573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740082380531798490319715 1110123570797697735479573)
                ·
                  refine ⟨52037042381142081350605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1110123570797697735479573 52037042381142081350605)
                  ·
                    rfl

theorem cell23_912076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_912076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912076 prefixEnd_912076 := by exact prefixLift 912076
  have htrace : WordTrace (prefixWord ++ tailWord_912076) baseStart_912076 baseEnd_912076 := by
    simpa [prefixWord, tailWord_912076, baseEnd_912076] using wordTrace_append hprefix tailTrace_912076
  have hstable : (prefixWord ++ tailWord_912076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912076).length < 2 ^ (prefixWord ++ tailWord_912076).sum := by decide
  have hdescent : baseEnd_912076 < baseStart_912076 := by decide
  rcases family_descends (prefixWord ++ tailWord_912076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912089 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_912089 : Nat := 118140960795 + 912089 * 2 ^ 59
def prefixEnd_912089 : Nat := 4983230072969 + 3 ^ 40 * 912089 * 2
def baseEnd_912089 : Nat := 156113352226262393764295

theorem tailTrace_912089 : CollatzResearch.WordTrace tailWord_912089 prefixEnd_912089 156113352226262393764295 := by
  unfold tailWord_912089
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266618792664800244635321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22177745861776533496423547 33266618792664800244635321)
  ·
    refine ⟨24949964094498600183476491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33266618792664800244635321 24949964094498600183476491)
    ·
      refine ⟨37424946141747900275214737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24949964094498600183476491 37424946141747900275214737)
      ·
        refine ⟨28068709606310925206411053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37424946141747900275214737 28068709606310925206411053)
        ·
          refine ⟨10525766102366596952404145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28068709606310925206411053 10525766102366596952404145)
          ·
            refine ⟨7894324576774947714303109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10525766102366596952404145 7894324576774947714303109)
            ·
              refine ⟨1480185858145302696431833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7894324576774947714303109 1480185858145302696431833)
              ·
                refine ⟨1110139393608977022323875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480185858145302696431833 1110139393608977022323875)
                ·
                  refine ⟨1665209090413465533485813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110139393608977022323875 1665209090413465533485813)
                  ·
                    refine ⟨156113352226262393764295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1665209090413465533485813 156113352226262393764295)
                    ·
                      rfl

theorem cell23_912089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_912089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912089 prefixEnd_912089 := by exact prefixLift 912089
  have htrace : WordTrace (prefixWord ++ tailWord_912089) baseStart_912089 baseEnd_912089 := by
    simpa [prefixWord, tailWord_912089, baseEnd_912089] using wordTrace_append hprefix tailTrace_912089
  have hstable : (prefixWord ++ tailWord_912089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912089).length < 2 ^ (prefixWord ++ tailWord_912089).sum := by decide
  have hdescent : baseEnd_912089 < baseStart_912089 := by decide
  rcases family_descends (prefixWord ++ tailWord_912089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912119 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 2, 4]
def baseStart_912119 : Nat := 118140960795 + 912119 * 2 ^ 59
def prefixEnd_912119 : Nat := 4983230072969 + 3 ^ 40 * 912119 * 2
def baseEnd_912119 : Nat := 156118487032807354639249

theorem tailTrace_912119 : CollatzResearch.WordTrace tailWord_912119 prefixEnd_912119 156118487032807354639249 := by
  unfold tailWord_912119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267712982556115368227411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22178475321704076912151607 33267712982556115368227411)
  ·
    refine ⟨49901569473834173052341117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33267712982556115368227411 49901569473834173052341117)
    ·
      refine ⟨18713088552687814894627919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49901569473834173052341117 18713088552687814894627919)
      ·
        refine ⟨28069632829031722341941879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18713088552687814894627919 28069632829031722341941879)
        ·
          refine ⟨42104449243547583512912819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28069632829031722341941879 42104449243547583512912819)
          ·
            refine ⟨63156673865321375269369229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42104449243547583512912819 63156673865321375269369229)
            ·
              refine ⟨23683752699495515726013461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63156673865321375269369229 23683752699495515726013461)
              ·
                refine ⟨1110175907788852299656881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23683752699495515726013461 1110175907788852299656881)
                ·
                  refine ⟨832631930841639224742661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110175907788852299656881 832631930841639224742661)
                  ·
                    refine ⟨156118487032807354639249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832631930841639224742661 156118487032807354639249)
                    ·
                      rfl

theorem cell23_912119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_912119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912119 prefixEnd_912119 := by exact prefixLift 912119
  have htrace : WordTrace (prefixWord ++ tailWord_912119) baseStart_912119 baseEnd_912119 := by
    simpa [prefixWord, tailWord_912119, baseEnd_912119] using wordTrace_append hprefix tailTrace_912119
  have hstable : (prefixWord ++ tailWord_912119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912119).length < 2 ^ (prefixWord ++ tailWord_912119).sum := by decide
  have hdescent : baseEnd_912119 < baseStart_912119 := by decide
  rcases family_descends (prefixWord ++ tailWord_912119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912122 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_912122 : Nat := 118140960795 + 912122 * 2 ^ 59
def prefixEnd_912122 : Nat := 4983230072969 + 3 ^ 40 * 912122 * 2
def baseEnd_912122 : Nat := 468357001540385552180233

theorem tailTrace_912122 : CollatzResearch.WordTrace tailWord_912122 prefixEnd_912122 468357001540385552180233 := by
  unfold tailWord_912122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316955600386311720146655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22178548267696831253724413 8316955600386311720146655)
  ·
    refine ⟨12475433400579467580219983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316955600386311720146655 12475433400579467580219983)
    ·
      refine ⟨18713150100869201370329975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475433400579467580219983 18713150100869201370329975)
      ·
        refine ⟨28069725151303802055494963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18713150100869201370329975 28069725151303802055494963)
        ·
          refine ⟨42104587726955703083242445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28069725151303802055494963 42104587726955703083242445)
          ·
            refine ⟨15789220397608388656215917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42104587726955703083242445 15789220397608388656215917)
            ·
              refine ⟨5920957649103145746080969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15789220397608388656215917 5920957649103145746080969)
              ·
                refine ⟨4440718236827359309560727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5920957649103145746080969 4440718236827359309560727)
                ·
                  refine ⟨6661077355241038964341091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440718236827359309560727 6661077355241038964341091)
                  ·
                    refine ⟨9991616032861558446511637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661077355241038964341091 9991616032861558446511637)
                    ·
                      refine ⟨468357001540385552180233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9991616032861558446511637 468357001540385552180233)
                      ·
                        rfl

theorem cell23_912122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_912122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912122 prefixEnd_912122 := by exact prefixLift 912122
  have htrace : WordTrace (prefixWord ++ tailWord_912122) baseStart_912122 baseEnd_912122 := by
    simpa [prefixWord, tailWord_912122, baseEnd_912122] using wordTrace_append hprefix tailTrace_912122
  have hstable : (prefixWord ++ tailWord_912122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912122).length < 2 ^ (prefixWord ++ tailWord_912122).sum := by decide
  have hdescent : baseEnd_912122 < baseStart_912122 := by decide
  rcases family_descends (prefixWord ++ tailWord_912122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912129 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_912129 : Nat := 118140960795 + 912129 * 2 ^ 59
def prefixEnd_912129 : Nat := 4983230072969 + 3 ^ 40 * 912129 * 2
def baseEnd_912129 : Nat := 468360595904967024792701

theorem tailTrace_912129 : CollatzResearch.WordTrace tailWord_912129 prefixEnd_912129 468360595904967024792701 := by
  unfold tailWord_912129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33268077712519887076091441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22178718475013258050727627 33268077712519887076091441)
  ·
    refine ⟨24951058284389915307068581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33268077712519887076091441 24951058284389915307068581)
    ·
      refine ⟨4678323428323109120075359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24951058284389915307068581 4678323428323109120075359)
      ·
        refine ⟨7017485142484663680113039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678323428323109120075359 7017485142484663680113039)
        ·
          refine ⟨10526227713726995520169559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017485142484663680113039 10526227713726995520169559)
          ·
            refine ⟨15789341570590493280254339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10526227713726995520169559 15789341570590493280254339)
            ·
              refine ⟨23684012355885739920381509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789341570590493280254339 23684012355885739920381509)
              ·
                refine ⟨4440752316728576235071533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23684012355885739920381509 4440752316728576235071533)
                ·
                  refine ⟨1665282118773216088151825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4440752316728576235071533 1665282118773216088151825)
                  ·
                    refine ⟨1248961589079912066113869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665282118773216088151825 1248961589079912066113869)
                    ·
                      refine ⟨468360595904967024792701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1248961589079912066113869 468360595904967024792701)
                      ·
                        rfl

theorem cell23_912129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_912129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912129 prefixEnd_912129 := by exact prefixLift 912129
  have htrace : WordTrace (prefixWord ++ tailWord_912129) baseStart_912129 baseEnd_912129 := by
    simpa [prefixWord, tailWord_912129, baseEnd_912129] using wordTrace_append hprefix tailTrace_912129
  have hstable : (prefixWord ++ tailWord_912129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912129).length < 2 ^ (prefixWord ++ tailWord_912129).sum := by decide
  have hdescent : baseEnd_912129 < baseStart_912129 := by decide
  rcases family_descends (prefixWord ++ tailWord_912129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912136 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_912136 : Nat := 118140960795 + 912136 * 2 ^ 59
def prefixEnd_912136 : Nat := 4983230072969 + 3 ^ 40 * 912136 * 2
def baseEnd_912136 : Nat := 156121396756516165801723

theorem tailTrace_912136 : CollatzResearch.WordTrace tailWord_912136 prefixEnd_912136 156121396756516165801723 := by
  unfold tailWord_912136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634166511747263635798131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22178888682329684847730841 16634166511747263635798131)
  ·
    refine ⟨24951249767620895453697197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634166511747263635798131 24951249767620895453697197)
    ·
      refine ⟨9356718662857835795136449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24951249767620895453697197 9356718662857835795136449)
      ·
        refine ⟨7017538997143376846352337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9356718662857835795136449 7017538997143376846352337)
        ·
          refine ⟨5263154247857532634764253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7017538997143376846352337 5263154247857532634764253)
          ·
            refine ⟨1973682842946574738036595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5263154247857532634764253 1973682842946574738036595)
            ·
              refine ⟨2960524264419862107054893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973682842946574738036595 2960524264419862107054893)
              ·
                refine ⟨1110196599157448290145585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960524264419862107054893 1110196599157448290145585)
                ·
                  refine ⟨832647449368086217609189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110196599157448290145585 832647449368086217609189)
                  ·
                    refine ⟨156121396756516165801723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832647449368086217609189 156121396756516165801723)
                    ·
                      rfl

theorem cell23_912136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_912136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912136 prefixEnd_912136 := by exact prefixLift 912136
  have htrace : WordTrace (prefixWord ++ tailWord_912136) baseStart_912136 baseEnd_912136 := by
    simpa [prefixWord, tailWord_912136, baseEnd_912136] using wordTrace_append hprefix tailTrace_912136
  have hstable : (prefixWord ++ tailWord_912136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912136).length < 2 ^ (prefixWord ++ tailWord_912136).sum := by decide
  have hdescent : baseEnd_912136 < baseStart_912136 := by decide
  rcases family_descends (prefixWord ++ tailWord_912136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912159 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_912159 : Nat := 118140960795 + 912159 * 2 ^ 59
def prefixEnd_912159 : Nat := 4983230072969 + 3 ^ 40 * 912159 * 2
def baseEnd_912159 : Nat := 468376000324601907417563

theorem tailTrace_912159 : CollatzResearch.WordTrace tailWord_912159 prefixEnd_912159 468376000324601907417563 := by
  unfold tailWord_912159
  simp only [CollatzResearch.WordTrace]
  refine ⟨33269171902411202199683531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22179447934940801466455687 33269171902411202199683531)
  ·
    refine ⟨49903757853616803299525297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33269171902411202199683531 49903757853616803299525297)
    ·
      refine ⟨37427818390212602474643973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49903757853616803299525297 37427818390212602474643973)
      ·
        refine ⟨7017715948164862963995745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37427818390212602474643973 7017715948164862963995745)
        ·
          refine ⟨5263286961123647222996809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7017715948164862963995745 5263286961123647222996809)
          ·
            refine ⟨3947465220842735417247607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263286961123647222996809 3947465220842735417247607)
            ·
              refine ⟨5921197831264103125871411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947465220842735417247607 5921197831264103125871411)
              ·
                refine ⟨8881796746896154688807117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921197831264103125871411 8881796746896154688807117)
                ·
                  refine ⟨3330673780086058008302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8881796746896154688807117 3330673780086058008302669)
                  ·
                    refine ⟨1249002667532271753113501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330673780086058008302669 1249002667532271753113501)
                    ·
                      refine ⟨468376000324601907417563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1249002667532271753113501 468376000324601907417563)
                      ·
                        rfl

theorem cell23_912159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_912159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912159 prefixEnd_912159 := by exact prefixLift 912159
  have htrace : WordTrace (prefixWord ++ tailWord_912159) baseStart_912159 baseEnd_912159 := by
    simpa [prefixWord, tailWord_912159, baseEnd_912159] using wordTrace_append hprefix tailTrace_912159
  have hstable : (prefixWord ++ tailWord_912159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912159).length < 2 ^ (prefixWord ++ tailWord_912159).sum := by decide
  have hdescent : baseEnd_912159 < baseStart_912159 := by decide
  rcases family_descends (prefixWord ++ tailWord_912159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912170 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_912170 : Nat := 118140960795 + 912170 * 2 ^ 59
def prefixEnd_912170 : Nat := 4983230072969 + 3 ^ 40 * 912170 * 2
def baseEnd_912170 : Nat := 156127216203933788126671

theorem tailTrace_912170 : CollatzResearch.WordTrace tailWord_912170 prefixEnd_912170 156127216203933788126671 := by
  unfold tailWord_912170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317393276342837769583491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22179715403580900718889309 8317393276342837769583491)
  ·
    refine ⟨12476089914514256654375237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317393276342837769583491 12476089914514256654375237)
    ·
      refine ⟨2339266858971423122695357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12476089914514256654375237 2339266858971423122695357)
      ·
        refine ⟨877225072114283671010759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2339266858971423122695357 877225072114283671010759)
        ·
          refine ⟨1315837608171425506516139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877225072114283671010759 1315837608171425506516139)
          ·
            refine ⟨1973756412257138259774209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315837608171425506516139 1973756412257138259774209)
            ·
              refine ⟨1480317309192853694830657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973756412257138259774209 1480317309192853694830657)
              ·
                refine ⟨1110237981894640271122993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480317309192853694830657 1110237981894640271122993)
                ·
                  refine ⟨832678486420980203342245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110237981894640271122993 832678486420980203342245)
                  ·
                    refine ⟨156127216203933788126671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832678486420980203342245 156127216203933788126671)
                    ·
                      rfl

theorem cell23_912170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_912170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912170 prefixEnd_912170 := by exact prefixLift 912170
  have htrace : WordTrace (prefixWord ++ tailWord_912170) baseStart_912170 baseEnd_912170 := by
    simpa [prefixWord, tailWord_912170, baseEnd_912170] using wordTrace_append hprefix tailTrace_912170
  have hstable : (prefixWord ++ tailWord_912170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912170).length < 2 ^ (prefixWord ++ tailWord_912170).sum := by decide
  have hdescent : baseEnd_912170 < baseStart_912170 := by decide
  rcases family_descends (prefixWord ++ tailWord_912170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912220 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_912220 : Nat := 118140960795 + 912220 * 2 ^ 59
def prefixEnd_912220 : Nat := 4983230072969 + 3 ^ 40 * 912220 * 2
def baseEnd_912220 : Nat := 468407322644526168754783

theorem tailTrace_912220 : CollatzResearch.WordTrace tailWord_912220 prefixEnd_912220 468407322644526168754783 := by
  unfold tailWord_912220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16635698377595104808827057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22180931170126806411769409 16635698377595104808827057)
  ·
    refine ⟨12476773783196328606620293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16635698377595104808827057 12476773783196328606620293)
    ·
      refine ⟨2339395084349311613741305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12476773783196328606620293 2339395084349311613741305)
      ·
        refine ⟨1754546313261983710305979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339395084349311613741305 1754546313261983710305979)
        ·
          refine ⟨2631819469892975565458969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754546313261983710305979 2631819469892975565458969)
          ·
            refine ⟨1973864602419731674094227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631819469892975565458969 1973864602419731674094227)
            ·
              refine ⟨2960796903629597511141341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973864602419731674094227 2960796903629597511141341)
              ·
                refine ⟨1110298838861099066678003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960796903629597511141341 1110298838861099066678003)
                ·
                  refine ⟨1665448258291648600017005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110298838861099066678003 1665448258291648600017005)
                  ·
                    refine ⟨624543096859368225006377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665448258291648600017005 624543096859368225006377)
                    ·
                      refine ⟨468407322644526168754783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624543096859368225006377 468407322644526168754783)
                      ·
                        rfl

theorem cell23_912220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_912220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912220 prefixEnd_912220 := by exact prefixLift 912220
  have htrace : WordTrace (prefixWord ++ tailWord_912220) baseStart_912220 baseEnd_912220 := by
    simpa [prefixWord, tailWord_912220, baseEnd_912220] using wordTrace_append hprefix tailTrace_912220
  have hstable : (prefixWord ++ tailWord_912220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912220).length < 2 ^ (prefixWord ++ tailWord_912220).sum := by decide
  have hdescent : baseEnd_912220 < baseStart_912220 := by decide
  rcases family_descends (prefixWord ++ tailWord_912220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912229 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_912229 : Nat := 118140960795 + 912229 * 2 ^ 59
def prefixEnd_912229 : Nat := 4983230072969 + 3 ^ 40 * 912229 * 2
def baseEnd_912229 : Nat := 468411943970416633542241

theorem tailTrace_912229 : CollatzResearch.WordTrace tailWord_912229 prefixEnd_912229 468411943970416633542241 := by
  unfold tailWord_912229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271725012157604154731741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22181150008105069436487827 33271725012157604154731741)
  ·
    refine ⟨12476896879559101558024403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33271725012157604154731741 12476896879559101558024403)
    ·
      refine ⟨18715345319338652337036605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476896879559101558024403 18715345319338652337036605)
      ·
        refine ⟨7018254494751994626388727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18715345319338652337036605 7018254494751994626388727)
        ·
          refine ⟨10527381742127991939583091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018254494751994626388727 10527381742127991939583091)
          ·
            refine ⟨15791072613191987909374637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527381742127991939583091 15791072613191987909374637)
            ·
              refine ⟨5921652229946995466015489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15791072613191987909374637 5921652229946995466015489)
              ·
                refine ⟨4441239172460246599511617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921652229946995466015489 4441239172460246599511617)
                ·
                  refine ⟨3330929379345184949633713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441239172460246599511617 3330929379345184949633713)
                  ·
                    refine ⟨2498197034508888712225285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330929379345184949633713 2498197034508888712225285)
                    ·
                      refine ⟨468411943970416633542241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2498197034508888712225285 468411943970416633542241)
                      ·
                        rfl

theorem cell23_912229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_912229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912229 prefixEnd_912229 := by exact prefixLift 912229
  have htrace : WordTrace (prefixWord ++ tailWord_912229) baseStart_912229 baseEnd_912229 := by
    simpa [prefixWord, tailWord_912229, baseEnd_912229] using wordTrace_append hprefix tailTrace_912229
  have hstable : (prefixWord ++ tailWord_912229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912229).length < 2 ^ (prefixWord ++ tailWord_912229).sum := by decide
  have hdescent : baseEnd_912229 < baseStart_912229 := by decide
  rcases family_descends (prefixWord ++ tailWord_912229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912279 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_912279 : Nat := 118140960795 + 912279 * 2 ^ 59
def prefixEnd_912279 : Nat := 4983230072969 + 3 ^ 40 * 912279 * 2
def baseEnd_912279 : Nat := 468437618003141437917011

theorem tailTrace_912279 : CollatzResearch.WordTrace tailWord_912279 prefixEnd_912279 468437618003141437917011 := by
  unfold tailWord_912279
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273548661976462694051891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22182365774650975129367927 33273548661976462694051891)
  ·
    refine ⟨49910322992964694041077837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33273548661976462694051891 49910322992964694041077837)
    ·
      refine ⟨18716371122361760265404189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49910322992964694041077837 18716371122361760265404189)
      ·
        refine ⟨7018639170885660099526571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18716371122361760265404189 7018639170885660099526571)
        ·
          refine ⟨10527958756328490149289857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018639170885660099526571 10527958756328490149289857)
          ·
            refine ⟨7895969067246367611967393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10527958756328490149289857 7895969067246367611967393)
            ·
              refine ⟨5921976800434775708975545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895969067246367611967393 5921976800434775708975545)
              ·
                refine ⟨4441482600326081781731659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921976800434775708975545 4441482600326081781731659)
                ·
                  refine ⟨6662223900489122672597489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441482600326081781731659 6662223900489122672597489)
                  ·
                    refine ⟨4996667925366842004448117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6662223900489122672597489 4996667925366842004448117)
                    ·
                      refine ⟨468437618003141437917011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4996667925366842004448117 468437618003141437917011)
                      ·
                        rfl

theorem cell23_912279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_912279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912279 prefixEnd_912279 := by exact prefixLift 912279
  have htrace : WordTrace (prefixWord ++ tailWord_912279) baseStart_912279 baseEnd_912279 := by
    simpa [prefixWord, tailWord_912279, baseEnd_912279] using wordTrace_append hprefix tailTrace_912279
  have hstable : (prefixWord ++ tailWord_912279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912279).length < 2 ^ (prefixWord ++ tailWord_912279).sum := by decide
  have hdescent : baseEnd_912279 < baseStart_912279 := by decide
  rcases family_descends (prefixWord ++ tailWord_912279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912290 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_912290 : Nat := 118140960795 + 912290 * 2 ^ 59
def prefixEnd_912290 : Nat := 4983230072969 + 3 ^ 40 * 912290 * 2
def baseEnd_912290 : Nat := 52049251810037877208829

theorem tailTrace_912290 : CollatzResearch.WordTrace tailWord_912290 prefixEnd_912290 52049251810037877208829 := by
  unfold tailWord_912290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318487466234152893175581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22182633243291074381801549 8318487466234152893175581)
  ·
    refine ⟨3119432799837807334940843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8318487466234152893175581 3119432799837807334940843)
    ·
      refine ⟨4679149199756711002411265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119432799837807334940843 4679149199756711002411265)
      ·
        refine ⟨3509361899817533251808449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4679149199756711002411265 3509361899817533251808449)
        ·
          refine ⟨2632021424863149938856337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509361899817533251808449 2632021424863149938856337)
          ·
            refine ⟨1974016068647362454142253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632021424863149938856337 1974016068647362454142253)
            ·
              refine ⟨740256025742760920303345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974016068647362454142253 740256025742760920303345)
              ·
                refine ⟨555192019307070690227509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740256025742760920303345 555192019307070690227509)
                ·
                  refine ⟨52049251810037877208829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555192019307070690227509 52049251810037877208829)
                  ·
                    rfl

theorem cell23_912290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_912290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912290 prefixEnd_912290 := by exact prefixLift 912290
  have htrace : WordTrace (prefixWord ++ tailWord_912290) baseStart_912290 baseEnd_912290 := by
    simpa [prefixWord, tailWord_912290, baseEnd_912290] using wordTrace_append hprefix tailTrace_912290
  have hstable : (prefixWord ++ tailWord_912290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912290).length < 2 ^ (prefixWord ++ tailWord_912290).sum := by decide
  have hdescent : baseEnd_912290 < baseStart_912290 := by decide
  rcases family_descends (prefixWord ++ tailWord_912290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912301 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_912301 : Nat := 118140960795 + 912301 * 2 ^ 59
def prefixEnd_912301 : Nat := 4983230072969 + 3 ^ 40 * 912301 * 2
def baseEnd_912301 : Nat := 468448914577540351841911

theorem tailTrace_912301 : CollatzResearch.WordTrace tailWord_912301 prefixEnd_912301 468448914577540351841911 := by
  unfold tailWord_912301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274351067896760451352757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22182900711931173634235171 33274351067896760451352757)
  ·
    refine ⟨3119470412615321292314321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33274351067896760451352757 3119470412615321292314321)
    ·
      refine ⟨2339602809461490969235741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119470412615321292314321 2339602809461490969235741)
      ·
        refine ⟨877351053548059113463403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2339602809461490969235741 877351053548059113463403)
        ·
          refine ⟨1316026580322088670195105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877351053548059113463403 1316026580322088670195105)
          ·
            refine ⟨987019935241566502646329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316026580322088670195105 987019935241566502646329)
            ·
              refine ⟨740264951431174876984747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987019935241566502646329 740264951431174876984747)
              ·
                refine ⟨1110397427146762315477121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740264951431174876984747 1110397427146762315477121)
                ·
                  refine ⟨832798070360071736607841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110397427146762315477121 832798070360071736607841)
                  ·
                    refine ⟨624598552770053802455881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 832798070360071736607841 624598552770053802455881)
                    ·
                      refine ⟨468448914577540351841911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624598552770053802455881 468448914577540351841911)
                      ·
                        rfl

theorem cell23_912301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_912301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912301 prefixEnd_912301 := by exact prefixLift 912301
  have htrace : WordTrace (prefixWord ++ tailWord_912301) baseStart_912301 baseEnd_912301 := by
    simpa [prefixWord, tailWord_912301, baseEnd_912301] using wordTrace_append hprefix tailTrace_912301
  have hstable : (prefixWord ++ tailWord_912301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912301).length < 2 ^ (prefixWord ++ tailWord_912301).sum := by decide
  have hdescent : baseEnd_912301 < baseStart_912301 := by decide
  rcases family_descends (prefixWord ++ tailWord_912301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912346 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_912346 : Nat := 118140960795 + 912346 * 2 ^ 59
def prefixEnd_912346 : Nat := 4983230072969 + 3 ^ 40 * 912346 * 2
def baseEnd_912346 : Nat := 52052446800776963975467

theorem tailTrace_912346 : CollatzResearch.WordTrace tailWord_912346 prefixEnd_912346 52052446800776963975467 := by
  unfold tailWord_912346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318998088183433284185223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22183994901822488757827261 8318998088183433284185223)
  ·
    refine ⟨12478497132275149926277835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8318998088183433284185223 12478497132275149926277835)
    ·
      refine ⟨18717745698412724889416753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12478497132275149926277835 18717745698412724889416753)
      ·
        refine ⟨14038309273809543667062565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18717745698412724889416753 14038309273809543667062565)
        ·
          refine ⟨2632182988839289437574231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14038309273809543667062565 2632182988839289437574231)
          ·
            refine ⟨3948274483258934156361347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632182988839289437574231 3948274483258934156361347)
            ·
              refine ⟨5922411724888401234542021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948274483258934156361347 5922411724888401234542021)
              ·
                refine ⟨1110452198416575231476629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5922411724888401234542021 1110452198416575231476629)
                ·
                  refine ⟨52052446800776963975467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1110452198416575231476629 52052446800776963975467)
                  ·
                    rfl

theorem cell23_912346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_912346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912346 prefixEnd_912346 := by exact prefixLift 912346
  have htrace : WordTrace (prefixWord ++ tailWord_912346) baseStart_912346 baseEnd_912346 := by
    simpa [prefixWord, tailWord_912346, baseEnd_912346] using wordTrace_append hprefix tailTrace_912346
  have hstable : (prefixWord ++ tailWord_912346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912346).length < 2 ^ (prefixWord ++ tailWord_912346).sum := by decide
  have hdescent : baseEnd_912346 < baseStart_912346 := by decide
  rcases family_descends (prefixWord ++ tailWord_912346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912376 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_912376 : Nat := 118140960795 + 912376 * 2 ^ 59
def prefixEnd_912376 : Nat := 4983230072969 + 3 ^ 40 * 912376 * 2
def baseEnd_912376 : Nat := 156162475208875852801355

theorem tailTrace_912376 : CollatzResearch.WordTrace tailWord_912376 prefixEnd_912376 156162475208875852801355 := by
  unfold tailWord_912376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16638543271312524130166491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22184724361750032173555321 16638543271312524130166491)
  ·
    refine ⟨24957814906968786195249737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16638543271312524130166491 24957814906968786195249737)
    ·
      refine ⟨18718361180226589646437303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24957814906968786195249737 18718361180226589646437303)
      ·
        refine ⟨28077541770339884469655955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718361180226589646437303 28077541770339884469655955)
        ·
          refine ⟨42116312655509826704483933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28077541770339884469655955 42116312655509826704483933)
          ·
            refine ⟨15793617245816185014181475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42116312655509826704483933 15793617245816185014181475)
            ·
              refine ⟨23690425868724277521272213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15793617245816185014181475 23690425868724277521272213)
              ·
                refine ⟨1110488712596450508809635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23690425868724277521272213 1110488712596450508809635)
                ·
                  refine ⟨1665733068894675763214453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110488712596450508809635 1665733068894675763214453)
                  ·
                    refine ⟨156162475208875852801355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1665733068894675763214453 156162475208875852801355)
                    ·
                      rfl

theorem cell23_912376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_912376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912376 prefixEnd_912376 := by exact prefixLift 912376
  have htrace : WordTrace (prefixWord ++ tailWord_912376) baseStart_912376 baseEnd_912376 := by
    simpa [prefixWord, tailWord_912376, baseEnd_912376] using wordTrace_append hprefix tailTrace_912376
  have hstable : (prefixWord ++ tailWord_912376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912376).length < 2 ^ (prefixWord ++ tailWord_912376).sum := by decide
  have hdescent : baseEnd_912376 < baseStart_912376 := by decide
  rcases family_descends (prefixWord ++ tailWord_912376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912407 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_912407 : Nat := 118140960795 + 912407 * 2 ^ 59
def prefixEnd_912407 : Nat := 4983230072969 + 3 ^ 40 * 912407 * 2
def baseEnd_912407 : Nat := 468503343526916937116423

theorem tailTrace_912407 : CollatzResearch.WordTrace tailWord_912407 prefixEnd_912407 468503343526916937116423 := by
  unfold tailWord_912407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33278217205512740554711475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22185478137008493703140983 33278217205512740554711475)
  ·
    refine ⟨49917325808269110832067213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33278217205512740554711475 49917325808269110832067213)
    ·
      refine ⟨18718997178100916562025205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49917325808269110832067213 18718997178100916562025205)
      ·
        refine ⟨1754905985446960927689863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18718997178100916562025205 1754905985446960927689863)
        ·
          refine ⟨2632358978170441391534795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754905985446960927689863 2632358978170441391534795)
          ·
            refine ⟨3948538467255662087302193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632358978170441391534795 3948538467255662087302193)
            ·
              refine ⟨2961403850441746565476645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948538467255662087302193 2961403850441746565476645)
              ·
                refine ⟨555263221957827481026871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961403850441746565476645 555263221957827481026871)
                ·
                  refine ⟨832894832936741221540307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555263221957827481026871 832894832936741221540307)
                  ·
                    refine ⟨1249342249405111832310461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832894832936741221540307 1249342249405111832310461)
                    ·
                      refine ⟨468503343526916937116423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1249342249405111832310461 468503343526916937116423)
                      ·
                        rfl

theorem cell23_912407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_912407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912407 prefixEnd_912407 := by exact prefixLift 912407
  have htrace : WordTrace (prefixWord ++ tailWord_912407) baseStart_912407 baseEnd_912407 := by
    simpa [prefixWord, tailWord_912407, baseEnd_912407] using wordTrace_append hprefix tailTrace_912407
  have hstable : (prefixWord ++ tailWord_912407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912407).length < 2 ^ (prefixWord ++ tailWord_912407).sum := by decide
  have hdescent : baseEnd_912407 < baseStart_912407 := by decide
  rcases family_descends (prefixWord ++ tailWord_912407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912430 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_912430 : Nat := 118140960795 + 912430 * 2 ^ 59
def prefixEnd_912430 : Nat := 4983230072969 + 3 ^ 40 * 912430 * 2
def baseEnd_912430 : Nat := 468515153581970347128817

theorem tailTrace_912430 : CollatzResearch.WordTrace tailWord_912430 prefixEnd_912430 468515153581970347128817 := by
  unfold tailWord_912430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159882010553676935349843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22186037389619610321865829 4159882010553676935349843)
  ·
    refine ⟨6239823015830515403024765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4159882010553676935349843 6239823015830515403024765)
    ·
      refine ⟨2339933630936443276134287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6239823015830515403024765 2339933630936443276134287)
      ·
        refine ⟨3509900446404664914201431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339933630936443276134287 3509900446404664914201431)
        ·
          refine ⟨5264850669606997371302147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509900446404664914201431 5264850669606997371302147)
          ·
            refine ⟨7897276004410496056953221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264850669606997371302147 7897276004410496056953221)
            ·
              refine ⟨1480739250826968010678729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7897276004410496056953221 1480739250826968010678729)
              ·
                refine ⟨1110554438120226008009047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480739250826968010678729 1110554438120226008009047)
                ·
                  refine ⟨1665831657180339012013571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110554438120226008009047 1665831657180339012013571)
                  ·
                    refine ⟨2498747485770508518020357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1665831657180339012013571 2498747485770508518020357)
                    ·
                      refine ⟨468515153581970347128817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2498747485770508518020357 468515153581970347128817)
                      ·
                        rfl

theorem cell23_912430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_912430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912430 prefixEnd_912430 := by exact prefixLift 912430
  have htrace : WordTrace (prefixWord ++ tailWord_912430) baseStart_912430 baseEnd_912430 := by
    simpa [prefixWord, tailWord_912430, baseEnd_912430] using wordTrace_append hprefix tailTrace_912430
  have hstable : (prefixWord ++ tailWord_912430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912430).length < 2 ^ (prefixWord ++ tailWord_912430).sum := by decide
  have hdescent : baseEnd_912430 < baseStart_912430 := by decide
  rcases family_descends (prefixWord ++ tailWord_912430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912480 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_912480 : Nat := 118140960795 + 912480 * 2 ^ 59
def prefixEnd_912480 : Nat := 4983230072969 + 3 ^ 40 * 912480 * 2
def baseEnd_912480 : Nat := 468540827614695151503587

theorem tailTrace_912480 : CollatzResearch.WordTrace tailWord_912480 prefixEnd_912480 468540827614695151503587 := by
  unfold tailWord_912480
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640439867124137011059447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22187253156165516014745929 16640439867124137011059447)
  ·
    refine ⟨24960659800686205516589171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640439867124137011059447 24960659800686205516589171)
    ·
      refine ⟨37440989701029308274883757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24960659800686205516589171 37440989701029308274883757)
      ·
        refine ⟨14040371137885990603081409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37440989701029308274883757 14040371137885990603081409)
        ·
          refine ⟨10530278353414492952311057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14040371137885990603081409 10530278353414492952311057)
          ·
            refine ⟨7897708765060869714233293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10530278353414492952311057 7897708765060869714233293)
            ·
              refine ⟨2961640786897826142837485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7897708765060869714233293 2961640786897826142837485)
              ·
                refine ⟨1110615295086684803564057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961640786897826142837485 1110615295086684803564057)
                ·
                  refine ⟨832961471315013602673043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110615295086684803564057 832961471315013602673043)
                  ·
                    refine ⟨1249442206972520404009565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832961471315013602673043 1249442206972520404009565)
                    ·
                      refine ⟨468540827614695151503587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1249442206972520404009565 468540827614695151503587)
                      ·
                        rfl

theorem cell23_912480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_912480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912480 prefixEnd_912480 := by exact prefixLift 912480
  have htrace : WordTrace (prefixWord ++ tailWord_912480) baseStart_912480 baseEnd_912480 := by
    simpa [prefixWord, tailWord_912480, baseEnd_912480] using wordTrace_append hprefix tailTrace_912480
  have hstable : (prefixWord ++ tailWord_912480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912480).length < 2 ^ (prefixWord ++ tailWord_912480).sum := by decide
  have hdescent : baseEnd_912480 < baseStart_912480 := by decide
  rcases family_descends (prefixWord ++ tailWord_912480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912573 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_912573 : Nat := 118140960795 + 912573 * 2 ^ 59
def prefixEnd_912573 : Nat := 4983230072969 + 3 ^ 40 * 912573 * 2
def baseEnd_912573 : Nat := 156196193771854429213553

theorem tailTrace_912573 : CollatzResearch.WordTrace tailWord_912573 prefixEnd_912573 156196193771854429213553 := by
  unfold tailWord_912573
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284271722911350905254373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22189514481940900603502915 33284271722911350905254373)
  ·
    refine ⟨6240800948045878294735195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33284271722911350905254373 6240800948045878294735195)
    ·
      refine ⟨9361201422068817442102793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240800948045878294735195 9361201422068817442102793)
      ·
        refine ⟨7020901066551613081577095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9361201422068817442102793 7020901066551613081577095)
        ·
          refine ⟨10531351599827419622365643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020901066551613081577095 10531351599827419622365643)
          ·
            refine ⟨15797027399741129433548465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531351599827419622365643 15797027399741129433548465)
            ·
              refine ⟨11847770549805847075161349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15797027399741129433548465 11847770549805847075161349)
              ·
                refine ⟨2221456978088596326592753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11847770549805847075161349 2221456978088596326592753)
                ·
                  refine ⟨1666092733566447244944565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221456978088596326592753 1666092733566447244944565)
                  ·
                    refine ⟨156196193771854429213553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1666092733566447244944565 156196193771854429213553)
                    ·
                      rfl

theorem cell23_912573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_912573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912573 prefixEnd_912573 := by exact prefixLift 912573
  have htrace : WordTrace (prefixWord ++ tailWord_912573) baseStart_912573 baseEnd_912573 := by
    simpa [prefixWord, tailWord_912573, baseEnd_912573] using wordTrace_append hprefix tailTrace_912573
  have hstable : (prefixWord ++ tailWord_912573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912573).length < 2 ^ (prefixWord ++ tailWord_912573).sum := by decide
  have hdescent : baseEnd_912573 < baseStart_912573 := by decide
  rcases family_descends (prefixWord ++ tailWord_912573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912577 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 5]
def baseStart_912577 : Nat := 118140960795 + 912577 * 2 ^ 59
def prefixEnd_912577 : Nat := 4983230072969 + 3 ^ 40 * 912577 * 2
def baseEnd_912577 : Nat := 52065626137575696887849

theorem tailTrace_912577 : CollatzResearch.WordTrace tailWord_912577 prefixEnd_912577 52065626137575696887849 := by
  unfold tailWord_912577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284417614896859588399985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22189611743264573058933323 33284417614896859588399985)
  ·
    refine ⟨24963313211172644691299989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33284417614896859588399985 24963313211172644691299989)
    ·
      refine ⟨1170155306773717719904687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24963313211172644691299989 1170155306773717719904687)
      ·
        refine ⟨1755232960160576579857031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170155306773717719904687 1755232960160576579857031)
        ·
          refine ⟨2632849440240864869785547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755232960160576579857031 2632849440240864869785547)
          ·
            refine ⟨3949274160361297304678321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632849440240864869785547 3949274160361297304678321)
            ·
              refine ⟨2961955620270972978508741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949274160361297304678321 2961955620270972978508741)
              ·
                refine ⟨555366678800807433470389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961955620270972978508741 555366678800807433470389)
                ·
                  refine ⟨52065626137575696887849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555366678800807433470389 52065626137575696887849)
                  ·
                    rfl

theorem cell23_912577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 5].length) (baseStart_912577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912577 prefixEnd_912577 := by exact prefixLift 912577
  have htrace : WordTrace (prefixWord ++ tailWord_912577) baseStart_912577 baseEnd_912577 := by
    simpa [prefixWord, tailWord_912577, baseEnd_912577] using wordTrace_append hprefix tailTrace_912577
  have hstable : (prefixWord ++ tailWord_912577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912577).length < 2 ^ (prefixWord ++ tailWord_912577).sum := by decide
  have hdescent : baseEnd_912577 < baseStart_912577 := by decide
  rcases family_descends (prefixWord ++ tailWord_912577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912628 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 5]
def baseStart_912628 : Nat := 118140960795 + 912628 * 2 ^ 59
def prefixEnd_912628 : Nat := 4983230072969 + 3 ^ 40 * 912628 * 2
def baseEnd_912628 : Nat := 52068535861284508050323

theorem tailTrace_912628 : CollatzResearch.WordTrace tailWord_912628 prefixEnd_912628 52068535861284508050323 := by
  unfold tailWord_912628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643138868856047649253269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22190851825141396865671025 16643138868856047649253269)
  ·
    refine ⟨780147134477627233558747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16643138868856047649253269 780147134477627233558747)
    ·
      refine ⟨1170220701716440850338121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780147134477627233558747 1170220701716440850338121)
      ·
        refine ⟨877665526287330637753591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170220701716440850338121 877665526287330637753591)
        ·
          refine ⟨1316498289430995956630387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877665526287330637753591 1316498289430995956630387)
          ·
            refine ⟨1974747434146493934945581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316498289430995956630387 1974747434146493934945581)
            ·
              refine ⟨740530287804935225604593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974747434146493934945581 740530287804935225604593)
              ·
                refine ⟨555397715853701419203445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740530287804935225604593 555397715853701419203445)
                ·
                  refine ⟨52068535861284508050323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555397715853701419203445 52068535861284508050323)
                  ·
                    rfl

theorem cell23_912628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_912628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912628 prefixEnd_912628 := by exact prefixLift 912628
  have htrace : WordTrace (prefixWord ++ tailWord_912628) baseStart_912628 baseEnd_912628 := by
    simpa [prefixWord, tailWord_912628, baseEnd_912628] using wordTrace_append hprefix tailTrace_912628
  have hstable : (prefixWord ++ tailWord_912628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912628).length < 2 ^ (prefixWord ++ tailWord_912628).sum := by decide
  have hdescent : baseEnd_912628 < baseStart_912628 := by decide
  rcases family_descends (prefixWord ++ tailWord_912628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912633 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 6]
def baseStart_912633 : Nat := 118140960795 + 912633 * 2 ^ 59
def prefixEnd_912633 : Nat := 4983230072969 + 3 ^ 40 * 912633 * 2
def baseEnd_912633 : Nat := 52068821128314783654487

theorem tailTrace_912633 : CollatzResearch.WordTrace tailWord_912633 prefixEnd_912633 52068821128314783654487 := by
  unfold tailWord_912633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33286460102693981152438553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22190973401795987434959035 33286460102693981152438553)
  ·
    refine ⟨24964845077020485864328915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33286460102693981152438553 24964845077020485864328915)
    ·
      refine ⟨37447267615530728796493373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24964845077020485864328915 37447267615530728796493373)
      ·
        refine ⟨14042725355824023298685015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37447267615530728796493373 14042725355824023298685015)
        ·
          refine ⟨21064088033736034948027523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14042725355824023298685015 21064088033736034948027523)
          ·
            refine ⟨31596132050604052422041285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064088033736034948027523 31596132050604052422041285)
            ·
              refine ⟨5924274759488259829132741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31596132050604052422041285 5924274759488259829132741)
              ·
                refine ⟨1110801517404048717962389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5924274759488259829132741 1110801517404048717962389)
                ·
                  refine ⟨52068821128314783654487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1110801517404048717962389 52068821128314783654487)
                  ·
                    rfl

theorem cell23_912633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_912633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912633 prefixEnd_912633 := by exact prefixLift 912633
  have htrace : WordTrace (prefixWord ++ tailWord_912633) baseStart_912633 baseEnd_912633 := by
    simpa [prefixWord, tailWord_912633, baseEnd_912633] using wordTrace_append hprefix tailTrace_912633
  have hstable : (prefixWord ++ tailWord_912633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912633).length < 2 ^ (prefixWord ++ tailWord_912633).sum := by decide
  have hdescent : baseEnd_912633 < baseStart_912633 := by decide
  rcases family_descends (prefixWord ++ tailWord_912633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912700 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_912700 : Nat := 118140960795 + 912700 * 2 ^ 59
def prefixEnd_912700 : Nat := 4983230072969 + 3 ^ 40 * 912700 * 2
def baseEnd_912700 : Nat := 468653793358684290752575

theorem tailTrace_912700 : CollatzResearch.WordTrace tailWord_912700 prefixEnd_912700 468653793358684290752575 := by
  unfold tailWord_912700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644451896725625797563777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22192602528967501063418369 16644451896725625797563777)
  ·
    refine ⟨12483338922544219348172833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16644451896725625797563777 12483338922544219348172833)
    ·
      refine ⟨9362504191908164511129625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12483338922544219348172833 9362504191908164511129625)
      ·
        refine ⟨7021878143931123383347219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9362504191908164511129625 7021878143931123383347219)
        ·
          refine ⟨10532817215896685075020829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021878143931123383347219 10532817215896685075020829)
          ·
            refine ⟨3949806455961256903132811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10532817215896685075020829 3949806455961256903132811)
            ·
              refine ⟨5924709683941885354699217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949806455961256903132811 5924709683941885354699217)
              ·
                refine ⟨4443532262956414016024413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924709683941885354699217 4443532262956414016024413)
                ·
                  refine ⟨1666324598608655256009155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4443532262956414016024413 1666324598608655256009155)
                  ·
                    refine ⟨2499486897912982884013733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1666324598608655256009155 2499486897912982884013733)
                    ·
                      refine ⟨468653793358684290752575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2499486897912982884013733 468653793358684290752575)
                      ·
                        rfl

theorem cell23_912700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_912700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912700 prefixEnd_912700 := by exact prefixLift 912700
  have htrace : WordTrace (prefixWord ++ tailWord_912700) baseStart_912700 baseEnd_912700 := by
    simpa [prefixWord, tailWord_912700, baseEnd_912700] using wordTrace_append hprefix tailTrace_912700
  have hstable : (prefixWord ++ tailWord_912700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912700).length < 2 ^ (prefixWord ++ tailWord_912700).sum := by decide
  have hdescent : baseEnd_912700 < baseStart_912700 := by decide
  rcases family_descends (prefixWord ++ tailWord_912700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912713 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_912713 : Nat := 118140960795 + 912713 * 2 ^ 59
def prefixEnd_912713 : Nat := 4983230072969 + 3 ^ 40 * 912713 * 2
def baseEnd_912713 : Nat := 468660468607192739890015

theorem tailTrace_912713 : CollatzResearch.WordTrace tailWord_912713 prefixEnd_912713 468660468607192739890015 := by
  unfold tailWord_912713
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289377942404154815350793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22192918628269436543567195 33289377942404154815350793)
  ·
    refine ⟨24967033456803116111513095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33289377942404154815350793 24967033456803116111513095)
    ·
      refine ⟨37450550185204674167269643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24967033456803116111513095 37450550185204674167269643)
      ·
        refine ⟨56175825277807011250904465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37450550185204674167269643 56175825277807011250904465)
        ·
          refine ⟨42131868958355258438178349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56175825277807011250904465 42131868958355258438178349)
          ·
            refine ⟨15799450859383221914316881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42131868958355258438178349 15799450859383221914316881)
            ·
              refine ⟨11849588144537416435737661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15799450859383221914316881 11849588144537416435737661)
              ·
                refine ⟨4443595554201531163401623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849588144537416435737661 4443595554201531163401623)
                ·
                  refine ⟨6665393331302296745102435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443595554201531163401623 6665393331302296745102435)
                  ·
                    refine ⟨9998089996953445117653653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665393331302296745102435 9998089996953445117653653)
                    ·
                      refine ⟨468660468607192739890015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9998089996953445117653653 468660468607192739890015)
                      ·
                        rfl

theorem cell23_912713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_912713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912713 prefixEnd_912713 := by exact prefixLift 912713
  have htrace : WordTrace (prefixWord ++ tailWord_912713) baseStart_912713 baseEnd_912713 := by
    simpa [prefixWord, tailWord_912713, baseEnd_912713] using wordTrace_append hprefix tailTrace_912713
  have hstable : (prefixWord ++ tailWord_912713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912713).length < 2 ^ (prefixWord ++ tailWord_912713).sum := by decide
  have hdescent : baseEnd_912713 < baseStart_912713 := by decide
  rcases family_descends (prefixWord ++ tailWord_912713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912720 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_912720 : Nat := 118140960795 + 912720 * 2 ^ 59
def prefixEnd_912720 : Nat := 4983230072969 + 3 ^ 40 * 912720 * 2
def baseEnd_912720 : Nat := 468664062971774212502483

theorem tailTrace_912720 : CollatzResearch.WordTrace tailWord_912720 prefixEnd_912720 468664062971774212502483 := by
  unfold tailWord_912720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644816626689397505427807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22193088835585863340570409 16644816626689397505427807)
  ·
    refine ⟨24967224940034096258141711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16644816626689397505427807 24967224940034096258141711)
    ·
      refine ⟨37450837410051144387212567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24967224940034096258141711 37450837410051144387212567)
      ·
        refine ⟨56176256115076716580818851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37450837410051144387212567 56176256115076716580818851)
        ·
          refine ⟨84264384172615074871228277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56176256115076716580818851 84264384172615074871228277)
          ·
            refine ⟨7899786016182663269177651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84264384172615074871228277 7899786016182663269177651)
            ·
              refine ⟨11849679024273994903766477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899786016182663269177651 11849679024273994903766477)
              ·
                refine ⟨4443629634102748088912429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849679024273994903766477 4443629634102748088912429)
                ·
                  refine ⟨1666361112788530533342161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4443629634102748088912429 1666361112788530533342161)
                  ·
                    refine ⟨1249770834591397900006621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666361112788530533342161 1249770834591397900006621)
                    ·
                      refine ⟨468664062971774212502483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1249770834591397900006621 468664062971774212502483)
                      ·
                        rfl

theorem cell23_912720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_912720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912720 prefixEnd_912720 := by exact prefixLift 912720
  have htrace : WordTrace (prefixWord ++ tailWord_912720) baseStart_912720 baseEnd_912720 := by
    simpa [prefixWord, tailWord_912720, baseEnd_912720] using wordTrace_append hprefix tailTrace_912720
  have hstable : (prefixWord ++ tailWord_912720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912720).length < 2 ^ (prefixWord ++ tailWord_912720).sum := by decide
  have hdescent : baseEnd_912720 < baseStart_912720 := by decide
  rcases family_descends (prefixWord ++ tailWord_912720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912730 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_912730 : Nat := 118140960795 + 912730 * 2 ^ 59
def prefixEnd_912730 : Nat := 4983230072969 + 3 ^ 40 * 912730 * 2
def baseEnd_912730 : Nat := 468669197778319173377437

theorem tailTrace_912730 : CollatzResearch.WordTrace tailWord_912730 prefixEnd_912730 468669197778319173377437 := by
  unfold tailWord_912730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322499495835641679679911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22193331988895044479146429 8322499495835641679679911)
  ·
    refine ⟨12483749243753462519519867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322499495835641679679911 12483749243753462519519867)
    ·
      refine ⟨18725623865630193779279801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483749243753462519519867 18725623865630193779279801)
      ·
        refine ⟨14044217899222645334459851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18725623865630193779279801 14044217899222645334459851)
        ·
          refine ⟨21066326848833968001689777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044217899222645334459851 21066326848833968001689777)
          ·
            refine ⟨15799745136625476001267333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21066326848833968001689777 15799745136625476001267333)
            ·
              refine ⟨2962452213117276750237625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15799745136625476001267333 2962452213117276750237625)
              ·
                refine ⟨2221839159837957562678219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962452213117276750237625 2221839159837957562678219)
                ·
                  refine ⟨3332758739756936344017329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221839159837957562678219 3332758739756936344017329)
                  ·
                    refine ⟨2499569054817702258012997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3332758739756936344017329 2499569054817702258012997)
                    ·
                      refine ⟨468669197778319173377437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2499569054817702258012997 468669197778319173377437)
                      ·
                        rfl

theorem cell23_912730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_912730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912730 prefixEnd_912730 := by exact prefixLift 912730
  have htrace : WordTrace (prefixWord ++ tailWord_912730) baseStart_912730 baseEnd_912730 := by
    simpa [prefixWord, tailWord_912730, baseEnd_912730] using wordTrace_append hprefix tailTrace_912730
  have hstable : (prefixWord ++ tailWord_912730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912730).length < 2 ^ (prefixWord ++ tailWord_912730).sum := by decide
  have hdescent : baseEnd_912730 < baseStart_912730 := by decide
  rcases family_descends (prefixWord ++ tailWord_912730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912753 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_912753 : Nat := 118140960795 + 912753 * 2 ^ 59
def prefixEnd_912753 : Nat := 4983230072969 + 3 ^ 40 * 912753 * 2
def baseEnd_912753 : Nat := 156227002611124194463277

theorem tailTrace_912753 : CollatzResearch.WordTrace tailWord_912753 prefixEnd_912753 156227002611124194463277 := by
  unfold tailWord_912753
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290836862259241646806913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22193891241506161097871275 33290836862259241646806913)
  ·
    refine ⟨24968127646694431235105185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33290836862259241646806913 24968127646694431235105185)
    ·
      refine ⟨18726095735020823426328889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24968127646694431235105185 18726095735020823426328889)
      ·
        refine ⟨14044571801265617569746667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18726095735020823426328889 14044571801265617569746667)
        ·
          refine ⟨21066857701898426354620001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044571801265617569746667 21066857701898426354620001)
          ·
            refine ⟨15800143276423819765965001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21066857701898426354620001 15800143276423819765965001)
            ·
              refine ⟨11850107457317864824473751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15800143276423819765965001 11850107457317864824473751)
              ·
                refine ⟨17775161185976797236710627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11850107457317864824473751 17775161185976797236710627)
                ·
                  refine ⟨26662741778965195855065941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17775161185976797236710627 26662741778965195855065941)
                  ·
                    refine ⟨156227002611124194463277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26662741778965195855065941 156227002611124194463277)
                    ·
                      rfl

theorem cell23_912753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_912753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912753 prefixEnd_912753 := by exact prefixLift 912753
  have htrace : WordTrace (prefixWord ++ tailWord_912753) baseStart_912753 baseEnd_912753 := by
    simpa [prefixWord, tailWord_912753, baseEnd_912753] using wordTrace_append hprefix tailTrace_912753
  have hstable : (prefixWord ++ tailWord_912753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912753).length < 2 ^ (prefixWord ++ tailWord_912753).sum := by decide
  have hdescent : baseEnd_912753 < baseStart_912753 := by decide
  rcases family_descends (prefixWord ++ tailWord_912753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912794 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_912794 : Nat := 118140960795 + 912794 * 2 ^ 59
def prefixEnd_912794 : Nat := 4983230072969 + 3 ^ 40 * 912794 * 2
def baseEnd_912794 : Nat := 468702060540206922977143

theorem tailTrace_912794 : CollatzResearch.WordTrace tailWord_912794 prefixEnd_912794 468702060540206922977143 := by
  unfold tailWord_912794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323083063777676412262359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22194888170073803766032957 8323083063777676412262359)
  ·
    refine ⟨12484624595666514618393539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8323083063777676412262359 12484624595666514618393539)
    ·
      refine ⟨18726936893499771927590309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12484624595666514618393539 18726936893499771927590309)
      ·
        refine ⟨3511300667531207236423183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18726936893499771927590309 3511300667531207236423183)
        ·
          refine ⟨5266951001296810854634775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511300667531207236423183 5266951001296810854634775)
          ·
            refine ⟨7900426501945216281952163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266951001296810854634775 7900426501945216281952163)
            ·
              refine ⟨11850639752917824422928245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900426501945216281952163 11850639752917824422928245)
              ·
                refine ⟨1110997476836046039649523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11850639752917824422928245 1110997476836046039649523)
                ·
                  refine ⟨1666496215254069059474285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110997476836046039649523 1666496215254069059474285)
                  ·
                    refine ⟨624936080720275897302857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666496215254069059474285 624936080720275897302857)
                    ·
                      refine ⟨468702060540206922977143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624936080720275897302857 468702060540206922977143)
                      ·
                        rfl

theorem cell23_912794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_912794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912794 prefixEnd_912794 := by exact prefixLift 912794
  have htrace : WordTrace (prefixWord ++ tailWord_912794) baseStart_912794 baseEnd_912794 := by
    simpa [prefixWord, tailWord_912794, baseEnd_912794] using wordTrace_append hprefix tailTrace_912794
  have hstable : (prefixWord ++ tailWord_912794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912794).length < 2 ^ (prefixWord ++ tailWord_912794).sum := by decide
  have hdescent : baseEnd_912794 < baseStart_912794 := by decide
  rcases family_descends (prefixWord ++ tailWord_912794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912828 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_912828 : Nat := 118140960795 + 912828 * 2 ^ 59
def prefixEnd_912828 : Nat := 4983230072969 + 3 ^ 40 * 912828 * 2
def baseEnd_912828 : Nat := 468719518882459789951987

theorem tailTrace_912828 : CollatzResearch.WordTrace tailWord_912828 prefixEnd_912828 468719518882459789951987 := by
  unfold tailWord_912828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646786168493764727893569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22195714891325019637191425 16646786168493764727893569)
  ·
    refine ⟨12485089626370323545920177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16646786168493764727893569 12485089626370323545920177)
    ·
      refine ⟨9363817219777742659440133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12485089626370323545920177 9363817219777742659440133)
      ·
        refine ⟨1755715728708326748645025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9363817219777742659440133 1755715728708326748645025)
        ·
          refine ⟨1316786796531245061483769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755715728708326748645025 1316786796531245061483769)
          ·
            refine ⟨987590097398433796112827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316786796531245061483769 987590097398433796112827)
            ·
              refine ⟨1481385146097650694169241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987590097398433796112827 1481385146097650694169241)
              ·
                refine ⟨1111038859573238020626931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481385146097650694169241 1111038859573238020626931)
                ·
                  refine ⟨1666558289359857030940397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111038859573238020626931 1666558289359857030940397)
                  ·
                    refine ⟨624959358509946386602649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666558289359857030940397 624959358509946386602649)
                    ·
                      refine ⟨468719518882459789951987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 624959358509946386602649 468719518882459789951987)
                      ·
                        rfl

theorem cell23_912828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_912828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912828 prefixEnd_912828 := by exact prefixLift 912828
  have htrace : WordTrace (prefixWord ++ tailWord_912828) baseStart_912828 baseEnd_912828 := by
    simpa [prefixWord, tailWord_912828, baseEnd_912828] using wordTrace_append hprefix tailTrace_912828
  have hstable : (prefixWord ++ tailWord_912828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912828).length < 2 ^ (prefixWord ++ tailWord_912828).sum := by decide
  have hdescent : baseEnd_912828 < baseStart_912828 := by decide
  rcases family_descends (prefixWord ++ tailWord_912828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912830 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_912830 : Nat := 118140960795 + 912830 * 2 ^ 59
def prefixEnd_912830 : Nat := 4983230072969 + 3 ^ 40 * 912830 * 2
def baseEnd_912830 : Nat := 52080060649307642458553

theorem tailTrace_912830 : CollatzResearch.WordTrace tailWord_912830 prefixEnd_912830 52080060649307642458553 := by
  unfold tailWord_912830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161705660372535474669993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22195763521986855864906629 4161705660372535474669993)
  ·
    refine ⟨3121279245279401606002495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4161705660372535474669993 3121279245279401606002495)
    ·
      refine ⟨4681918867919102409003743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121279245279401606002495 4681918867919102409003743)
      ·
        refine ⟨7022878301878653613505615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681918867919102409003743 7022878301878653613505615)
        ·
          refine ⟨10534317452817980420258423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022878301878653613505615 10534317452817980420258423)
          ·
            refine ⟨15801476179226970630387635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534317452817980420258423 15801476179226970630387635)
            ·
              refine ⟨23702214268840455945581453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15801476179226970630387635 23702214268840455945581453)
              ·
                refine ⟨8888330350815170979593045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23702214268840455945581453 8888330350815170979593045)
                ·
                  refine ⟨52080060649307642458553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8888330350815170979593045 52080060649307642458553)
                  ·
                    rfl

theorem cell23_912830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_912830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912830 prefixEnd_912830 := by exact prefixLift 912830
  have htrace : WordTrace (prefixWord ++ tailWord_912830) baseStart_912830 baseEnd_912830 := by
    simpa [prefixWord, tailWord_912830, baseEnd_912830] using wordTrace_append hprefix tailTrace_912830
  have hstable : (prefixWord ++ tailWord_912830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912830).length < 2 ^ (prefixWord ++ tailWord_912830).sum := by decide
  have hdescent : baseEnd_912830 < baseStart_912830 := by decide
  rcases family_descends (prefixWord ++ tailWord_912830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912874 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_912874 : Nat := 118140960795 + 912874 * 2 ^ 59
def prefixEnd_912874 : Nat := 4983230072969 + 3 ^ 40 * 912874 * 2
def baseEnd_912874 : Nat := 468743138992566609976775

theorem tailTrace_912874 : CollatzResearch.WordTrace tailWord_912874 prefixEnd_912874 468743138992566609976775 := by
  unfold tailWord_912874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323812523705219827990419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22196833396547252874641117 8323812523705219827990419)
  ·
    refine ⟨12485718785557829741985629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8323812523705219827990419 12485718785557829741985629)
    ·
      refine ⟨4682144544584186153244611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12485718785557829741985629 4682144544584186153244611)
      ·
        refine ⟨7023216816876279229866917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682144544584186153244611 7023216816876279229866917)
        ·
          refine ⟨1316853153164302355600047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7023216816876279229866917 1316853153164302355600047)
          ·
            refine ⟨1975279729746453533400071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316853153164302355600047 1975279729746453533400071)
            ·
              refine ⟨2962919594619680300100107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975279729746453533400071 2962919594619680300100107)
              ·
                refine ⟨4444379391929520450150161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962919594619680300100107 4444379391929520450150161)
                ·
                  refine ⟨3333284543947140337612621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444379391929520450150161 3333284543947140337612621)
                  ·
                    refine ⟨1249981703980177626604733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333284543947140337612621 1249981703980177626604733)
                    ·
                      refine ⟨468743138992566609976775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1249981703980177626604733 468743138992566609976775)
                      ·
                        rfl

theorem cell23_912874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_912874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912874 prefixEnd_912874 := by exact prefixLift 912874
  have htrace : WordTrace (prefixWord ++ tailWord_912874) baseStart_912874 baseEnd_912874 := by
    simpa [prefixWord, tailWord_912874, baseEnd_912874] using wordTrace_append hprefix tailTrace_912874
  have hstable : (prefixWord ++ tailWord_912874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912874).length < 2 ^ (prefixWord ++ tailWord_912874).sum := by decide
  have hdescent : baseEnd_912874 < baseStart_912874 := by decide
  rcases family_descends (prefixWord ++ tailWord_912874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912909 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_912909 : Nat := 118140960795 + 912909 * 2 ^ 59
def prefixEnd_912909 : Nat := 4983230072969 + 3 ^ 40 * 912909 * 2
def baseEnd_912909 : Nat := 468761110815473973039115

theorem tailTrace_912909 : CollatzResearch.WordTrace tailWord_912909 prefixEnd_912909 468761110815473973039115 := by
  unfold tailWord_912909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33296526649694080289485781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22197684433129386859657187 33296526649694080289485781)
  ·
    refine ⟨780387343352205006784823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33296526649694080289485781 780387343352205006784823)
    ·
      refine ⟨1170581015028307510177235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780387343352205006784823 1170581015028307510177235)
      ·
        refine ⟨1755871522542461265265853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170581015028307510177235 1755871522542461265265853)
        ·
          refine ⟨658451820953422974474695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1755871522542461265265853 658451820953422974474695)
          ·
            refine ⟨987677731430134461712043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658451820953422974474695 987677731430134461712043)
            ·
              refine ⟨1481516597145201692568065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987677731430134461712043 1481516597145201692568065)
              ·
                refine ⟨1111137447858901269426049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481516597145201692568065 1111137447858901269426049)
                ·
                  refine ⟨833353085894175952069537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111137447858901269426049 833353085894175952069537)
                  ·
                    refine ⟨625014814420631964052153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833353085894175952069537 625014814420631964052153)
                    ·
                      refine ⟨468761110815473973039115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625014814420631964052153 468761110815473973039115)
                      ·
                        rfl

theorem cell23_912909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_912909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912909 prefixEnd_912909 := by exact prefixLift 912909
  have htrace : WordTrace (prefixWord ++ tailWord_912909) baseStart_912909 baseEnd_912909 := by
    simpa [prefixWord, tailWord_912909, baseEnd_912909] using wordTrace_append hprefix tailTrace_912909
  have hstable : (prefixWord ++ tailWord_912909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912909).length < 2 ^ (prefixWord ++ tailWord_912909).sum := by decide
  have hdescent : baseEnd_912909 < baseStart_912909 := by decide
  rcases family_descends (prefixWord ++ tailWord_912909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912924 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_912924 : Nat := 118140960795 + 912924 * 2 ^ 59
def prefixEnd_912924 : Nat := 4983230072969 + 3 ^ 40 * 912924 * 2
def baseEnd_912924 : Nat := 156256271008430471450515

theorem tailTrace_912924 : CollatzResearch.WordTrace tailWord_912924 prefixEnd_912924 156256271008430471450515 := by
  unfold tailWord_912924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16648536872319868925640913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22198049163093158567521217 16648536872319868925640913)
  ·
    refine ⟨12486402654239901694230685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16648536872319868925640913 12486402654239901694230685)
    ·
      refine ⟨4682400995339963135336507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12486402654239901694230685 4682400995339963135336507)
      ·
        refine ⟨7023601493009944703004761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682400995339963135336507 7023601493009944703004761)
        ·
          refine ⟨5267701119757458527253571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023601493009944703004761 5267701119757458527253571)
          ·
            refine ⟨7901551679636187790880357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267701119757458527253571 7901551679636187790880357)
            ·
              refine ⟨1481540939931785210790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7901551679636187790880357 1481540939931785210790067)
              ·
                refine ⟨2222311409897677816185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481540939931785210790067 2222311409897677816185101)
                ·
                  refine ⟨833366778711629181069413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2222311409897677816185101 833366778711629181069413)
                  ·
                    refine ⟨156256271008430471450515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 833366778711629181069413 156256271008430471450515)
                    ·
                      rfl

theorem cell23_912924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_912924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_912924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_912924 prefixEnd_912924 := by exact prefixLift 912924
  have htrace : WordTrace (prefixWord ++ tailWord_912924) baseStart_912924 baseEnd_912924 := by
    simpa [prefixWord, tailWord_912924, baseEnd_912924] using wordTrace_append hprefix tailTrace_912924
  have hstable : (prefixWord ++ tailWord_912924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912924).length < 2 ^ (prefixWord ++ tailWord_912924).sum := by decide
  have hdescent : baseEnd_912924 < baseStart_912924 := by decide
  rcases family_descends (prefixWord ++ tailWord_912924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913014 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_913014 : Nat := 118140960795 + 913014 * 2 ^ 59
def prefixEnd_913014 : Nat := 4983230072969 + 3 ^ 40 * 913014 * 2
def baseEnd_913014 : Nat := 156271675428065354075377

theorem tailTrace_913014 : CollatzResearch.WordTrace tailWord_913014 prefixEnd_913014 156271675428065354075377 := by
  unfold tailWord_913014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081272269644605201378631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22200237542875788814705397 2081272269644605201378631)
  ·
    refine ⟨3121908404466907802067947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081272269644605201378631 3121908404466907802067947)
    ·
      refine ⟨4682862606700361703101921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121908404466907802067947 4682862606700361703101921)
      ·
        refine ⟨3512146955025271277326441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4682862606700361703101921 3512146955025271277326441)
        ·
          refine ⟨2634110216268953457994831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512146955025271277326441 2634110216268953457994831)
          ·
            refine ⟨3951165324403430186992247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634110216268953457994831 3951165324403430186992247)
            ·
              refine ⟨5926747986605145280488371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951165324403430186992247 5926747986605145280488371)
              ·
                refine ⟨8890121979907717920732557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926747986605145280488371 8890121979907717920732557)
                ·
                  refine ⟨3333795742465394220274709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8890121979907717920732557 3333795742465394220274709)
                  ·
                    refine ⟨156271675428065354075377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3333795742465394220274709 156271675428065354075377)
                    ·
                      rfl

theorem cell23_913014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_913014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913014 prefixEnd_913014 := by exact prefixLift 913014
  have htrace : WordTrace (prefixWord ++ tailWord_913014) baseStart_913014 baseEnd_913014 := by
    simpa [prefixWord, tailWord_913014, baseEnd_913014] using wordTrace_append hprefix tailTrace_913014
  have hstable : (prefixWord ++ tailWord_913014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913014).length < 2 ^ (prefixWord ++ tailWord_913014).sum := by decide
  have hdescent : baseEnd_913014 < baseStart_913014 := by decide
  rcases family_descends (prefixWord ++ tailWord_913014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913031 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 2, 4]
def baseStart_913031 : Nat := 118140960795 + 913031 * 2 ^ 59
def prefixEnd_913031 : Nat := 4983230072969 + 3 ^ 40 * 913031 * 2
def baseEnd_913031 : Nat := 156274585151774165237851

theorem tailTrace_913031 : CollatzResearch.WordTrace tailWord_913031 prefixEnd_913031 156274585151774165237851 := by
  unfold tailWord_913031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33300976355252095125426947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22200650903501396750284631 33300976355252095125426947)
  ·
    refine ⟨49951464532878142688140421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33300976355252095125426947 49951464532878142688140421)
    ·
      refine ⟨9365899599914651754026329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49951464532878142688140421 9365899599914651754026329)
      ·
        refine ⟨7024424699935988815519747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9365899599914651754026329 7024424699935988815519747)
        ·
          refine ⟨10536637049903983223279621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024424699935988815519747 10536637049903983223279621)
          ·
            refine ⟨1975619446856996854364929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10536637049903983223279621 1975619446856996854364929)
            ·
              refine ⟨1481714585142747640773697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975619446856996854364929 1481714585142747640773697)
              ·
                refine ⟨1111285938857060730580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481714585142747640773697 1111285938857060730580273)
                ·
                  refine ⟨833464454142795547935205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111285938857060730580273 833464454142795547935205)
                  ·
                    refine ⟨156274585151774165237851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 833464454142795547935205 156274585151774165237851)
                    ·
                      rfl

theorem cell23_913031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_913031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913031 prefixEnd_913031 := by exact prefixLift 913031
  have htrace : WordTrace (prefixWord ++ tailWord_913031) baseStart_913031 baseEnd_913031 := by
    simpa [prefixWord, tailWord_913031, baseEnd_913031] using wordTrace_append hprefix tailTrace_913031
  have hstable : (prefixWord ++ tailWord_913031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913031).length < 2 ^ (prefixWord ++ tailWord_913031).sum := by decide
  have hdescent : baseEnd_913031 < baseStart_913031 := by decide
  rcases family_descends (prefixWord ++ tailWord_913031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913055 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 3, 2, 2]
def baseStart_913055 : Nat := 118140960795 + 913055 * 2 ^ 59
def prefixEnd_913055 : Nat := 4983230072969 + 3 ^ 40 * 913055 * 2
def baseEnd_913055 : Nat := 468836078991030401813443

theorem tailTrace_913055 : CollatzResearch.WordTrace tailWord_913055 prefixEnd_913055 468836078991030401813443 := by
  unfold tailWord_913055
  simp only [CollatzResearch.WordTrace]
  refine ⟨33301851707165147224300619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22201234471443431482867079 33301851707165147224300619)
  ·
    refine ⟨49952777560747720836450929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33301851707165147224300619 49952777560747720836450929)
    ·
      refine ⟨37464583170560790627338197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49952777560747720836450929 37464583170560790627338197)
      ·
        refine ⟨878076168060018530328239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37464583170560790627338197 878076168060018530328239)
        ·
          refine ⟨1317114252090027795492359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878076168060018530328239 1317114252090027795492359)
          ·
            refine ⟨1975671378135041693238539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317114252090027795492359 1975671378135041693238539)
            ·
              refine ⟨2963507067202562539857809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975671378135041693238539 2963507067202562539857809)
              ·
                refine ⟨2222630300401921904893357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963507067202562539857809 2222630300401921904893357)
                ·
                  refine ⟨833486362650720714335009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2222630300401921904893357 833486362650720714335009)
                  ·
                    refine ⟨625114771988040535751257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833486362650720714335009 625114771988040535751257)
                    ·
                      refine ⟨468836078991030401813443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625114771988040535751257 468836078991030401813443)
                      ·
                        rfl

theorem cell23_913055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_913055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913055 prefixEnd_913055 := by exact prefixLift 913055
  have htrace : WordTrace (prefixWord ++ tailWord_913055) baseStart_913055 baseEnd_913055 := by
    simpa [prefixWord, tailWord_913055, baseEnd_913055] using wordTrace_append hprefix tailTrace_913055
  have hstable : (prefixWord ++ tailWord_913055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913055).length < 2 ^ (prefixWord ++ tailWord_913055).sum := by decide
  have hdescent : baseEnd_913055 < baseStart_913055 := by decide
  rcases family_descends (prefixWord ++ tailWord_913055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913087 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 6]
def baseStart_913087 : Nat := 118140960795 + 913087 * 2 ^ 59
def prefixEnd_913087 : Nat := 4983230072969 + 3 ^ 40 * 913087 * 2
def baseEnd_913087 : Nat := 156284170123991425537765

theorem tailTrace_913087 : CollatzResearch.WordTrace tailWord_913087 prefixEnd_913087 156284170123991425537765 := by
  unfold tailWord_913087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33303018843049216689465515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22202012562032811126310343 33303018843049216689465515)
  ·
    refine ⟨49954528264573825034198273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33303018843049216689465515 49954528264573825034198273)
    ·
      refine ⟨37465896198430368775648705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49954528264573825034198273 37465896198430368775648705)
      ·
        refine ⟨28099422148822776581736529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37465896198430368775648705 28099422148822776581736529)
        ·
          refine ⟨21074566611617082436302397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28099422148822776581736529 21074566611617082436302397)
          ·
            refine ⟨7902962479356405913613399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21074566611617082436302397 7902962479356405913613399)
            ·
              refine ⟨11854443719034608870420099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902962479356405913613399 11854443719034608870420099)
              ·
                refine ⟨17781665578551913305630149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11854443719034608870420099 17781665578551913305630149)
                ·
                  refine ⟨3334062295978483744805653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17781665578551913305630149 3334062295978483744805653)
                  ·
                    refine ⟨156284170123991425537765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3334062295978483744805653 156284170123991425537765)
                    ·
                      rfl

theorem cell23_913087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_913087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913087 prefixEnd_913087 := by exact prefixLift 913087
  have htrace : WordTrace (prefixWord ++ tailWord_913087) baseStart_913087 baseEnd_913087 := by
    simpa [prefixWord, tailWord_913087, baseEnd_913087] using wordTrace_append hprefix tailTrace_913087
  have hstable : (prefixWord ++ tailWord_913087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913087).length < 2 ^ (prefixWord ++ tailWord_913087).sum := by decide
  have hdescent : baseEnd_913087 < baseStart_913087 := by decide
  rcases family_descends (prefixWord ++ tailWord_913087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913107 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_913107 : Nat := 118140960795 + 913107 * 2 ^ 59
def prefixEnd_913107 : Nat := 4983230072969 + 3 ^ 40 * 913107 * 2
def baseEnd_913107 : Nat := 468862779985064198363203

theorem tailTrace_913107 : CollatzResearch.WordTrace tailWord_913107 prefixEnd_913107 468862779985064198363203 := by
  unfold tailWord_913107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33303748302976760105193575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22202498868651173403462383 33303748302976760105193575)
  ·
    refine ⟨49955622454465140157790363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33303748302976760105193575 49955622454465140157790363)
    ·
      refine ⟨74933433681697710236685545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49955622454465140157790363 74933433681697710236685545)
      ·
        refine ⟨56200075261273282677514159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74933433681697710236685545 56200075261273282677514159)
        ·
          refine ⟨84300112891909924016271239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56200075261273282677514159 84300112891909924016271239)
          ·
            refine ⟨126450169337864886024406859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84300112891909924016271239 126450169337864886024406859)
            ·
              refine ⟨189675254006797329036610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126450169337864886024406859 189675254006797329036610289)
              ·
                refine ⟨142256440505097996777457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189675254006797329036610289 142256440505097996777457717)
                ·
                  refine ⟨13336541297352937197886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142256440505097996777457717 13336541297352937197886661)
                  ·
                    refine ⟨2500601493253675724603749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13336541297352937197886661 2500601493253675724603749)
                    ·
                      refine ⟨468862779985064198363203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2500601493253675724603749 468862779985064198363203)
                      ·
                        rfl

theorem cell23_913107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_913107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913107 prefixEnd_913107 := by exact prefixLift 913107
  have htrace : WordTrace (prefixWord ++ tailWord_913107) baseStart_913107 baseEnd_913107 := by
    simpa [prefixWord, tailWord_913107, baseEnd_913107] using wordTrace_append hprefix tailTrace_913107
  have hstable : (prefixWord ++ tailWord_913107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913107).length < 2 ^ (prefixWord ++ tailWord_913107).sum := by decide
  have hdescent : baseEnd_913107 < baseStart_913107 := by decide
  rcases family_descends (prefixWord ++ tailWord_913107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913128 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_913128 : Nat := 118140960795 + 913128 * 2 ^ 59
def prefixEnd_913128 : Nat := 4983230072969 + 3 ^ 40 * 913128 * 2
def baseEnd_913128 : Nat := 468873563078808616200607

theorem tailTrace_913128 : CollatzResearch.WordTrace tailWord_913128 prefixEnd_913128 468873563078808616200607 := by
  unfold tailWord_913128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652257117950340345854019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22203009490600453794472025 16652257117950340345854019)
  ·
    refine ⟨24978385676925510518781029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16652257117950340345854019 24978385676925510518781029)
    ·
      refine ⟨4683447314423533222271443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24978385676925510518781029 4683447314423533222271443)
      ·
        refine ⟨7025170971635299833407165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683447314423533222271443 7025170971635299833407165)
        ·
          refine ⟨2634439114363237437527687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7025170971635299833407165 2634439114363237437527687)
          ·
            refine ⟨3951658671544856156291531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634439114363237437527687 3951658671544856156291531)
            ·
              refine ⟨5927488007317284234437297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951658671544856156291531 5927488007317284234437297)
              ·
                refine ⟨4445616005487963175827973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927488007317284234437297 4445616005487963175827973)
                ·
                  refine ⟨833553001028993095467745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4445616005487963175827973 833553001028993095467745)
                  ·
                    refine ⟨625164750771744821600809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833553001028993095467745 625164750771744821600809)
                    ·
                      refine ⟨468873563078808616200607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625164750771744821600809 468873563078808616200607)
                      ·
                        rfl

theorem cell23_913128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_913128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913128 prefixEnd_913128 := by exact prefixLift 913128
  have htrace : WordTrace (prefixWord ++ tailWord_913128) baseStart_913128 baseEnd_913128 := by
    simpa [prefixWord, tailWord_913128, baseEnd_913128] using wordTrace_append hprefix tailTrace_913128
  have hstable : (prefixWord ++ tailWord_913128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913128).length < 2 ^ (prefixWord ++ tailWord_913128).sum := by decide
  have hdescent : baseEnd_913128 < baseStart_913128 := by decide
  rcases family_descends (prefixWord ++ tailWord_913128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913144 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_913144 : Nat := 118140960795 + 913144 * 2 ^ 59
def prefixEnd_913144 : Nat := 4983230072969 + 3 ^ 40 * 913144 * 2
def baseEnd_913144 : Nat := 468881778769280553600533

theorem tailTrace_913144 : CollatzResearch.WordTrace tailWord_913144 prefixEnd_913144 468881778769280553600533 := by
  unfold tailWord_913144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652548901921357712145243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22203398535895143616193657 16652548901921357712145243)
  ·
    refine ⟨24978823352882036568217865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16652548901921357712145243 24978823352882036568217865)
    ·
      refine ⟨18734117514661527426163399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24978823352882036568217865 18734117514661527426163399)
      ·
        refine ⟨28101176271992291139245099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18734117514661527426163399 28101176271992291139245099)
        ·
          refine ⟨42151764407988436708867649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28101176271992291139245099 42151764407988436708867649)
          ·
            refine ⟨31613823305991327531650737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42151764407988436708867649 31613823305991327531650737)
            ·
              refine ⟨23710367479493495648738053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31613823305991327531650737 23710367479493495648738053)
              ·
                refine ⟨4445693902405030434138385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23710367479493495648738053 4445693902405030434138385)
                ·
                  refine ⟨3334270426803772825603789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445693902405030434138385 3334270426803772825603789)
                  ·
                    refine ⟨1250351410051414809601421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334270426803772825603789 1250351410051414809601421)
                    ·
                      refine ⟨468881778769280553600533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250351410051414809601421 468881778769280553600533)
                      ·
                        rfl

theorem cell23_913144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_913144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913144 prefixEnd_913144 := by exact prefixLift 913144
  have htrace : WordTrace (prefixWord ++ tailWord_913144) baseStart_913144 baseEnd_913144 := by
    simpa [prefixWord, tailWord_913144, baseEnd_913144] using wordTrace_append hprefix tailTrace_913144
  have hstable : (prefixWord ++ tailWord_913144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913144).length < 2 ^ (prefixWord ++ tailWord_913144).sum := by decide
  have hdescent : baseEnd_913144 < baseStart_913144 := by decide
  rcases family_descends (prefixWord ++ tailWord_913144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 7]
def baseStart_913147 : Nat := 118140960795 + 913147 * 2 ^ 59
def prefixEnd_913147 : Nat := 4983230072969 + 3 ^ 40 * 913147 * 2
def baseEnd_913147 : Nat := 156294439737081347287673

theorem tailTrace_913147 : CollatzResearch.WordTrace tailWord_913147 prefixEnd_913147 156294439737081347287673 := by
  unfold tailWord_913147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305207222831846936649695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22203471481887897957766463 33305207222831846936649695)
  ·
    refine ⟨49957810834247770404974543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305207222831846936649695 49957810834247770404974543)
    ·
      refine ⟨74936716251371655607461815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49957810834247770404974543 74936716251371655607461815)
      ·
        refine ⟨112405074377057483411192723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74936716251371655607461815 112405074377057483411192723)
        ·
          refine ⟨168607611565586225116789085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112405074377057483411192723 168607611565586225116789085)
          ·
            refine ⟨63227854337094834418795907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168607611565586225116789085 63227854337094834418795907)
            ·
              refine ⟨94841781505642251628193861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63227854337094834418795907 94841781505642251628193861)
              ·
                refine ⟨17782834032307922180286349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94841781505642251628193861 17782834032307922180286349)
                ·
                  refine ⟨6668562762115470817607381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17782834032307922180286349 6668562762115470817607381)
                  ·
                    refine ⟨156294439737081347287673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6668562762115470817607381 156294439737081347287673)
                    ·
                      rfl

theorem cell23_913147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_913147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913147 prefixEnd_913147 := by exact prefixLift 913147
  have htrace : WordTrace (prefixWord ++ tailWord_913147) baseStart_913147 baseEnd_913147 := by
    simpa [prefixWord, tailWord_913147, baseEnd_913147] using wordTrace_append hprefix tailTrace_913147
  have hstable : (prefixWord ++ tailWord_913147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913147).length < 2 ^ (prefixWord ++ tailWord_913147).sum := by decide
  have hdescent : baseEnd_913147 < baseStart_913147 := by decide
  rcases family_descends (prefixWord ++ tailWord_913147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913162 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_913162 : Nat := 118140960795 + 913162 * 2 ^ 59
def prefixEnd_913162 : Nat := 4983230072969 + 3 ^ 40 * 913162 * 2
def baseEnd_913162 : Nat := 468891021421061483175451

theorem tailTrace_913162 : CollatzResearch.WordTrace tailWord_913162 prefixEnd_913162 468891021421061483175451 := by
  unfold tailWord_913162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8326438579444376124611435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22203836211851669665630493 8326438579444376124611435)
  ·
    refine ⟨12489657869166564186917153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8326438579444376124611435 12489657869166564186917153)
    ·
      refine ⟨9367243401874923140187865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12489657869166564186917153 9367243401874923140187865)
      ·
        refine ⟨7025432551406192355140899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9367243401874923140187865 7025432551406192355140899)
        ·
          refine ⟨10538148827109288532711349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025432551406192355140899 10538148827109288532711349)
          ·
            refine ⟨987951452541495799941689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10538148827109288532711349 987951452541495799941689)
            ·
              refine ⟨740963589406121849956267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987951452541495799941689 740963589406121849956267)
              ·
                refine ⟨1111445384109182774934401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740963589406121849956267 1111445384109182774934401)
                ·
                  refine ⟨833584038081887081200801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111445384109182774934401 833584038081887081200801)
                  ·
                    refine ⟨625188028561415310900601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833584038081887081200801 625188028561415310900601)
                    ·
                      refine ⟨468891021421061483175451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625188028561415310900601 468891021421061483175451)
                      ·
                        rfl

theorem cell23_913162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_913162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913162 prefixEnd_913162 := by exact prefixLift 913162
  have htrace : WordTrace (prefixWord ++ tailWord_913162) baseStart_913162 baseEnd_913162 := by
    simpa [prefixWord, tailWord_913162, baseEnd_913162] using wordTrace_append hprefix tailTrace_913162
  have hstable : (prefixWord ++ tailWord_913162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913162).length < 2 ^ (prefixWord ++ tailWord_913162).sum := by decide
  have hdescent : baseEnd_913162 < baseStart_913162 := by decide
  rcases family_descends (prefixWord ++ tailWord_913162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913201 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_913201 : Nat := 118140960795 + 913201 * 2 ^ 59
def prefixEnd_913201 : Nat := 4983230072969 + 3 ^ 40 * 913201 * 2
def baseEnd_913201 : Nat := 468911047166586830587771

theorem tailTrace_913201 : CollatzResearch.WordTrace tailWord_913201 prefixEnd_913201 468911047166586830587771 := by
  unfold tailWord_913201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307176764636214159115457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22204784509757476106076971 33307176764636214159115457)
  ·
    refine ⟨24980382573477160619336593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33307176764636214159115457 24980382573477160619336593)
    ·
      refine ⟨18735286930107870464502445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24980382573477160619336593 18735286930107870464502445)
      ·
        refine ⟨7025732598790451424188417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18735286930107870464502445 7025732598790451424188417)
        ·
          refine ⟨5269299449092838568141313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7025732598790451424188417 5269299449092838568141313)
          ·
            refine ⟨3951974586819628926105985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269299449092838568141313 3951974586819628926105985)
            ·
              refine ⟨2963980940114721694579489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951974586819628926105985 2963980940114721694579489)
              ·
                refine ⟨2222985705086041270934617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963980940114721694579489 2222985705086041270934617)
                ·
                  refine ⟨1667239278814530953200963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222985705086041270934617 1667239278814530953200963)
                  ·
                    refine ⟨2500858918221796429801445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667239278814530953200963 2500858918221796429801445)
                    ·
                      refine ⟨468911047166586830587771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2500858918221796429801445 468911047166586830587771)
                      ·
                        rfl

theorem cell23_913201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_913201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913201 prefixEnd_913201 := by exact prefixLift 913201
  have htrace : WordTrace (prefixWord ++ tailWord_913201) baseStart_913201 baseEnd_913201 := by
    simpa [prefixWord, tailWord_913201, baseEnd_913201] using wordTrace_append hprefix tailTrace_913201
  have hstable : (prefixWord ++ tailWord_913201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913201).length < 2 ^ (prefixWord ++ tailWord_913201).sum := by decide
  have hdescent : baseEnd_913201 < baseStart_913201 := by decide
  rcases family_descends (prefixWord ++ tailWord_913201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913228 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_913228 : Nat := 118140960795 + 913228 * 2 ^ 59
def prefixEnd_913228 : Nat := 4983230072969 + 3 ^ 40 * 913228 * 2
def baseEnd_913228 : Nat := 156308303714752741650049

theorem tailTrace_913228 : CollatzResearch.WordTrace tailWord_913228 prefixEnd_913228 156308303714752741650049 := by
  unfold tailWord_913228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654080767769198885174169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22205441023692265180232225 16654080767769198885174169)
  ·
    refine ⟨12490560575826899163880627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16654080767769198885174169 12490560575826899163880627)
    ·
      refine ⟨18735840863740348745820941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490560575826899163880627 18735840863740348745820941)
      ·
        refine ⟨7025940323902630779682853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18735840863740348745820941 7025940323902630779682853)
        ·
          refine ⟨1317363810731743271190535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7025940323902630779682853 1317363810731743271190535)
          ·
            refine ⟨1976045716097614906785803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317363810731743271190535 1976045716097614906785803)
            ·
              refine ⟨2964068574146422360178705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976045716097614906785803 2964068574146422360178705)
              ·
                refine ⟨2223051430609816770134029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964068574146422360178705 2223051430609816770134029)
                ·
                  refine ⟨833644286478681288800261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2223051430609816770134029 833644286478681288800261)
                  ·
                    refine ⟨156308303714752741650049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 833644286478681288800261 156308303714752741650049)
                    ·
                      rfl

theorem cell23_913228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_913228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913228 prefixEnd_913228 := by exact prefixLift 913228
  have htrace : WordTrace (prefixWord ++ tailWord_913228) baseStart_913228 baseEnd_913228 := by
    simpa [prefixWord, tailWord_913228, baseEnd_913228] using wordTrace_append hprefix tailTrace_913228
  have hstable : (prefixWord ++ tailWord_913228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913228).length < 2 ^ (prefixWord ++ tailWord_913228).sum := by decide
  have hdescent : baseEnd_913228 < baseStart_913228 := by decide
  rcases family_descends (prefixWord ++ tailWord_913228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913258 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_913258 : Nat := 118140960795 + 913258 * 2 ^ 59
def prefixEnd_913258 : Nat := 4983230072969 + 3 ^ 40 * 913258 * 2
def baseEnd_913258 : Nat := 52104479507099234175001

theorem tailTrace_913258 : CollatzResearch.WordTrace tailWord_913258 prefixEnd_913258 52104479507099234175001 := by
  unfold tailWord_913258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327313931357428223485107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22206170483619808595960285 8327313931357428223485107)
  ·
    refine ⟨12490970897036142335227661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327313931357428223485107 12490970897036142335227661)
    ·
      refine ⟨4684114086388553375710373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12490970897036142335227661 4684114086388553375710373)
      ·
        refine ⟨878271391197853757945695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4684114086388553375710373 878271391197853757945695)
        ·
          refine ⟨1317407086796780636918543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878271391197853757945695 1317407086796780636918543)
          ·
            refine ⟨1976110630195170955377815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317407086796780636918543 1976110630195170955377815)
            ·
              refine ⟨2964165945292756433066723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976110630195170955377815 2964165945292756433066723)
              ·
                refine ⟨4446248917939134649600085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964165945292756433066723 4446248917939134649600085)
                ·
                  refine ⟨52104479507099234175001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4446248917939134649600085 52104479507099234175001)
                  ·
                    rfl

theorem cell23_913258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_913258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913258 prefixEnd_913258 := by exact prefixLift 913258
  have htrace : WordTrace (prefixWord ++ tailWord_913258) baseStart_913258 baseEnd_913258 := by
    simpa [prefixWord, tailWord_913258, baseEnd_913258] using wordTrace_append hprefix tailTrace_913258
  have hstable : (prefixWord ++ tailWord_913258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913258).length < 2 ^ (prefixWord ++ tailWord_913258).sum := by decide
  have hdescent : baseEnd_913258 < baseStart_913258 := by decide
  rcases family_descends (prefixWord ++ tailWord_913258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913291 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 8, 2]
def baseStart_913291 : Nat := 118140960795 + 913291 * 2 ^ 59
def prefixEnd_913291 : Nat := 4983230072969 + 3 ^ 40 * 913291 * 2
def baseEnd_913291 : Nat := 468957260425491478462357

theorem tailTrace_913291 : CollatzResearch.WordTrace tailWord_913291 prefixEnd_913291 468957260425491478462357 := by
  unfold tailWord_913291
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310459334310159529891727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22206972889540106353261151 33310459334310159529891727)
  ·
    refine ⟨49965689001465239294837591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33310459334310159529891727 49965689001465239294837591)
    ·
      refine ⟨74948533502197858942256387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49965689001465239294837591 74948533502197858942256387)
      ·
        refine ⟨112422800253296788413384581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74948533502197858942256387 112422800253296788413384581)
        ·
          refine ⟨21079275047493147827509609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112422800253296788413384581 21079275047493147827509609)
          ·
            refine ⟨15809456285619860870632207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21079275047493147827509609 15809456285619860870632207)
            ·
              refine ⟨23714184428429791305948311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15809456285619860870632207 23714184428429791305948311)
              ·
                refine ⟨35571276642644686958922467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23714184428429791305948311 35571276642644686958922467)
                ·
                  refine ⟨53356914963967030438383701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35571276642644686958922467 53356914963967030438383701)
                  ·
                    refine ⟨625276347233988637949809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53356914963967030438383701 625276347233988637949809)
                    ·
                      refine ⟨468957260425491478462357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625276347233988637949809 468957260425491478462357)
                      ·
                        rfl

theorem cell23_913291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8, 2].length) (baseStart_913291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913291 prefixEnd_913291 := by exact prefixLift 913291
  have htrace : WordTrace (prefixWord ++ tailWord_913291) baseStart_913291 baseEnd_913291 := by
    simpa [prefixWord, tailWord_913291, baseEnd_913291] using wordTrace_append hprefix tailTrace_913291
  have hstable : (prefixWord ++ tailWord_913291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913291).length < 2 ^ (prefixWord ++ tailWord_913291).sum := by decide
  have hdescent : baseEnd_913291 < baseStart_913291 := by decide
  rcases family_descends (prefixWord ++ tailWord_913291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913301 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_913301 : Nat := 118140960795 + 913301 * 2 ^ 59
def prefixEnd_913301 : Nat := 4983230072969 + 3 ^ 40 * 913301 * 2
def baseEnd_913301 : Nat := 156320798410678813112437

theorem tailTrace_913301 : CollatzResearch.WordTrace tailWord_913301 prefixEnd_913301 156320798410678813112437 := by
  unfold tailWord_913301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310824064273931237755757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22207216042849287491837171 33310824064273931237755757)
  ·
    refine ⟨12491559024102724214158409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33310824064273931237755757 12491559024102724214158409)
    ·
      refine ⟨9368669268077043160618807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12491559024102724214158409 9368669268077043160618807)
      ·
        refine ⟨14053003902115564740928211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9368669268077043160618807 14053003902115564740928211)
        ·
          refine ⟨21079505853173347111392317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14053003902115564740928211 21079505853173347111392317)
          ·
            refine ⟨7904814694940005166772119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21079505853173347111392317 7904814694940005166772119)
            ·
              refine ⟨11857222042410007750158179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904814694940005166772119 11857222042410007750158179)
              ·
                refine ⟨17785833063615011625237269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857222042410007750158179 17785833063615011625237269)
                ·
                  refine ⟨833710924856953669932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17785833063615011625237269 833710924856953669932997)
                  ·
                    refine ⟨156320798410678813112437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 833710924856953669932997 156320798410678813112437)
                    ·
                      rfl

theorem cell23_913301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_913301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913301 prefixEnd_913301 := by exact prefixLift 913301
  have htrace : WordTrace (prefixWord ++ tailWord_913301) baseStart_913301 baseEnd_913301 := by
    simpa [prefixWord, tailWord_913301, baseEnd_913301] using wordTrace_append hprefix tailTrace_913301
  have hstable : (prefixWord ++ tailWord_913301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913301).length < 2 ^ (prefixWord ++ tailWord_913301).sum := by decide
  have hdescent : baseEnd_913301 < baseStart_913301 := by decide
  rcases family_descends (prefixWord ++ tailWord_913301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913319 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_913319 : Nat := 118140960795 + 913319 * 2 ^ 59
def prefixEnd_913319 : Nat := 4983230072969 + 3 ^ 40 * 913319 * 2
def baseEnd_913319 : Nat := 468971637883817368912229

theorem tailTrace_913319 : CollatzResearch.WordTrace tailWord_913319 prefixEnd_913319 468971637883817368912229 := by
  unfold tailWord_913319
  simp only [CollatzResearch.WordTrace]
  refine ⟨33311480578208720311911011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22207653718805813541274007 33311480578208720311911011)
  ·
    refine ⟨49967220867313080467866517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33311480578208720311911011 49967220867313080467866517)
    ·
      refine ⟨2342213478155300646931243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49967220867313080467866517 2342213478155300646931243)
      ·
        refine ⟨3513320217232950970396865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342213478155300646931243 3513320217232950970396865)
        ·
          refine ⟨2634990162924713227797649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513320217232950970396865 2634990162924713227797649)
          ·
            refine ⟨1976242622193534920848237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2634990162924713227797649 1976242622193534920848237)
            ·
              refine ⟨741090983322575595318089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976242622193534920848237 741090983322575595318089)
              ·
                refine ⟨555818237491931696488567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741090983322575595318089 555818237491931696488567)
                ·
                  refine ⟨833727356237897544732851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555818237491931696488567 833727356237897544732851)
                  ·
                    refine ⟨1250591034356846317099277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 833727356237897544732851 1250591034356846317099277)
                    ·
                      refine ⟨468971637883817368912229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250591034356846317099277 468971637883817368912229)
                      ·
                        rfl

theorem cell23_913319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_913319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913319 prefixEnd_913319 := by exact prefixLift 913319
  have htrace : WordTrace (prefixWord ++ tailWord_913319) baseStart_913319 baseEnd_913319 := by
    simpa [prefixWord, tailWord_913319, baseEnd_913319] using wordTrace_append hprefix tailTrace_913319
  have hstable : (prefixWord ++ tailWord_913319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913319).length < 2 ^ (prefixWord ++ tailWord_913319).sum := by decide
  have hdescent : baseEnd_913319 < baseStart_913319 := by decide
  rcases family_descends (prefixWord ++ tailWord_913319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913324 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_913324 : Nat := 118140960795 + 913324 * 2 ^ 59
def prefixEnd_913324 : Nat := 4983230072969 + 3 ^ 40 * 913324 * 2
def baseEnd_913324 : Nat := 468974205287089849349705

theorem tailTrace_913324 : CollatzResearch.WordTrace tailWord_913324 prefixEnd_913324 468974205287089849349705 := by
  unfold tailWord_913324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16655831471595303082921513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22207775295460404110562017 16655831471595303082921513)
  ·
    refine ⟨12491873603696477312191135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16655831471595303082921513 12491873603696477312191135)
    ·
      refine ⟨18737810405544715968286703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491873603696477312191135 18737810405544715968286703)
      ·
        refine ⟨28106715608317073952430055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18737810405544715968286703 28106715608317073952430055)
        ·
          refine ⟨42160073412475610928645083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28106715608317073952430055 42160073412475610928645083)
          ·
            refine ⟨63240110118713416392967625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42160073412475610928645083 63240110118713416392967625)
            ·
              refine ⟨47430082589035062294725719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63240110118713416392967625 47430082589035062294725719)
              ·
                refine ⟨71145123883552593442088579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47430082589035062294725719 71145123883552593442088579)
                ·
                  refine ⟨106717685825328890163132869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71145123883552593442088579 106717685825328890163132869)
                  ·
                    refine ⟨20009566092249166905587413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106717685825328890163132869 20009566092249166905587413)
                    ·
                      refine ⟨468974205287089849349705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20009566092249166905587413 468974205287089849349705)
                      ·
                        rfl

theorem cell23_913324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_913324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913324 prefixEnd_913324 := by exact prefixLift 913324
  have htrace : WordTrace (prefixWord ++ tailWord_913324) baseStart_913324 baseEnd_913324 := by
    simpa [prefixWord, tailWord_913324, baseEnd_913324] using wordTrace_append hprefix tailTrace_913324
  have hstable : (prefixWord ++ tailWord_913324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913324).length < 2 ^ (prefixWord ++ tailWord_913324).sum := by decide
  have hdescent : baseEnd_913324 < baseStart_913324 := by decide
  rcases family_descends (prefixWord ++ tailWord_913324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913326 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_913326 : Nat := 118140960795 + 913326 * 2 ^ 59
def prefixEnd_913326 : Nat := 4983230072969 + 3 ^ 40 * 913326 * 2
def baseEnd_913326 : Nat := 52108359138710982391633

theorem tailTrace_913326 : CollatzResearch.WordTrace tailWord_913326 prefixEnd_913326 52108359138710982391633 := by
  unfold tailWord_913326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163966986147920063426979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22207823926122240338277221 4163966986147920063426979)
  ·
    refine ⟨6245950479221880095140469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4163966986147920063426979 6245950479221880095140469)
    ·
      refine ⟨585557857427051258919419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6245950479221880095140469 585557857427051258919419)
      ·
        refine ⟨878336786140576888379129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585557857427051258919419 878336786140576888379129)
        ·
          refine ⟨658752589605432666284347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878336786140576888379129 658752589605432666284347)
          ·
            refine ⟨988128884408148999426521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658752589605432666284347 988128884408148999426521)
            ·
              refine ⟨741096663306111749569891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988128884408148999426521 741096663306111749569891)
              ·
                refine ⟨1111644994959167624354837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741096663306111749569891 1111644994959167624354837)
                ·
                  refine ⟨52108359138710982391633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1111644994959167624354837 52108359138710982391633)
                  ·
                    rfl

theorem cell23_913326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_913326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913326 prefixEnd_913326 := by exact prefixLift 913326
  have htrace : WordTrace (prefixWord ++ tailWord_913326) baseStart_913326 baseEnd_913326 := by
    simpa [prefixWord, tailWord_913326, baseEnd_913326] using wordTrace_append hprefix tailTrace_913326
  have hstable : (prefixWord ++ tailWord_913326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913326).length < 2 ^ (prefixWord ++ tailWord_913326).sum := by decide
  have hdescent : baseEnd_913326 < baseStart_913326 := by decide
  rcases family_descends (prefixWord ++ tailWord_913326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913358 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_913358 : Nat := 118140960795 + 913358 * 2 ^ 59
def prefixEnd_913358 : Nat := 4983230072969 + 3 ^ 40 * 913358 * 2
def baseEnd_913358 : Nat := 468991663629342716324549

theorem tailTrace_913358 : CollatzResearch.WordTrace tailWord_913358 prefixEnd_913358 468991663629342716324549 := by
  unfold tailWord_913358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164112878133428746572591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22208602016711619981720485 4164112878133428746572591)
  ·
    refine ⟨6246169317200143119858887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4164112878133428746572591 6246169317200143119858887)
    ·
      refine ⟨9369253975800214679788331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6246169317200143119858887 9369253975800214679788331)
      ·
        refine ⟨14053880963700322019682497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369253975800214679788331 14053880963700322019682497)
        ·
          refine ⟨10540410722775241514761873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14053880963700322019682497 10540410722775241514761873)
          ·
            refine ⟨7905308042081431136071405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540410722775241514761873 7905308042081431136071405)
            ·
              refine ⟨2964490515780536676026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7905308042081431136071405 2964490515780536676026777)
              ·
                refine ⟨2223367886835402507020083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964490515780536676026777 2223367886835402507020083)
                ·
                  refine ⟨3335051830253103760530125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223367886835402507020083 3335051830253103760530125)
                  ·
                    refine ⟨1250644436344913910198797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335051830253103760530125 1250644436344913910198797)
                    ·
                      refine ⟨468991663629342716324549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250644436344913910198797 468991663629342716324549)
                      ·
                        rfl

theorem cell23_913358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_913358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913358 prefixEnd_913358 := by exact prefixLift 913358
  have htrace : WordTrace (prefixWord ++ tailWord_913358) baseStart_913358 baseEnd_913358 := by
    simpa [prefixWord, tailWord_913358, baseEnd_913358] using wordTrace_append hprefix tailTrace_913358
  have hstable : (prefixWord ++ tailWord_913358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913358).length < 2 ^ (prefixWord ++ tailWord_913358).sum := by decide
  have hdescent : baseEnd_913358 < baseStart_913358 := by decide
  rcases family_descends (prefixWord ++ tailWord_913358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913362 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_913362 : Nat := 118140960795 + 913362 * 2 ^ 59
def prefixEnd_913362 : Nat := 4983230072969 + 3 ^ 40 * 913362 * 2
def baseEnd_913362 : Nat := 468993717551960700674531

theorem tailTrace_913362 : CollatzResearch.WordTrace tailWord_913362 prefixEnd_913362 468993717551960700674531 := by
  unfold tailWord_913362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328262229263234663931585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22208699278035292437150893 8328262229263234663931585)
  ·
    refine ⟨6246196671947425997948689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8328262229263234663931585 6246196671947425997948689)
    ·
      refine ⟨4684647503960569498461517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6246196671947425997948689 4684647503960569498461517)
      ·
        refine ⟨1756742813985213561923069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4684647503960569498461517 1756742813985213561923069)
        ·
          refine ⟨658778555244455085721151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1756742813985213561923069 658778555244455085721151)
          ·
            refine ⟨988167832866682628581727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658778555244455085721151 988167832866682628581727)
            ·
              refine ⟨1482251749300023942872591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988167832866682628581727 1482251749300023942872591)
              ·
                refine ⟨2223377623950035914308887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482251749300023942872591 2223377623950035914308887)
                ·
                  refine ⟨3335066435925053871463331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223377623950035914308887 3335066435925053871463331)
                  ·
                    refine ⟨5002599653887580807194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3335066435925053871463331 5002599653887580807194997)
                    ·
                      refine ⟨468993717551960700674531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5002599653887580807194997 468993717551960700674531)
                      ·
                        rfl

theorem cell23_913362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_913362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913362 prefixEnd_913362 := by exact prefixLift 913362
  have htrace : WordTrace (prefixWord ++ tailWord_913362) baseStart_913362 baseEnd_913362 := by
    simpa [prefixWord, tailWord_913362, baseEnd_913362] using wordTrace_append hprefix tailTrace_913362
  have hstable : (prefixWord ++ tailWord_913362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913362).length < 2 ^ (prefixWord ++ tailWord_913362).sum := by decide
  have hdescent : baseEnd_913362 < baseStart_913362 := by decide
  rcases family_descends (prefixWord ++ tailWord_913362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913375 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_913375 : Nat := 118140960795 + 913375 * 2 ^ 59
def prefixEnd_913375 : Nat := 4983230072969 + 3 ^ 40 * 913375 * 2
def baseEnd_913375 : Nat := 469000392800469149811971

theorem tailTrace_913375 : CollatzResearch.WordTrace tailWord_913375 prefixEnd_913375 469000392800469149811971 := by
  unfold tailWord_913375
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313523066005841875949579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22209015377337227917299719 33313523066005841875949579)
  ·
    refine ⟨49970284599008762813924369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33313523066005841875949579 49970284599008762813924369)
    ·
      refine ⟨37477713449256572110443277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49970284599008762813924369 37477713449256572110443277)
      ·
        refine ⟨14054142543471214541416229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37477713449256572110443277 14054142543471214541416229)
        ·
          refine ⟨2635151726900852726515543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14054142543471214541416229 2635151726900852726515543)
          ·
            refine ⟨3952727590351279089773315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635151726900852726515543 3952727590351279089773315)
            ·
              refine ⟨5929091385526918634659973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952727590351279089773315 5929091385526918634659973)
              ·
                refine ⟨1111704634786297243998745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5929091385526918634659973 1111704634786297243998745)
                ·
                  refine ⟨833778476089722932999059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111704634786297243998745 833778476089722932999059)
                  ·
                    refine ⟨1250667714134584399498589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 833778476089722932999059 1250667714134584399498589)
                    ·
                      refine ⟨469000392800469149811971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250667714134584399498589 469000392800469149811971)
                      ·
                        rfl

theorem cell23_913375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_913375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913375 prefixEnd_913375 := by exact prefixLift 913375
  have htrace : WordTrace (prefixWord ++ tailWord_913375) baseStart_913375 baseEnd_913375 := by
    simpa [prefixWord, tailWord_913375, baseEnd_913375] using wordTrace_append hprefix tailTrace_913375
  have hstable : (prefixWord ++ tailWord_913375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913375).length < 2 ^ (prefixWord ++ tailWord_913375).sum := by decide
  have hdescent : baseEnd_913375 < baseStart_913375 := by decide
  rcases family_descends (prefixWord ++ tailWord_913375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913391 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 6]
def baseStart_913391 : Nat := 118140960795 + 913391 * 2 ^ 59
def prefixEnd_913391 : Nat := 4983230072969 + 3 ^ 40 * 913391 * 2
def baseEnd_913391 : Nat := 156336202830313695737299

theorem tailTrace_913391 : CollatzResearch.WordTrace tailWord_913391 prefixEnd_913391 156336202830313695737299 := by
  unfold tailWord_913391
  simp only [CollatzResearch.WordTrace]
  refine ⟨33314106633947876608532027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22209404422631917739021351 33314106633947876608532027)
  ·
    refine ⟨49971159950921814912798041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33314106633947876608532027 49971159950921814912798041)
    ·
      refine ⟨37478369963191361184598531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49971159950921814912798041 37478369963191361184598531)
      ·
        refine ⟨56217554944787041776897797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37478369963191361184598531 56217554944787041776897797)
        ·
          refine ⟨10540791552147570333168337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56217554944787041776897797 10540791552147570333168337)
          ·
            refine ⟨7905593664110677749876253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540791552147570333168337 7905593664110677749876253)
            ·
              refine ⟨2964597624041504156203595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7905593664110677749876253 2964597624041504156203595)
              ·
                refine ⟨4446896436062256234305393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964597624041504156203595 4446896436062256234305393)
                ·
                  refine ⟨3335172327046692175729045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446896436062256234305393 3335172327046692175729045)
                  ·
                    refine ⟨156336202830313695737299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3335172327046692175729045 156336202830313695737299)
                    ·
                      rfl

theorem cell23_913391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_913391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913391 prefixEnd_913391 := by exact prefixLift 913391
  have htrace : WordTrace (prefixWord ++ tailWord_913391) baseStart_913391 baseEnd_913391 := by
    simpa [prefixWord, tailWord_913391, baseEnd_913391] using wordTrace_append hprefix tailTrace_913391
  have hstable : (prefixWord ++ tailWord_913391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913391).length < 2 ^ (prefixWord ++ tailWord_913391).sum := by decide
  have hdescent : baseEnd_913391 < baseStart_913391 := by decide
  rcases family_descends (prefixWord ++ tailWord_913391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913415 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_913415 : Nat := 118140960795 + 913415 * 2 ^ 59
def prefixEnd_913415 : Nat := 4983230072969 + 3 ^ 40 * 913415 * 2
def baseEnd_913415 : Nat := 469020932026648993311787

theorem tailTrace_913415 : CollatzResearch.WordTrace tailWord_913415 prefixEnd_913415 469020932026648993311787 := by
  unfold tailWord_913415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33314981985860928707405699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22209987990573952471603799 33314981985860928707405699)
  ·
    refine ⟨49972472978791393061108549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33314981985860928707405699 49972472978791393061108549)
    ·
      refine ⟨9369838683523386198957853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49972472978791393061108549 9369838683523386198957853)
      ·
        refine ⟨3513689506321269824609195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9369838683523386198957853 3513689506321269824609195)
        ·
          refine ⟨5270534259481904736913793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513689506321269824609195 5270534259481904736913793)
          ·
            refine ⟨3952900694611428552685345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270534259481904736913793 3952900694611428552685345)
            ·
              refine ⟨2964675520958571414514009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952900694611428552685345 2964675520958571414514009)
              ·
                refine ⟨2223506640718928560885507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964675520958571414514009 2223506640718928560885507)
                ·
                  refine ⟨3335259961078392841328261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223506640718928560885507 3335259961078392841328261)
                  ·
                    refine ⟨625361242702198657749049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335259961078392841328261 625361242702198657749049)
                    ·
                      refine ⟨469020932026648993311787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625361242702198657749049 469020932026648993311787)
                      ·
                        rfl

theorem cell23_913415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_913415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913415 prefixEnd_913415 := by exact prefixLift 913415
  have htrace : WordTrace (prefixWord ++ tailWord_913415) baseStart_913415 baseEnd_913415 := by
    simpa [prefixWord, tailWord_913415, baseEnd_913415] using wordTrace_append hprefix tailTrace_913415
  have hstable : (prefixWord ++ tailWord_913415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913415).length < 2 ^ (prefixWord ++ tailWord_913415).sum := by decide
  have hdescent : baseEnd_913415 < baseStart_913415 := by decide
  rcases family_descends (prefixWord ++ tailWord_913415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913451 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 6, 5]
def baseStart_913451 : Nat := 118140960795 + 913451 * 2 ^ 59
def prefixEnd_913451 : Nat := 4983230072969 + 3 ^ 40 * 913451 * 2
def baseEnd_913451 : Nat := 156346472443403617487207

theorem tailTrace_913451 : CollatzResearch.WordTrace tailWord_913451 prefixEnd_913451 156346472443403617487207 := by
  unfold tailWord_913451
  simp only [CollatzResearch.WordTrace]
  refine ⟨33316295013730506855716207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22210863342487004570477471 33316295013730506855716207)
  ·
    refine ⟨49974442520595760283574311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33316295013730506855716207 49974442520595760283574311)
    ·
      refine ⟨74961663780893640425361467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49974442520595760283574311 74961663780893640425361467)
      ·
        refine ⟨112442495671340460638042201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74961663780893640425361467 112442495671340460638042201)
        ·
          refine ⟨84331871753505345478531651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112442495671340460638042201 84331871753505345478531651)
          ·
            refine ⟨126497807630258018217797477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84331871753505345478531651 126497807630258018217797477)
            ·
              refine ⟨23718338930673378415837027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126497807630258018217797477 23718338930673378415837027)
              ·
                refine ⟨35577508396010067623755541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23718338930673378415837027 35577508396010067623755541)
                ·
                  refine ⟨1667695706062971919863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35577508396010067623755541 1667695706062971919863541)
                  ·
                    refine ⟨156346472443403617487207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1667695706062971919863541 156346472443403617487207)
                    ·
                      rfl

theorem cell23_913451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].length) (baseStart_913451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913451 prefixEnd_913451 := by exact prefixLift 913451
  have htrace : WordTrace (prefixWord ++ tailWord_913451) baseStart_913451 baseEnd_913451 := by
    simpa [prefixWord, tailWord_913451, baseEnd_913451] using wordTrace_append hprefix tailTrace_913451
  have hstable : (prefixWord ++ tailWord_913451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913451).length < 2 ^ (prefixWord ++ tailWord_913451).sum := by decide
  have hdescent : baseEnd_913451 < baseStart_913451 := by decide
  rcases family_descends (prefixWord ++ tailWord_913451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913468 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_913468 : Nat := 118140960795 + 913468 * 2 ^ 59
def prefixEnd_913468 : Nat := 4983230072969 + 3 ^ 40 * 913468 * 2
def baseEnd_913468 : Nat := 156349382167112428649681

theorem tailTrace_913468 : CollatzResearch.WordTrace tailWord_913468 prefixEnd_913468 156349382167112428649681 := by
  unfold tailWord_913468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658457527334459379542529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22211276703112612506056705 16658457527334459379542529)
  ·
    refine ⟨12493843145500844534656897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16658457527334459379542529 12493843145500844534656897)
    ·
      refine ⟨9370382359125633400992673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12493843145500844534656897 9370382359125633400992673)
      ·
        refine ⟨7027786769344225050744505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9370382359125633400992673 7027786769344225050744505)
        ·
          refine ⟨5270840077008168788058379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7027786769344225050744505 5270840077008168788058379)
          ·
            refine ⟨7906260115512253182087569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270840077008168788058379 7906260115512253182087569)
            ·
              refine ⟨5929695086634189886565677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906260115512253182087569 5929695086634189886565677)
              ·
                refine ⟨2223635657487821207462129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5929695086634189886565677 2223635657487821207462129)
                ·
                  refine ⟨1667726743115865905596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223635657487821207462129 1667726743115865905596597)
                  ·
                    refine ⟨156349382167112428649681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1667726743115865905596597 156349382167112428649681)
                    ·
                      rfl

theorem cell23_913468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_913468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913468 prefixEnd_913468 := by exact prefixLift 913468
  have htrace : WordTrace (prefixWord ++ tailWord_913468) baseStart_913468 baseEnd_913468 := by
    simpa [prefixWord, tailWord_913468, baseEnd_913468] using wordTrace_append hprefix tailTrace_913468
  have hstable : (prefixWord ++ tailWord_913468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913468).length < 2 ^ (prefixWord ++ tailWord_913468).sum := by decide
  have hdescent : baseEnd_913468 < baseStart_913468 := by decide
  rcases family_descends (prefixWord ++ tailWord_913468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913485 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_913485 : Nat := 118140960795 + 913485 * 2 ^ 59
def prefixEnd_913485 : Nat := 4983230072969 + 3 ^ 40 * 913485 * 2
def baseEnd_913485 : Nat := 156352291890821239812155

theorem tailTrace_913485 : CollatzResearch.WordTrace tailWord_913485 prefixEnd_913485 156352291890821239812155 := by
  unfold tailWord_913485
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317535095607330662453909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22211690063738220441635939 33317535095607330662453909)
  ·
    refine ⟨1561759457606593624802527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33317535095607330662453909 1561759457606593624802527)
    ·
      refine ⟨2342639186409890437203791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1561759457606593624802527 2342639186409890437203791)
      ·
        refine ⟨3513958779614835655805687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342639186409890437203791 3513958779614835655805687)
        ·
          refine ⟨5270938169422253483708531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513958779614835655805687 5270938169422253483708531)
          ·
            refine ⟨7906407254133380225562797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270938169422253483708531 7906407254133380225562797)
            ·
              refine ⟨2964902720300017584586049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7906407254133380225562797 2964902720300017584586049)
              ·
                refine ⟨2223677040225013188439537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964902720300017584586049 2223677040225013188439537)
                ·
                  refine ⟨1667757780168759891329653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223677040225013188439537 1667757780168759891329653)
                  ·
                    refine ⟨156352291890821239812155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1667757780168759891329653 156352291890821239812155)
                    ·
                      rfl

theorem cell23_913485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_913485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913485 prefixEnd_913485 := by exact prefixLift 913485
  have htrace : WordTrace (prefixWord ++ tailWord_913485) baseStart_913485 baseEnd_913485 := by
    simpa [prefixWord, tailWord_913485, baseEnd_913485] using wordTrace_append hprefix tailTrace_913485
  have hstable : (prefixWord ++ tailWord_913485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913485).length < 2 ^ (prefixWord ++ tailWord_913485).sum := by decide
  have hdescent : baseEnd_913485 < baseStart_913485 := by decide
  rcases family_descends (prefixWord ++ tailWord_913485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913508 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_913508 : Nat := 118140960795 + 913508 * 2 ^ 59
def prefixEnd_913508 : Nat := 4983230072969 + 3 ^ 40 * 913508 * 2
def baseEnd_913508 : Nat := 469068685727517129448859

theorem tailTrace_913508 : CollatzResearch.WordTrace tailWord_913508 prefixEnd_913508 469068685727517129448859 := by
  unfold tailWord_913508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659186987262002795270589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22212249316349337060360785 16659186987262002795270589)
  ·
    refine ⟨6247195120223251048226471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16659186987262002795270589 6247195120223251048226471)
    ·
      refine ⟨9370792680334876572339707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247195120223251048226471 9370792680334876572339707)
      ·
        refine ⟨14056189020502314858509561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370792680334876572339707 14056189020502314858509561)
        ·
          refine ⟨10542141765376736143882171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056189020502314858509561 10542141765376736143882171)
          ·
            refine ⟨15813212648065104215823257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542141765376736143882171 15813212648065104215823257)
            ·
              refine ⟨11859909486048828161867443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813212648065104215823257 11859909486048828161867443)
              ·
                refine ⟨17789864229073242242801165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859909486048828161867443 17789864229073242242801165)
                ·
                  refine ⟨6671199085902465841050437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17789864229073242242801165 6671199085902465841050437)
                  ·
                    refine ⟨1250849828606712345196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6671199085902465841050437 1250849828606712345196957)
                    ·
                      refine ⟨469068685727517129448859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250849828606712345196957 469068685727517129448859)
                      ·
                        rfl

theorem cell23_913508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_913508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913508 prefixEnd_913508 := by exact prefixLift 913508
  have htrace : WordTrace (prefixWord ++ tailWord_913508) baseStart_913508 baseEnd_913508 := by
    simpa [prefixWord, tailWord_913508, baseEnd_913508] using wordTrace_append hprefix tailTrace_913508
  have hstable : (prefixWord ++ tailWord_913508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913508).length < 2 ^ (prefixWord ++ tailWord_913508).sum := by decide
  have hdescent : baseEnd_913508 < baseStart_913508 := by decide
  rcases family_descends (prefixWord ++ tailWord_913508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913531 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_913531 : Nat := 118140960795 + 913531 * 2 ^ 59
def prefixEnd_913531 : Nat := 4983230072969 + 3 ^ 40 * 913531 * 2
def baseEnd_913531 : Nat := 469080495782570539461253

theorem tailTrace_913531 : CollatzResearch.WordTrace tailWord_913531 prefixEnd_913531 469080495782570539461253 := by
  unfold tailWord_913531
  simp only [CollatzResearch.WordTrace]
  refine ⟨33319212853440680518628447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22212808568960453679085631 33319212853440680518628447)
  ·
    refine ⟨49978819280161020777942671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33319212853440680518628447 49978819280161020777942671)
    ·
      refine ⟨74968228920241531166914007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49978819280161020777942671 74968228920241531166914007)
      ·
        refine ⟨112452343380362296750371011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74968228920241531166914007 112452343380362296750371011)
        ·
          refine ⟨168678515070543445125556517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112452343380362296750371011 168678515070543445125556517)
          ·
            refine ⟨31627221575726895961041847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168678515070543445125556517 31627221575726895961041847)
            ·
              refine ⟨47440832363590343941562771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31627221575726895961041847 47440832363590343941562771)
              ·
                refine ⟨71161248545385515912344157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47440832363590343941562771 71161248545385515912344157)
                ·
                  refine ⟨26685468204519568467129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71161248545385515912344157 26685468204519568467129059)
                  ·
                    refine ⟨40028202306779352700693589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26685468204519568467129059 40028202306779352700693589)
                    ·
                      refine ⟨469080495782570539461253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 40028202306779352700693589 469080495782570539461253)
                      ·
                        rfl

theorem cell23_913531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_913531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913531 prefixEnd_913531 := by exact prefixLift 913531
  have htrace : WordTrace (prefixWord ++ tailWord_913531) baseStart_913531 baseEnd_913531 := by
    simpa [prefixWord, tailWord_913531, baseEnd_913531] using wordTrace_append hprefix tailTrace_913531
  have hstable : (prefixWord ++ tailWord_913531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913531).length < 2 ^ (prefixWord ++ tailWord_913531).sum := by decide
  have hdescent : baseEnd_913531 < baseStart_913531 := by decide
  rcases family_descends (prefixWord ++ tailWord_913531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913555 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 3]
def baseStart_913555 : Nat := 118140960795 + 913555 * 2 ^ 59
def prefixEnd_913555 : Nat := 4983230072969 + 3 ^ 40 * 913555 * 2
def baseEnd_913555 : Nat := 469092819318278445561143

theorem tailTrace_913555 : CollatzResearch.WordTrace tailWord_913555 prefixEnd_913555 469092819318278445561143 := by
  unfold tailWord_913555
  simp only [CollatzResearch.WordTrace]
  refine ⟨33320088205353732617502119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22213392136902488411668079 33320088205353732617502119)
  ·
    refine ⟨49980132308030598926253179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33320088205353732617502119 49980132308030598926253179)
    ·
      refine ⟨74970198462045898389379769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49980132308030598926253179 74970198462045898389379769)
      ·
        refine ⟨56227648846534423792034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74970198462045898389379769 56227648846534423792034827)
        ·
          refine ⟨84341473269801635688052241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56227648846534423792034827 84341473269801635688052241)
          ·
            refine ⟨63256104952351226766039181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84341473269801635688052241 63256104952351226766039181)
            ·
              refine ⟨23721039357131710037264693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63256104952351226766039181 23721039357131710037264693)
              ·
                refine ⟨2223847439731097815993565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23721039357131710037264693 2223847439731097815993565)
                ·
                  refine ⟨833942789899161680997587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2223847439731097815993565 833942789899161680997587)
                  ·
                    refine ⟨1250914184848742521496381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 833942789899161680997587 1250914184848742521496381)
                    ·
                      refine ⟨469092819318278445561143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1250914184848742521496381 469092819318278445561143)
                      ·
                        rfl

theorem cell23_913555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_913555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913555 prefixEnd_913555 := by exact prefixLift 913555
  have htrace : WordTrace (prefixWord ++ tailWord_913555) baseStart_913555 baseEnd_913555 := by
    simpa [prefixWord, tailWord_913555, baseEnd_913555] using wordTrace_append hprefix tailTrace_913555
  have hstable : (prefixWord ++ tailWord_913555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913555).length < 2 ^ (prefixWord ++ tailWord_913555).sum := by decide
  have hdescent : baseEnd_913555 < baseStart_913555 := by decide
  rcases family_descends (prefixWord ++ tailWord_913555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913595 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 4]
def baseStart_913595 : Nat := 118140960795 + 913595 * 2 ^ 59
def prefixEnd_913595 : Nat := 4983230072969 + 3 ^ 40 * 913595 * 2
def baseEnd_913595 : Nat := 469113358544458289060959

theorem tailTrace_913595 : CollatzResearch.WordTrace tailWord_913595 prefixEnd_913595 469113358544458289060959 := by
  unfold tailWord_913595
  simp only [CollatzResearch.WordTrace]
  refine ⟨33321547125208819448958239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22214364750139212965972159 33321547125208819448958239)
  ·
    refine ⟨49982320687813229173437359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33321547125208819448958239 49982320687813229173437359)
    ·
      refine ⟨74973481031719843760156039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49982320687813229173437359 74973481031719843760156039)
      ·
        refine ⟨112460221547579765640234059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74973481031719843760156039 112460221547579765640234059)
        ·
          refine ⟨168690332321369648460351089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112460221547579765640234059 168690332321369648460351089)
          ·
            refine ⟨126517749241027236345263317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168690332321369648460351089 126517749241027236345263317)
            ·
              refine ⟨2965259747836575851842109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126517749241027236345263317 2965259747836575851842109)
              ·
                refine ⟨1111972405438715944440791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2965259747836575851842109 1111972405438715944440791)
                ·
                  refine ⟨1667958608158073916661187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111972405438715944440791 1667958608158073916661187)
                  ·
                    refine ⟨2501937912237110874991781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667958608158073916661187 2501937912237110874991781)
                    ·
                      refine ⟨469113358544458289060959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2501937912237110874991781 469113358544458289060959)
                      ·
                        rfl

theorem cell23_913595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 4].length) (baseStart_913595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913595 prefixEnd_913595 := by exact prefixLift 913595
  have htrace : WordTrace (prefixWord ++ tailWord_913595) baseStart_913595 baseEnd_913595 := by
    simpa [prefixWord, tailWord_913595, baseEnd_913595] using wordTrace_append hprefix tailTrace_913595
  have hstable : (prefixWord ++ tailWord_913595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913595).length < 2 ^ (prefixWord ++ tailWord_913595).sum := by decide
  have hdescent : baseEnd_913595 < baseStart_913595 := by decide
  rcases family_descends (prefixWord ++ tailWord_913595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913608 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_913608 : Nat := 118140960795 + 913608 * 2 ^ 59
def prefixEnd_913608 : Nat := 4983230072969 + 3 ^ 40 * 913608 * 2
def baseEnd_913608 : Nat := 469120033792966738198399

theorem tailTrace_913608 : CollatzResearch.WordTrace tailWord_913608 prefixEnd_913608 469120033792966738198399 := by
  unfold tailWord_913608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661010637080861334590739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22214680849441148446120985 16661010637080861334590739)
  ·
    refine ⟨24991515955621292001886109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16661010637080861334590739 24991515955621292001886109)
    ·
      refine ⟨9371818483357984500707291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24991515955621292001886109 9371818483357984500707291)
      ·
        refine ⟨14057727725036976751060937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9371818483357984500707291 14057727725036976751060937)
        ·
          refine ⟨10543295793777732563295703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14057727725036976751060937 10543295793777732563295703)
          ·
            refine ⟨15814943690666598844943555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543295793777732563295703 15814943690666598844943555)
            ·
              refine ⟨23722415535999898267415333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15814943690666598844943555 23722415535999898267415333)
              ·
                refine ⟨4447952912999980925140375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23722415535999898267415333 4447952912999980925140375)
                ·
                  refine ⟨6671929369499971387710563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447952912999980925140375 6671929369499971387710563)
                  ·
                    refine ⟨10007894054249957081565845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671929369499971387710563 10007894054249957081565845)
                    ·
                      refine ⟨469120033792966738198399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10007894054249957081565845 469120033792966738198399)
                      ·
                        rfl

theorem cell23_913608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_913608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913608 prefixEnd_913608 := by exact prefixLift 913608
  have htrace : WordTrace (prefixWord ++ tailWord_913608) baseStart_913608 baseEnd_913608 := by
    simpa [prefixWord, tailWord_913608, baseEnd_913608] using wordTrace_append hprefix tailTrace_913608
  have hstable : (prefixWord ++ tailWord_913608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913608).length < 2 ^ (prefixWord ++ tailWord_913608).sum := by decide
  have hdescent : baseEnd_913608 < baseStart_913608 := by decide
  rcases family_descends (prefixWord ++ tailWord_913608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913625 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_913625 : Nat := 118140960795 + 913625 * 2 ^ 59
def prefixEnd_913625 : Nat := 4983230072969 + 3 ^ 40 * 913625 * 2
def baseEnd_913625 : Nat := 469128762964093171685821

theorem tailTrace_913625 : CollatzResearch.WordTrace tailWord_913625 prefixEnd_913625 469128762964093171685821 := by
  unfold tailWord_913625
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322641315100134572550329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22215094210066756381700219 33322641315100134572550329)
  ·
    refine ⟨24991980986325100929412747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33322641315100134572550329 24991980986325100929412747)
    ·
      refine ⟨37487971479487651394119121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24991980986325100929412747 37487971479487651394119121)
      ·
        refine ⟨28115978609615738545589341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37487971479487651394119121 28115978609615738545589341)
        ·
          refine ⟨10543491978605901954596003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28115978609615738545589341 10543491978605901954596003)
          ·
            refine ⟨15815237967908852931894005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543491978605901954596003 15815237967908852931894005)
            ·
              refine ⟨1482678559491454962365063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15815237967908852931894005 1482678559491454962365063)
              ·
                refine ⟨2224017839237182443547595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482678559491454962365063 2224017839237182443547595)
                ·
                  refine ⟨3336026758855773665321393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224017839237182443547595 3336026758855773665321393)
                  ·
                    refine ⟨2502020069141830248991045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336026758855773665321393 2502020069141830248991045)
                    ·
                      refine ⟨469128762964093171685821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2502020069141830248991045 469128762964093171685821)
                      ·
                        rfl

theorem cell23_913625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_913625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913625 prefixEnd_913625 := by exact prefixLift 913625
  have htrace : WordTrace (prefixWord ++ tailWord_913625) baseStart_913625 baseEnd_913625 := by
    simpa [prefixWord, tailWord_913625, baseEnd_913625] using wordTrace_append hprefix tailTrace_913625
  have hstable : (prefixWord ++ tailWord_913625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913625).length < 2 ^ (prefixWord ++ tailWord_913625).sum := by decide
  have hdescent : baseEnd_913625 < baseStart_913625 := by decide
  rcases family_descends (prefixWord ++ tailWord_913625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913629 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_913629 : Nat := 118140960795 + 913629 * 2 ^ 59
def prefixEnd_913629 : Nat := 4983230072969 + 3 ^ 40 * 913629 * 2
def baseEnd_913629 : Nat := 469130816886711156035803

theorem tailTrace_913629 : CollatzResearch.WordTrace tailWord_913629 prefixEnd_913629 469130816886711156035803 := by
  unfold tailWord_913629
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322787207085643255695941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22215191471390428837130627 33322787207085643255695941)
  ·
    refine ⟨6248022601328558110442989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33322787207085643255695941 6248022601328558110442989)
    ·
      refine ⟨2343008475498209291416121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6248022601328558110442989 2343008475498209291416121)
      ·
        refine ⟨1757256356623656968562091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2343008475498209291416121 1757256356623656968562091)
        ·
          refine ⟨2635884534935485452843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757256356623656968562091 2635884534935485452843137)
          ·
            refine ⟨1976913401201614089632353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635884534935485452843137 1976913401201614089632353)
            ·
              refine ⟨1482685050901210567224265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976913401201614089632353 1482685050901210567224265)
              ·
                refine ⟨1112013788175907925418199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482685050901210567224265 1112013788175907925418199)
                ·
                  refine ⟨1668020682263861888127299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112013788175907925418199 1668020682263861888127299)
                  ·
                    refine ⟨2502031023395792832190949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1668020682263861888127299 2502031023395792832190949)
                    ·
                      refine ⟨469130816886711156035803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2502031023395792832190949 469130816886711156035803)
                      ·
                        rfl

theorem cell23_913629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_913629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913629 prefixEnd_913629 := by exact prefixLift 913629
  have htrace : WordTrace (prefixWord ++ tailWord_913629) baseStart_913629 baseEnd_913629 := by
    simpa [prefixWord, tailWord_913629, baseEnd_913629] using wordTrace_append hprefix tailTrace_913629
  have hstable : (prefixWord ++ tailWord_913629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913629).length < 2 ^ (prefixWord ++ tailWord_913629).sum := by decide
  have hdescent : baseEnd_913629 < baseStart_913629 := by decide
  rcases family_descends (prefixWord ++ tailWord_913629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913632 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_913632 : Nat := 118140960795 + 913632 * 2 ^ 59
def prefixEnd_913632 : Nat := 4983230072969 + 3 ^ 40 * 913632 * 2
def baseEnd_913632 : Nat := 469132357328674644298289

theorem tailTrace_913632 : CollatzResearch.WordTrace tailWord_913632 prefixEnd_913632 469132357328674644298289 := by
  unfold tailWord_913632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661448313037387384027575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22215264417383183178703433 16661448313037387384027575)
  ·
    refine ⟨24992172469556081076041363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16661448313037387384027575 24992172469556081076041363)
    ·
      refine ⟨37488258704334121614062045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24992172469556081076041363 37488258704334121614062045)
      ·
        refine ⟨14058097014125295605273267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37488258704334121614062045 14058097014125295605273267)
        ·
          refine ⟨21087145521187943407909901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058097014125295605273267 21087145521187943407909901)
          ·
            refine ⟨7907679570445478777966213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21087145521187943407909901 7907679570445478777966213)
            ·
              refine ⟨1482689919458527270868665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7907679570445478777966213 1482689919458527270868665)
              ·
                refine ⟨1112017439593895453151499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482689919458527270868665 1112017439593895453151499)
                ·
                  refine ⟨1668026159390843179727249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112017439593895453151499 1668026159390843179727249)
                  ·
                    refine ⟨1251019619543132384795437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668026159390843179727249 1251019619543132384795437)
                    ·
                      refine ⟨469132357328674644298289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1251019619543132384795437 469132357328674644298289)
                      ·
                        rfl

theorem cell23_913632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_913632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913632 prefixEnd_913632 := by exact prefixLift 913632
  have htrace : WordTrace (prefixWord ++ tailWord_913632) baseStart_913632 baseEnd_913632 := by
    simpa [prefixWord, tailWord_913632, baseEnd_913632] using wordTrace_append hprefix tailTrace_913632
  have hstable : (prefixWord ++ tailWord_913632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913632).length < 2 ^ (prefixWord ++ tailWord_913632).sum := by decide
  have hdescent : baseEnd_913632 < baseStart_913632 := by decide
  rcases family_descends (prefixWord ++ tailWord_913632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913715 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_913715 : Nat := 118140960795 + 913715 * 2 ^ 59
def prefixEnd_913715 : Nat := 4983230072969 + 3 ^ 40 * 913715 * 2
def baseEnd_913715 : Nat := 469174976222997819560407

theorem tailTrace_913715 : CollatzResearch.WordTrace tailWord_913715 prefixEnd_913715 469174976222997819560407 := by
  unfold tailWord_913715
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325923884774079943326599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22217282589849386628884399 33325923884774079943326599)
  ·
    refine ⟨49988885827161119914989899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33325923884774079943326599 49988885827161119914989899)
    ·
      refine ⟨74983328740741679872484849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49988885827161119914989899 74983328740741679872484849)
      ·
        refine ⟨56237496555556259904363637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74983328740741679872484849 56237496555556259904363637)
        ·
          refine ⟨5272265302083399366034091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56237496555556259904363637 5272265302083399366034091)
          ·
            refine ⟨7908397953125099049051137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272265302083399366034091 7908397953125099049051137)
            ·
              refine ⟨5931298464843824286788353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908397953125099049051137 5931298464843824286788353)
              ·
                refine ⟨4448473848632868215091265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931298464843824286788353 4448473848632868215091265)
                ·
                  refine ⟨3336355386474651161318449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448473848632868215091265 3336355386474651161318449)
                  ·
                    refine ⟨2502266539855988370988837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336355386474651161318449 2502266539855988370988837)
                    ·
                      refine ⟨469174976222997819560407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2502266539855988370988837 469174976222997819560407)
                      ·
                        rfl

theorem cell23_913715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_913715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913715 prefixEnd_913715 := by exact prefixLift 913715
  have htrace : WordTrace (prefixWord ++ tailWord_913715) baseStart_913715 baseEnd_913715 := by
    simpa [prefixWord, tailWord_913715, baseEnd_913715] using wordTrace_append hprefix tailTrace_913715
  have hstable : (prefixWord ++ tailWord_913715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913715).length < 2 ^ (prefixWord ++ tailWord_913715).sum := by decide
  have hdescent : baseEnd_913715 < baseStart_913715 := by decide
  rcases family_descends (prefixWord ++ tailWord_913715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913815 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 8]
def baseStart_913815 : Nat := 118140960795 + 913815 * 2 ^ 59
def prefixEnd_913815 : Nat := 4983230072969 + 3 ^ 40 * 913815 * 2
def baseEnd_913815 : Nat := 52136258254271936478883

theorem tailTrace_913815 : CollatzResearch.WordTrace tailWord_913815 prefixEnd_913815 52136258254271936478883 := by
  unfold tailWord_913815
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329571184411797021966899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22219714122941198014644599 33329571184411797021966899)
  ·
    refine ⟨49994356776617695532950349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33329571184411797021966899 49994356776617695532950349)
    ·
      refine ⟨18747883791231635824856381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49994356776617695532950349 18747883791231635824856381)
      ·
        refine ⟨7030456421711863434321143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18747883791231635824856381 7030456421711863434321143)
        ·
          refine ⟨10545684632567795151481715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030456421711863434321143 10545684632567795151481715)
          ·
            refine ⟨15818526948851692727222573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545684632567795151481715 15818526948851692727222573)
            ·
              refine ⟨5931947605819384772708465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15818526948851692727222573 5931947605819384772708465)
              ·
                refine ⟨4448960704364538579531349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931947605819384772708465 4448960704364538579531349)
                ·
                  refine ⟨52136258254271936478883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4448960704364538579531349 52136258254271936478883)
                  ·
                    rfl

theorem cell23_913815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 8].length) (baseStart_913815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913815 prefixEnd_913815 := by exact prefixLift 913815
  have htrace : WordTrace (prefixWord ++ tailWord_913815) baseStart_913815 baseEnd_913815 := by
    simpa [prefixWord, tailWord_913815, baseEnd_913815] using wordTrace_append hprefix tailTrace_913815
  have hstable : (prefixWord ++ tailWord_913815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913815).length < 2 ^ (prefixWord ++ tailWord_913815).sum := by decide
  have hdescent : baseEnd_913815 < baseStart_913815 := by decide
  rcases family_descends (prefixWord ++ tailWord_913815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913849 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 6]
def baseStart_913849 : Nat := 118140960795 + 913849 * 2 ^ 59
def prefixEnd_913849 : Nat := 4983230072969 + 3 ^ 40 * 913849 * 2
def baseEnd_913849 : Nat := 52138198070077810587199

theorem tailTrace_913849 : CollatzResearch.WordTrace tailWord_913849 prefixEnd_913849 52138198070077810587199 := by
  unfold tailWord_913849
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330811266288620828704601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22220540844192413885803067 33330811266288620828704601)
  ·
    refine ⟨24998108449716465621528451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33330811266288620828704601 24998108449716465621528451)
    ·
      refine ⟨37497162674574698432292677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24998108449716465621528451 37497162674574698432292677)
      ·
        refine ⟨7030718001482755956054877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37497162674574698432292677 7030718001482755956054877)
        ·
          refine ⟨2636519250556033483520579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030718001482755956054877 2636519250556033483520579)
          ·
            refine ⟨3954778875834050225280869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636519250556033483520579 3954778875834050225280869)
            ·
              refine ⟨741521039218884417240163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3954778875834050225280869 741521039218884417240163)
              ·
                refine ⟨1112281558828326625860245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741521039218884417240163 1112281558828326625860245)
                ·
                  refine ⟨52138198070077810587199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1112281558828326625860245 52138198070077810587199)
                  ·
                    rfl

theorem cell23_913849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_913849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913849 prefixEnd_913849 := by exact prefixLift 913849
  have htrace : WordTrace (prefixWord ++ tailWord_913849) baseStart_913849 baseEnd_913849 := by
    simpa [prefixWord, tailWord_913849, baseEnd_913849] using wordTrace_append hprefix tailTrace_913849
  have hstable : (prefixWord ++ tailWord_913849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913849).length < 2 ^ (prefixWord ++ tailWord_913849).sum := by decide
  have hdescent : baseEnd_913849 < baseStart_913849 := by decide
  rcases family_descends (prefixWord ++ tailWord_913849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913919 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_913919 : Nat := 118140960795 + 913919 * 2 ^ 59
def prefixEnd_913919 : Nat := 4983230072969 + 3 ^ 40 * 913919 * 2
def baseEnd_913919 : Nat := 469279726276515021409469

theorem tailTrace_913919 : CollatzResearch.WordTrace tailWord_913919 prefixEnd_913919 469279726276515021409469 := by
  unfold tailWord_913919
  simp only [CollatzResearch.WordTrace]
  refine ⟨33333364376035022783752811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22222242917356681855835207 33333364376035022783752811)
  ·
    refine ⟨50000046564052534175629217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33333364376035022783752811 50000046564052534175629217)
    ·
      refine ⟨37500034923039400631721913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50000046564052534175629217 37500034923039400631721913)
      ·
        refine ⟨28125026192279550473791435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37500034923039400631721913 28125026192279550473791435)
        ·
          refine ⟨42187539288419325710687153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28125026192279550473791435 42187539288419325710687153)
          ·
            refine ⟨31640654466314494283015365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42187539288419325710687153 31640654466314494283015365)
            ·
              refine ⟨5932622712433967678065381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31640654466314494283015365 5932622712433967678065381)
              ·
                refine ⟨1112366758581368939637259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5932622712433967678065381 1112366758581368939637259)
                ·
                  refine ⟨1668550137872053409455889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112366758581368939637259 1668550137872053409455889)
                  ·
                    refine ⟨1251412603404040057091917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668550137872053409455889 1251412603404040057091917)
                    ·
                      refine ⟨469279726276515021409469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1251412603404040057091917 469279726276515021409469)
                      ·
                        rfl

theorem cell23_913919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_913919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_913919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_913919 prefixEnd_913919 := by exact prefixLift 913919
  have htrace : WordTrace (prefixWord ++ tailWord_913919) baseStart_913919 baseEnd_913919 := by
    simpa [prefixWord, tailWord_913919, baseEnd_913919] using wordTrace_append hprefix tailTrace_913919
  have hstable : (prefixWord ++ tailWord_913919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913919).length < 2 ^ (prefixWord ++ tailWord_913919).sum := by decide
  have hdescent : baseEnd_913919 < baseStart_913919 := by decide
  rcases family_descends (prefixWord ++ tailWord_913919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914042 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_914042 : Nat := 118140960795 + 914042 * 2 ^ 59
def prefixEnd_914042 : Nat := 4983230072969 + 3 ^ 40 * 914042 * 2
def baseEnd_914042 : Nat := 156447628132339346723801

theorem tailTrace_914042 : CollatzResearch.WordTrace tailWord_914042 prefixEnd_914042 156447628132339346723801 := by
  unfold tailWord_914042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334462638647353697620095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22225233703059609860320253 8334462638647353697620095)
  ·
    refine ⟨12501693957971030546430143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8334462638647353697620095 12501693957971030546430143)
    ·
      refine ⟨18752540936956545819645215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12501693957971030546430143 18752540936956545819645215)
      ·
        refine ⟨28128811405434818729467823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18752540936956545819645215 28128811405434818729467823)
        ·
          refine ⟨42193217108152228094201735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28128811405434818729467823 42193217108152228094201735)
          ·
            refine ⟨63289825662228342141302603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42193217108152228094201735 63289825662228342141302603)
            ·
              refine ⟨94934738493342513211953905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63289825662228342141302603 94934738493342513211953905)
              ·
                refine ⟨71201053870006884908965429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94934738493342513211953905 71201053870006884908965429)
                ·
                  refine ⟨6675098800313145460215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71201053870006884908965429 6675098800313145460215509)
                  ·
                    refine ⟨156447628132339346723801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6675098800313145460215509 156447628132339346723801)
                    ·
                      rfl

theorem cell23_914042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_914042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914042 prefixEnd_914042 := by exact prefixLift 914042
  have htrace : WordTrace (prefixWord ++ tailWord_914042) baseStart_914042 baseEnd_914042 := by
    simpa [prefixWord, tailWord_914042, baseEnd_914042] using wordTrace_append hprefix tailTrace_914042
  have hstable : (prefixWord ++ tailWord_914042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914042).length < 2 ^ (prefixWord ++ tailWord_914042).sum := by decide
  have hdescent : baseEnd_914042 < baseStart_914042 := by decide
  rcases family_descends (prefixWord ++ tailWord_914042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914089 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_914089 : Nat := 118140960795 + 914089 * 2 ^ 59
def prefixEnd_914089 : Nat := 4983230072969 + 3 ^ 40 * 914089 * 2
def baseEnd_914089 : Nat := 156455672662593118761229

theorem tailTrace_914089 : CollatzResearch.WordTrace tailWord_914089 prefixEnd_914089 156455672662593118761229 := by
  unfold tailWord_914089
  simp only [CollatzResearch.WordTrace]
  refine ⟨33339564785419141817441321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22226376523612761211627547 33339564785419141817441321)
  ·
    refine ⟨25004673589064356363080991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33339564785419141817441321 25004673589064356363080991)
    ·
      refine ⟨37507010383596534544621487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25004673589064356363080991 37507010383596534544621487)
      ·
        refine ⟨56260515575394801816932231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37507010383596534544621487 56260515575394801816932231)
        ·
          refine ⟨84390773363092202725398347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56260515575394801816932231 84390773363092202725398347)
          ·
            refine ⟨126586160044638304088097521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84390773363092202725398347 126586160044638304088097521)
            ·
              refine ⟨94939620033478728066073141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126586160044638304088097521 94939620033478728066073141)
              ·
                refine ⟨8900589378138630756194357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94939620033478728066073141 8900589378138630756194357)
                ·
                  refine ⟨834430254200496633393221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8900589378138630756194357 834430254200496633393221)
                  ·
                    refine ⟨156455672662593118761229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834430254200496633393221 156455672662593118761229)
                    ·
                      rfl

theorem cell23_914089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_914089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914089 prefixEnd_914089 := by exact prefixLift 914089
  have htrace : WordTrace (prefixWord ++ tailWord_914089) baseStart_914089 baseEnd_914089 := by
    simpa [prefixWord, tailWord_914089, baseEnd_914089] using wordTrace_append hprefix tailTrace_914089
  have hstable : (prefixWord ++ tailWord_914089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914089).length < 2 ^ (prefixWord ++ tailWord_914089).sum := by decide
  have hdescent : baseEnd_914089 < baseStart_914089 := by decide
  rcases family_descends (prefixWord ++ tailWord_914089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914093 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_914093 : Nat := 118140960795 + 914093 * 2 ^ 59
def prefixEnd_914093 : Nat := 4983230072969 + 3 ^ 40 * 914093 * 2
def baseEnd_914093 : Nat := 156456357303465780211223

theorem tailTrace_914093 : CollatzResearch.WordTrace tailWord_914093 prefixEnd_914093 156456357303465780211223 := by
  unfold tailWord_914093
  simp only [CollatzResearch.WordTrace]
  refine ⟨33339710677404650500586933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22226473784936433667057955 33339710677404650500586933)
  ·
    refine ⟨3125597876006685984430025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33339710677404650500586933 3125597876006685984430025)
    ·
      refine ⟨2344198407005014488322519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125597876006685984430025 2344198407005014488322519)
      ·
        refine ⟨3516297610507521732483779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344198407005014488322519 3516297610507521732483779)
        ·
          refine ⟨5274446415761282598725669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516297610507521732483779 5274446415761282598725669)
          ·
            refine ⟨988958702955240487261063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5274446415761282598725669 988958702955240487261063)
            ·
              refine ⟨1483438054432860730891595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988958702955240487261063 1483438054432860730891595)
              ·
                refine ⟨2225157081649291096337393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483438054432860730891595 2225157081649291096337393)
                ·
                  refine ⟨1668867811236968322253045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225157081649291096337393 1668867811236968322253045)
                  ·
                    refine ⟨156456357303465780211223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1668867811236968322253045 156456357303465780211223)
                    ·
                      rfl

theorem cell23_914093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_914093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914093 prefixEnd_914093 := by exact prefixLift 914093
  have htrace : WordTrace (prefixWord ++ tailWord_914093) baseStart_914093 baseEnd_914093 := by
    simpa [prefixWord, tailWord_914093, baseEnd_914093] using wordTrace_append hprefix tailTrace_914093
  have hstable : (prefixWord ++ tailWord_914093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914093).length < 2 ^ (prefixWord ++ tailWord_914093).sum := by decide
  have hdescent : baseEnd_914093 < baseStart_914093 := by decide
  rcases family_descends (prefixWord ++ tailWord_914093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914109 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_914109 : Nat := 118140960795 + 914109 * 2 ^ 59
def prefixEnd_914109 : Nat := 4983230072969 + 3 ^ 40 * 914109 * 2
def baseEnd_914109 : Nat := 469377287600869278033595

theorem tailTrace_914109 : CollatzResearch.WordTrace tailWord_914109 prefixEnd_914109 469377287600869278033595 := by
  unfold tailWord_914109
  simp only [CollatzResearch.WordTrace]
  refine ⟨33340294245346685233169381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22226862830231123488779587 33340294245346685233169381)
  ·
    refine ⟨6251305171002503481219259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33340294245346685233169381 6251305171002503481219259)
    ·
      refine ⟨9376957756503755221828889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251305171002503481219259 9376957756503755221828889)
      ·
        refine ⟨7032718317377816416371667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9376957756503755221828889 7032718317377816416371667)
        ·
          refine ⟨10549077476066724624557501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032718317377816416371667 10549077476066724624557501)
          ·
            refine ⟨3955904053525021734209063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10549077476066724624557501 3955904053525021734209063)
            ·
              refine ⟨5933856080287532601313595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955904053525021734209063 5933856080287532601313595)
              ·
                refine ⟨8900784120431298901970393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5933856080287532601313595 8900784120431298901970393)
                ·
                  refine ⟨6675588090323474176477795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8900784120431298901970393 6675588090323474176477795)
                  ·
                    refine ⟨10013382135485211264716693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675588090323474176477795 10013382135485211264716693)
                    ·
                      refine ⟨469377287600869278033595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10013382135485211264716693 469377287600869278033595)
                      ·
                        rfl

theorem cell23_914109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_914109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914109 prefixEnd_914109 := by exact prefixLift 914109
  have htrace : WordTrace (prefixWord ++ tailWord_914109) baseStart_914109 baseEnd_914109 := by
    simpa [prefixWord, tailWord_914109, baseEnd_914109] using wordTrace_append hprefix tailTrace_914109
  have hstable : (prefixWord ++ tailWord_914109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914109).length < 2 ^ (prefixWord ++ tailWord_914109).sum := by decide
  have hdescent : baseEnd_914109 < baseStart_914109 := by decide
  rcases family_descends (prefixWord ++ tailWord_914109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914119 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 6]
def baseStart_914119 : Nat := 118140960795 + 914119 * 2 ^ 59
def prefixEnd_914119 : Nat := 4983230072969 + 3 ^ 40 * 914119 * 2
def baseEnd_914119 : Nat := 52153602489712693212061

theorem tailTrace_914119 : CollatzResearch.WordTrace tailWord_914119 prefixEnd_914119 52153602489712693212061 := by
  unfold tailWord_914119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33340658975310456941033411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22227105983540304627355607 33340658975310456941033411)
  ·
    refine ⟨50010988462965685411550117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33340658975310456941033411 50010988462965685411550117)
    ·
      refine ⟨9377060336806066014665647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50010988462965685411550117 9377060336806066014665647)
      ·
        refine ⟨14065590505209099021998471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377060336806066014665647 14065590505209099021998471)
        ·
          refine ⟨21098385757813648532997707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14065590505209099021998471 21098385757813648532997707)
          ·
            refine ⟨31647578636720472799496561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21098385757813648532997707 31647578636720472799496561)
            ·
              refine ⟨23735683977540354599622421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31647578636720472799496561 23735683977540354599622421)
              ·
                refine ⟨1112610186447204121857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23735683977540354599622421 1112610186447204121857301)
                ·
                  refine ⟨52153602489712693212061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1112610186447204121857301 52153602489712693212061)
                  ·
                    rfl

theorem cell23_914119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 6].length) (baseStart_914119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914119 prefixEnd_914119 := by exact prefixLift 914119
  have htrace : WordTrace (prefixWord ++ tailWord_914119) baseStart_914119 baseEnd_914119 := by
    simpa [prefixWord, tailWord_914119, baseEnd_914119] using wordTrace_append hprefix tailTrace_914119
  have hstable : (prefixWord ++ tailWord_914119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914119).length < 2 ^ (prefixWord ++ tailWord_914119).sum := by decide
  have hdescent : baseEnd_914119 < baseStart_914119 := by decide
  rcases family_descends (prefixWord ++ tailWord_914119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914173 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_914173 : Nat := 118140960795 + 914173 * 2 ^ 59
def prefixEnd_914173 : Nat := 4983230072969 + 3 ^ 40 * 914173 * 2
def baseEnd_914173 : Nat := 469410150362757027633301

theorem tailTrace_914173 : CollatzResearch.WordTrace tailWord_914173 prefixEnd_914173 469410150362757027633301 := by
  unfold tailWord_914173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342628517114824163499173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22228419011409882775666115 33342628517114824163499173)
  ·
    refine ⟨6251742846959029530656095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33342628517114824163499173 6251742846959029530656095)
    ·
      refine ⟨9377614270438544295984143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251742846959029530656095 9377614270438544295984143)
      ·
        refine ⟨14066421405657816443976215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377614270438544295984143 14066421405657816443976215)
        ·
          refine ⟨21099632108486724665964323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066421405657816443976215 21099632108486724665964323)
          ·
            refine ⟨31649448162730086998946485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099632108486724665964323 31649448162730086998946485)
            ·
              refine ⟨2967135765255945656151233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31649448162730086998946485 2967135765255945656151233)
              ·
                refine ⟨2225351823941959242113425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967135765255945656151233 2225351823941959242113425)
                ·
                  refine ⟨1669013867956469431585069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225351823941959242113425 1669013867956469431585069)
                  ·
                    refine ⟨625880200483676036844401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669013867956469431585069 625880200483676036844401)
                    ·
                      refine ⟨469410150362757027633301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 625880200483676036844401 469410150362757027633301)
                      ·
                        rfl

theorem cell23_914173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_914173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914173 prefixEnd_914173 := by exact prefixLift 914173
  have htrace : WordTrace (prefixWord ++ tailWord_914173) baseStart_914173 baseEnd_914173 := by
    simpa [prefixWord, tailWord_914173, baseEnd_914173] using wordTrace_append hprefix tailTrace_914173
  have hstable : (prefixWord ++ tailWord_914173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914173).length < 2 ^ (prefixWord ++ tailWord_914173).sum := by decide
  have hdescent : baseEnd_914173 < baseStart_914173 := by decide
  rcases family_descends (prefixWord ++ tailWord_914173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914186 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_914186 : Nat := 118140960795 + 914186 * 2 ^ 59
def prefixEnd_914186 : Nat := 4983230072969 + 3 ^ 40 * 914186 * 2
def baseEnd_914186 : Nat := 469416825611265476770741

theorem tailTrace_914186 : CollatzResearch.WordTrace tailWord_914186 prefixEnd_914186 469416825611265476770741 := by
  unfold tailWord_914186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335775666516931845930603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22228735110711818255814941 8335775666516931845930603)
  ·
    refine ⟨12503663499775397768895905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8335775666516931845930603 12503663499775397768895905)
    ·
      refine ⟨9377747624831548326671929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12503663499775397768895905 9377747624831548326671929)
      ·
        refine ⟨7033310718623661245003947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377747624831548326671929 7033310718623661245003947)
        ·
          refine ⟨10549966077935491867505921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033310718623661245003947 10549966077935491867505921)
          ·
            refine ⟨7912474558451618900629441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549966077935491867505921 7912474558451618900629441)
            ·
              refine ⟨5934355918838714175472081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912474558451618900629441 5934355918838714175472081)
              ·
                refine ⟨4450766939129035631604061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934355918838714175472081 4450766939129035631604061)
                ·
                  refine ⟨1669037602173388361851523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4450766939129035631604061 1669037602173388361851523)
                  ·
                    refine ⟨2503556403260082542777285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669037602173388361851523 2503556403260082542777285)
                    ·
                      refine ⟨469416825611265476770741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2503556403260082542777285 469416825611265476770741)
                      ·
                        rfl

theorem cell23_914186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_914186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914186 prefixEnd_914186 := by exact prefixLift 914186
  have htrace : WordTrace (prefixWord ++ tailWord_914186) baseStart_914186 baseEnd_914186 := by
    simpa [prefixWord, tailWord_914186, baseEnd_914186] using wordTrace_append hprefix tailTrace_914186
  have hstable : (prefixWord ++ tailWord_914186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914186).length < 2 ^ (prefixWord ++ tailWord_914186).sum := by decide
  have hdescent : baseEnd_914186 < baseStart_914186 := by decide
  rcases family_descends (prefixWord ++ tailWord_914186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914209 : List Nat := [1, 2, 3, 2, 1, 2, 1, 11]
def baseStart_914209 : Nat := 118140960795 + 914209 * 2 ^ 59
def prefixEnd_914209 : Nat := 4983230072969 + 3 ^ 40 * 914209 * 2
def baseEnd_914209 : Nat := 17386245765419218029005

theorem tailTrace_914209 : CollatzResearch.WordTrace tailWord_914209 prefixEnd_914209 17386245765419218029005 := by
  unfold tailWord_914209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343941544984402311809681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22229294363322934874539787 33343941544984402311809681)
  ·
    refine ⟨25007956158738301733857261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33343941544984402311809681 25007956158738301733857261)
    ·
      refine ⟨9377983559526863150196473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25007956158738301733857261 9377983559526863150196473)
      ·
        refine ⟨7033487669645147362647355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377983559526863150196473 7033487669645147362647355)
        ·
          refine ⟨10550231504467721043971033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033487669645147362647355 10550231504467721043971033)
          ·
            refine ⟨7912673628350790782978275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10550231504467721043971033 7912673628350790782978275)
            ·
              refine ⟨11869010442526186174467413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912673628350790782978275 11869010442526186174467413)
              ·
                refine ⟨17386245765419218029005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11869010442526186174467413 17386245765419218029005)
                ·
                  rfl

theorem cell23_914209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 11].length) (baseStart_914209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914209 prefixEnd_914209 := by exact prefixLift 914209
  have htrace : WordTrace (prefixWord ++ tailWord_914209) baseStart_914209 baseEnd_914209 := by
    simpa [prefixWord, tailWord_914209, baseEnd_914209] using wordTrace_append hprefix tailTrace_914209
  have hstable : (prefixWord ++ tailWord_914209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914209).length < 2 ^ (prefixWord ++ tailWord_914209).sum := by decide
  have hdescent : baseEnd_914209 < baseStart_914209 := by decide
  rcases family_descends (prefixWord ++ tailWord_914209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914236 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_914236 : Nat := 118140960795 + 914236 * 2 ^ 59
def prefixEnd_914236 : Nat := 4983230072969 + 3 ^ 40 * 914236 * 2
def baseEnd_914236 : Nat := 469442499643990281145511

theorem tailTrace_914236 : CollatzResearch.WordTrace tailWord_914236 prefixEnd_914236 469442499643990281145511 := by
  unfold tailWord_914236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672463157943292961521281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22229950877257723948695041 16672463157943292961521281)
  ·
    refine ⟨12504347368457469721140961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16672463157943292961521281 12504347368457469721140961)
    ·
      refine ⟨9378260526343102290855721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12504347368457469721140961 9378260526343102290855721)
      ·
        refine ⟨7033695394757326718141791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9378260526343102290855721 7033695394757326718141791)
        ·
          refine ⟨10550543092135990077212687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033695394757326718141791 10550543092135990077212687)
          ·
            refine ⟨15825814638203985115819031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550543092135990077212687 15825814638203985115819031)
            ·
              refine ⟨23738721957305977673728547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15825814638203985115819031 23738721957305977673728547)
              ·
                refine ⟨35608082935958966510592821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23738721957305977673728547 35608082935958966510592821)
                ·
                  refine ⟨3338257775246153110368077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35608082935958966510592821 3338257775246153110368077)
                  ·
                    refine ⟨1251846665717307416388029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338257775246153110368077 1251846665717307416388029)
                    ·
                      refine ⟨469442499643990281145511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1251846665717307416388029 469442499643990281145511)
                      ·
                        rfl

theorem cell23_914236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_914236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914236 prefixEnd_914236 := by exact prefixLift 914236
  have htrace : WordTrace (prefixWord ++ tailWord_914236) baseStart_914236 baseEnd_914236 := by
    simpa [prefixWord, tailWord_914236, baseEnd_914236] using wordTrace_append hprefix tailTrace_914236
  have hstable : (prefixWord ++ tailWord_914236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914236).length < 2 ^ (prefixWord ++ tailWord_914236).sum := by decide
  have hdescent : baseEnd_914236 < baseStart_914236 := by decide
  rcases family_descends (prefixWord ++ tailWord_914236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914274 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_914274 : Nat := 118140960795 + 914274 * 2 ^ 59
def prefixEnd_914274 : Nat := 4983230072969 + 3 ^ 40 * 914274 * 2
def baseEnd_914274 : Nat := 469462011908861132470337

theorem tailTrace_914274 : CollatzResearch.WordTrace tailWord_914274 prefixEnd_914274 469462011908861132470337 := by
  unfold tailWord_914274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336578072437229603231469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22230874859832612275283917 8336578072437229603231469)
  ·
    refine ⟨3126216777163961101211801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8336578072437229603231469 3126216777163961101211801)
    ·
      refine ⟨2344662582872970825908851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3126216777163961101211801 2344662582872970825908851)
      ·
        refine ⟨3516993874309456238863277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344662582872970825908851 3516993874309456238863277)
        ·
          refine ⟨1318872702866046089573729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3516993874309456238863277 1318872702866046089573729)
          ·
            refine ⟨989154527149534567180297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318872702866046089573729 989154527149534567180297)
            ·
              refine ⟨741865895362150925385223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989154527149534567180297 741865895362150925385223)
              ·
                refine ⟨1112798843043226388077835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741865895362150925385223 1112798843043226388077835)
                ·
                  refine ⟨1669198264564839582116753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112798843043226388077835 1669198264564839582116753)
                  ·
                    refine ⟨1251898698423629686587565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669198264564839582116753 1251898698423629686587565)
                    ·
                      refine ⟨469462011908861132470337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1251898698423629686587565 469462011908861132470337)
                      ·
                        rfl

theorem cell23_914274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_914274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914274 prefixEnd_914274 := by exact prefixLift 914274
  have htrace : WordTrace (prefixWord ++ tailWord_914274) baseStart_914274 baseEnd_914274 := by
    simpa [prefixWord, tailWord_914274, baseEnd_914274] using wordTrace_append hprefix tailTrace_914274
  have hstable : (prefixWord ++ tailWord_914274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914274).length < 2 ^ (prefixWord ++ tailWord_914274).sum := by decide
  have hdescent : baseEnd_914274 < baseStart_914274 := by decide
  rcases family_descends (prefixWord ++ tailWord_914274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914296 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_914296 : Nat := 118140960795 + 914296 * 2 ^ 59
def prefixEnd_914296 : Nat := 4983230072969 + 3 ^ 40 * 914296 * 2
def baseEnd_914296 : Nat := 469473308483260046395235

theorem tailTrace_914296 : CollatzResearch.WordTrace tailWord_914296 prefixEnd_914296 469473308483260046395235 := by
  unfold tailWord_914296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673557347834608085113371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22231409797112810780151161 16673557347834608085113371)
  ·
    refine ⟨25010336021751912127670057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16673557347834608085113371 25010336021751912127670057)
    ·
      refine ⟨18757752016313934095752543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25010336021751912127670057 18757752016313934095752543)
      ·
        refine ⟨28136628024470901143628815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18757752016313934095752543 28136628024470901143628815)
        ·
          refine ⟨42204942036706351715443223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28136628024470901143628815 42204942036706351715443223)
          ·
            refine ⟨63307413055059527573164835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42204942036706351715443223 63307413055059527573164835)
            ·
              refine ⟨94961119582589291359747253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63307413055059527573164835 94961119582589291359747253)
              ·
                refine ⟨8902604960867746064976305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94961119582589291359747253 8902604960867746064976305)
                ·
                  refine ⟨6676953720650809548732229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902604960867746064976305 6676953720650809548732229)
                  ·
                    refine ⟨1251928822622026790387293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676953720650809548732229 1251928822622026790387293)
                    ·
                      refine ⟨469473308483260046395235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1251928822622026790387293 469473308483260046395235)
                      ·
                        rfl

theorem cell23_914296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_914296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914296 prefixEnd_914296 := by exact prefixLift 914296
  have htrace : WordTrace (prefixWord ++ tailWord_914296) baseStart_914296 baseEnd_914296 := by
    simpa [prefixWord, tailWord_914296, baseEnd_914296] using wordTrace_append hprefix tailTrace_914296
  have hstable : (prefixWord ++ tailWord_914296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914296).length < 2 ^ (prefixWord ++ tailWord_914296).sum := by decide
  have hdescent : baseEnd_914296 < baseStart_914296 := by decide
  rcases family_descends (prefixWord ++ tailWord_914296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914316 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 7]
def baseStart_914316 : Nat := 118140960795 + 914316 * 2 ^ 59
def prefixEnd_914316 : Nat := 4983230072969 + 3 ^ 40 * 914316 * 2
def baseEnd_914316 : Nat := 52164842010705552016127

theorem tailTrace_914316 : CollatzResearch.WordTrace tailWord_914316 prefixEnd_914316 52164842010705552016127 := by
  unfold tailWord_914316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673922077798379792977401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22231896103731173057303201 16673922077798379792977401)
  ·
    refine ⟨12505441558348784844733051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16673922077798379792977401 12505441558348784844733051)
    ·
      refine ⟨18758162337523177267099577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505441558348784844733051 18758162337523177267099577)
      ·
        refine ⟨14068621753142382950324683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18758162337523177267099577 14068621753142382950324683)
        ·
          refine ⟨21102932629713574425487025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14068621753142382950324683 21102932629713574425487025)
          ·
            refine ⟨15827199472285180819115269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21102932629713574425487025 15827199472285180819115269)
            ·
              refine ⟨2967599901053471403584113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15827199472285180819115269 2967599901053471403584113)
              ·
                refine ⟨2225699925790103552688085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967599901053471403584113 2225699925790103552688085)
                ·
                  refine ⟨52164842010705552016127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2225699925790103552688085 52164842010705552016127)
                  ·
                    rfl

theorem cell23_914316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_914316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914316 prefixEnd_914316 := by exact prefixLift 914316
  have htrace : WordTrace (prefixWord ++ tailWord_914316) baseStart_914316 baseEnd_914316 := by
    simpa [prefixWord, tailWord_914316, baseEnd_914316] using wordTrace_append hprefix tailTrace_914316
  have hstable : (prefixWord ++ tailWord_914316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914316).length < 2 ^ (prefixWord ++ tailWord_914316).sum := by decide
  have hdescent : baseEnd_914316 < baseStart_914316 := by decide
  rcases family_descends (prefixWord ++ tailWord_914316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914383 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_914383 : Nat := 118140960795 + 914383 * 2 ^ 59
def prefixEnd_914383 : Nat := 4983230072969 + 3 ^ 40 * 914383 * 2
def baseEnd_914383 : Nat := 469517981300201206007335

theorem tailTrace_914383 : CollatzResearch.WordTrace tailWord_914383 prefixEnd_914383 469517981300201206007335 := by
  unfold tailWord_914383
  simp only [CollatzResearch.WordTrace]
  refine ⟨33350287846354030028643803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22233525230902686685762535 33350287846354030028643803)
  ·
    refine ⟨50025431769531045042965705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33350287846354030028643803 50025431769531045042965705)
    ·
      refine ⟨37519073827148283782224279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50025431769531045042965705 37519073827148283782224279)
      ·
        refine ⟨56278610740722425673336419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37519073827148283782224279 56278610740722425673336419)
        ·
          refine ⟨84417916111083638510004629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56278610740722425673336419 84417916111083638510004629)
          ·
            refine ⟨3957089817707045555156467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84417916111083638510004629 3957089817707045555156467)
            ·
              refine ⟨5935634726560568332734701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957089817707045555156467 5935634726560568332734701)
              ·
                refine ⟨2225863022460213124775513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5935634726560568332734701 2225863022460213124775513)
                ·
                  refine ⟨1669397266845159843581635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225863022460213124775513 1669397266845159843581635)
                  ·
                    refine ⟨2504095900267739765372453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669397266845159843581635 2504095900267739765372453)
                    ·
                      refine ⟨469517981300201206007335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2504095900267739765372453 469517981300201206007335)
                      ·
                        rfl

theorem cell23_914383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_914383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914383 prefixEnd_914383 := by exact prefixLift 914383
  have htrace : WordTrace (prefixWord ++ tailWord_914383) baseStart_914383 baseEnd_914383 := by
    simpa [prefixWord, tailWord_914383, baseEnd_914383] using wordTrace_append hprefix tailTrace_914383
  have hstable : (prefixWord ++ tailWord_914383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914383).length < 2 ^ (prefixWord ++ tailWord_914383).sum := by decide
  have hdescent : baseEnd_914383 < baseStart_914383 := by decide
  rcases family_descends (prefixWord ++ tailWord_914383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914390 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_914390 : Nat := 118140960795 + 914390 * 2 ^ 59
def prefixEnd_914390 : Nat := 4983230072969 + 3 ^ 40 * 914390 * 2
def baseEnd_914390 : Nat := 469521575664782678619803

theorem tailTrace_914390 : CollatzResearch.WordTrace tailWord_914390 prefixEnd_914390 469521575664782678619803 := by
  unfold tailWord_914390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084408947333041889009289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22233695438219113482765749 2084408947333041889009289)
  ·
    refine ⟨1563306710499781416756967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2084408947333041889009289 1563306710499781416756967)
    ·
      refine ⟨2344960065749672125135451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563306710499781416756967 2344960065749672125135451)
      ·
        refine ⟨3517440098624508187703177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344960065749672125135451 3517440098624508187703177)
        ·
          refine ⟨2638080073968381140777383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3517440098624508187703177 2638080073968381140777383)
          ·
            refine ⟨3957120110952571711166075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638080073968381140777383 3957120110952571711166075)
            ·
              refine ⟨5935680166428857566749113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957120110952571711166075 5935680166428857566749113)
              ·
                refine ⟨4451760124821643175061835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935680166428857566749113 4451760124821643175061835)
                ·
                  refine ⟨6677640187232464762592753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451760124821643175061835 6677640187232464762592753)
                  ·
                    refine ⟨5008230140424348571944565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677640187232464762592753 5008230140424348571944565)
                    ·
                      refine ⟨469521575664782678619803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5008230140424348571944565 469521575664782678619803)
                      ·
                        rfl

theorem cell23_914390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_914390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914390 prefixEnd_914390 := by exact prefixLift 914390
  have htrace : WordTrace (prefixWord ++ tailWord_914390) baseStart_914390 baseEnd_914390 := by
    simpa [prefixWord, tailWord_914390, baseEnd_914390] using wordTrace_append hprefix tailTrace_914390
  have hstable : (prefixWord ++ tailWord_914390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914390).length < 2 ^ (prefixWord ++ tailWord_914390).sum := by decide
  have hdescent : baseEnd_914390 < baseStart_914390 := by decide
  rcases family_descends (prefixWord ++ tailWord_914390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914467 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 3]
def baseStart_914467 : Nat := 118140960795 + 914467 * 2 ^ 59
def prefixEnd_914467 : Nat := 4983230072969 + 3 ^ 40 * 914467 * 2
def baseEnd_914467 : Nat := 469561113675178877356949

theorem tailTrace_914467 : CollatzResearch.WordTrace tailWord_914467 prefixEnd_914467 469561113675178877356949 := by
  unfold tailWord_914467
  simp only [CollatzResearch.WordTrace]
  refine ⟨33353351578049712374701655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22235567718699808249801103 33353351578049712374701655)
  ·
    refine ⟨50030027367074568562052483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33353351578049712374701655 50030027367074568562052483)
    ·
      refine ⟨75045041050611852843078725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50030027367074568562052483 75045041050611852843078725)
      ·
        refine ⟨14070945196989722408077261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75045041050611852843078725 14070945196989722408077261)
        ·
          refine ⟨5276604448871145903028973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14070945196989722408077261 5276604448871145903028973)
          ·
            refine ⟨1978726668326679713635865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5276604448871145903028973 1978726668326679713635865)
            ·
              refine ⟨1484045001245009785226899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978726668326679713635865 1484045001245009785226899)
              ·
                refine ⟨2226067501867514677840349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484045001245009785226899 2226067501867514677840349)
                ·
                  refine ⟨834775313200318004190131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2226067501867514677840349 834775313200318004190131)
                  ·
                    refine ⟨1252162969800477006285197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834775313200318004190131 1252162969800477006285197)
                    ·
                      refine ⟨469561113675178877356949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252162969800477006285197 469561113675178877356949)
                      ·
                        rfl

theorem cell23_914467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_914467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914467 prefixEnd_914467 := by exact prefixLift 914467
  have htrace : WordTrace (prefixWord ++ tailWord_914467) baseStart_914467 baseEnd_914467 := by
    simpa [prefixWord, tailWord_914467, baseEnd_914467] using wordTrace_append hprefix tailTrace_914467
  have hstable : (prefixWord ++ tailWord_914467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914467).length < 2 ^ (prefixWord ++ tailWord_914467).sum := by decide
  have hdescent : baseEnd_914467 < baseStart_914467 := by decide
  rcases family_descends (prefixWord ++ tailWord_914467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914484 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_914484 : Nat := 118140960795 + 914484 * 2 ^ 59
def prefixEnd_914484 : Nat := 4983230072969 + 3 ^ 40 * 914484 * 2
def baseEnd_914484 : Nat := 469569842846305310844371

theorem tailTrace_914484 : CollatzResearch.WordTrace tailWord_914484 prefixEnd_914484 469569842846305310844371 := by
  unfold tailWord_914484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676985809494062139035253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22235981079325416185380337 16676985809494062139035253)
  ·
    refine ⟨1563467419640068325534555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16676985809494062139035253 1563467419640068325534555)
    ·
      refine ⟨2345201129460102488301833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563467419640068325534555 2345201129460102488301833)
      ·
        refine ⟨1758900847095076866226375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345201129460102488301833 1758900847095076866226375)
        ·
          refine ⟨2638351270642615299339563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758900847095076866226375 2638351270642615299339563)
          ·
            refine ⟨3957526905963922949009345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638351270642615299339563 3957526905963922949009345)
            ·
              refine ⟨2968145179472942211757009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957526905963922949009345 2968145179472942211757009)
              ·
                refine ⟨2226108884604706658817757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968145179472942211757009 2226108884604706658817757)
                ·
                  refine ⟨834790831726764997056659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2226108884604706658817757 834790831726764997056659)
                  ·
                    refine ⟨1252186247590147495584989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834790831726764997056659 1252186247590147495584989)
                    ·
                      refine ⟨469569842846305310844371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252186247590147495584989 469569842846305310844371)
                      ·
                        rfl

theorem cell23_914484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_914484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914484 prefixEnd_914484 := by exact prefixLift 914484
  have htrace : WordTrace (prefixWord ++ tailWord_914484) baseStart_914484 baseEnd_914484 := by
    simpa [prefixWord, tailWord_914484, baseEnd_914484] using wordTrace_append hprefix tailTrace_914484
  have hstable : (prefixWord ++ tailWord_914484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914484).length < 2 ^ (prefixWord ++ tailWord_914484).sum := by decide
  have hdescent : baseEnd_914484 < baseStart_914484 := by decide
  rcases family_descends (prefixWord ++ tailWord_914484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914490 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_914490 : Nat := 118140960795 + 914490 * 2 ^ 59
def prefixEnd_914490 : Nat := 4983230072969 + 3 ^ 40 * 914490 * 2
def baseEnd_914490 : Nat := 469572923730232287369343

theorem tailTrace_914490 : CollatzResearch.WordTrace tailWord_914490 prefixEnd_914490 469572923730232287369343 := by
  unfold tailWord_914490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338547614241596825697231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22236126971310924868525949 8338547614241596825697231)
  ·
    refine ⟨12507821421362395238545847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8338547614241596825697231 12507821421362395238545847)
    ·
      refine ⟨18761732132043592857818771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12507821421362395238545847 18761732132043592857818771)
      ·
        refine ⟨28142598198065389286728157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18761732132043592857818771 28142598198065389286728157)
        ·
          refine ⟨10553474324274520982523059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28142598198065389286728157 10553474324274520982523059)
          ·
            refine ⟨15830211486411781473784589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553474324274520982523059 15830211486411781473784589)
            ·
              refine ⟨5936329307404418052669221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15830211486411781473784589 5936329307404418052669221)
              ·
                refine ⟨1113061745138328384875479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5936329307404418052669221 1113061745138328384875479)
                ·
                  refine ⟨1669592617707492577313219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113061745138328384875479 1669592617707492577313219)
                  ·
                    refine ⟨2504388926561238865969829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669592617707492577313219 2504388926561238865969829)
                    ·
                      refine ⟨469572923730232287369343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2504388926561238865969829 469572923730232287369343)
                      ·
                        rfl

theorem cell23_914490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_914490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914490 prefixEnd_914490 := by exact prefixLift 914490
  have htrace : WordTrace (prefixWord ++ tailWord_914490) baseStart_914490 baseEnd_914490 := by
    simpa [prefixWord, tailWord_914490, baseEnd_914490] using wordTrace_append hprefix tailTrace_914490
  have hstable : (prefixWord ++ tailWord_914490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914490).length < 2 ^ (prefixWord ++ tailWord_914490).sum := by decide
  have hdescent : baseEnd_914490 < baseStart_914490 := by decide
  rcases family_descends (prefixWord ++ tailWord_914490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914510 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_914510 : Nat := 118140960795 + 914510 * 2 ^ 59
def prefixEnd_914510 : Nat := 4983230072969 + 3 ^ 40 * 914510 * 2
def baseEnd_914510 : Nat := 469583193343322209119251

theorem tailTrace_914510 : CollatzResearch.WordTrace tailWord_914510 prefixEnd_914510 469583193343322209119251 := by
  unfold tailWord_914510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169364989611741339814623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22236613277929287145677989 4169364989611741339814623)
  ·
    refine ⟨6254047484417612009721935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169364989611741339814623 6254047484417612009721935)
    ·
      refine ⟨9381071226626418014582903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254047484417612009721935 9381071226626418014582903)
      ·
        refine ⟨14071606839939627021874355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381071226626418014582903 14071606839939627021874355)
        ·
          refine ⟨21107410259909440532811533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071606839939627021874355 21107410259909440532811533)
          ·
            refine ⟨7915278847466040199804325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21107410259909440532811533 7915278847466040199804325)
            ·
              refine ⟨1484114783899882537463311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7915278847466040199804325 1484114783899882537463311)
              ·
                refine ⟨2226172175849823806194967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484114783899882537463311 2226172175849823806194967)
                ·
                  refine ⟨3339258263774735709292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226172175849823806194967 3339258263774735709292451)
                  ·
                    refine ⟨5008887395662103563938677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339258263774735709292451 5008887395662103563938677)
                    ·
                      refine ⟨469583193343322209119251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5008887395662103563938677 469583193343322209119251)
                      ·
                        rfl

theorem cell23_914510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_914510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914510 prefixEnd_914510 := by exact prefixLift 914510
  have htrace : WordTrace (prefixWord ++ tailWord_914510) baseStart_914510 baseEnd_914510 := by
    simpa [prefixWord, tailWord_914510, baseEnd_914510] using wordTrace_append hprefix tailTrace_914510
  have hstable : (prefixWord ++ tailWord_914510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914510).length < 2 ^ (prefixWord ++ tailWord_914510).sum := by decide
  have hdescent : baseEnd_914510 < baseStart_914510 := by decide
  rcases family_descends (prefixWord ++ tailWord_914510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914518 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_914518 : Nat := 118140960795 + 914518 * 2 ^ 59
def prefixEnd_914518 : Nat := 4983230072969 + 3 ^ 40 * 914518 * 2
def baseEnd_914518 : Nat := 469587301188558177819215

theorem tailTrace_914518 : CollatzResearch.WordTrace tailWord_914518 prefixEnd_914518 469587301188558177819215 := by
  unfold tailWord_914518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084700731304059255300513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22236807800576632056538805 2084700731304059255300513)
  ·
    refine ⟨1563525548478044441475385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2084700731304059255300513 1563525548478044441475385)
    ·
      refine ⟨1172644161358533331106539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1563525548478044441475385 1172644161358533331106539)
      ·
        refine ⟨1758966242037799996659809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172644161358533331106539 1758966242037799996659809)
        ·
          refine ⟨1319224681528349997494857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758966242037799996659809 1319224681528349997494857)
          ·
            refine ⟨989418511146262498121143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319224681528349997494857 989418511146262498121143)
            ·
              refine ⟨1484127766719393747181715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989418511146262498121143 1484127766719393747181715)
              ·
                refine ⟨2226191650079090620772573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484127766719393747181715 2226191650079090620772573)
                ·
                  refine ⟨834821868779658982789715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2226191650079090620772573 834821868779658982789715)
                  ·
                    refine ⟨1252232803169488474184573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834821868779658982789715 1252232803169488474184573)
                    ·
                      refine ⟨469587301188558177819215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252232803169488474184573 469587301188558177819215)
                      ·
                        rfl

theorem cell23_914518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_914518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914518 prefixEnd_914518 := by exact prefixLift 914518
  have htrace : WordTrace (prefixWord ++ tailWord_914518) baseStart_914518 baseEnd_914518 := by
    simpa [prefixWord, tailWord_914518, baseEnd_914518] using wordTrace_append hprefix tailTrace_914518
  have hstable : (prefixWord ++ tailWord_914518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914518).length < 2 ^ (prefixWord ++ tailWord_914518).sum := by decide
  have hdescent : baseEnd_914518 < baseStart_914518 := by decide
  rcases family_descends (prefixWord ++ tailWord_914518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914530 : List Nat := [3, 3, 2, 2, 1, 1, 1, 10]
def baseStart_914530 : Nat := 118140960795 + 914530 * 2 ^ 59
def prefixEnd_914530 : Nat := 4983230072969 + 3 ^ 40 * 914530 * 2
def baseEnd_914530 : Nat := 17392350479867115958117

theorem tailTrace_914530 : CollatzResearch.WordTrace tailWord_914530 prefixEnd_914530 17392350479867115958117 := by
  unfold tailWord_914530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338912344205368533561261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22237099584547649422830029 8338912344205368533561261)
  ·
    refine ⟨3127092129077013200085473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8338912344205368533561261 3127092129077013200085473)
    ·
      refine ⟨2345319096807759900064105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3127092129077013200085473 2345319096807759900064105)
      ·
        refine ⟨1758989322605819925048079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345319096807759900064105 1758989322605819925048079)
        ·
          refine ⟨2638483983908729887572119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758989322605819925048079 2638483983908729887572119)
          ·
            refine ⟨3957725975863094831358179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638483983908729887572119 3957725975863094831358179)
            ·
              refine ⟨5936588963794642247037269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957725975863094831358179 5936588963794642247037269)
              ·
                refine ⟨17392350479867115958117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5936588963794642247037269 17392350479867115958117)
                ·
                  rfl

theorem cell23_914530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_914530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914530 prefixEnd_914530 := by exact prefixLift 914530
  have htrace : WordTrace (prefixWord ++ tailWord_914530) baseStart_914530 baseEnd_914530 := by
    simpa [prefixWord, tailWord_914530, baseEnd_914530] using wordTrace_append hprefix tailTrace_914530
  have hstable : (prefixWord ++ tailWord_914530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914530).length < 2 ^ (prefixWord ++ tailWord_914530).sum := by decide
  have hdescent : baseEnd_914530 < baseStart_914530 := by decide
  rcases family_descends (prefixWord ++ tailWord_914530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914533 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_914533 : Nat := 118140960795 + 914533 * 2 ^ 59
def prefixEnd_914533 : Nat := 4983230072969 + 3 ^ 40 * 914533 * 2
def baseEnd_914533 : Nat := 469595003398375619131645

theorem tailTrace_914533 : CollatzResearch.WordTrace tailWord_914533 prefixEnd_914533 469595003398375619131645 := by
  unfold tailWord_914533
  simp only [CollatzResearch.WordTrace]
  refine ⟨33355758795810605646604253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22237172530540403764402835 33355758795810605646604253)
  ·
    refine ⟨12508409548428977117476595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33355758795810605646604253 12508409548428977117476595)
    ·
      refine ⟨18762614322643465676214893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508409548428977117476595 18762614322643465676214893)
      ·
        refine ⟨7035980370991299628580585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18762614322643465676214893 7035980370991299628580585)
        ·
          refine ⟨5276985278243474721435439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7035980370991299628580585 5276985278243474721435439)
          ·
            refine ⟨7915477917365212082153159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276985278243474721435439 7915477917365212082153159)
            ·
              refine ⟨11873216876047818123229739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915477917365212082153159 11873216876047818123229739)
              ·
                refine ⟨17809825314071727184844609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873216876047818123229739 17809825314071727184844609)
                ·
                  refine ⟨13357368985553795388633457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17809825314071727184844609 13357368985553795388633457)
                  ·
                    refine ⟨10018026739165346541475093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13357368985553795388633457 10018026739165346541475093)
                    ·
                      refine ⟨469595003398375619131645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10018026739165346541475093 469595003398375619131645)
                      ·
                        rfl

theorem cell23_914533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_914533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914533 prefixEnd_914533 := by exact prefixLift 914533
  have htrace : WordTrace (prefixWord ++ tailWord_914533) baseStart_914533 baseEnd_914533 := by
    simpa [prefixWord, tailWord_914533, baseEnd_914533] using wordTrace_append hprefix tailTrace_914533
  have hstable : (prefixWord ++ tailWord_914533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914533).length < 2 ^ (prefixWord ++ tailWord_914533).sum := by decide
  have hdescent : baseEnd_914533 < baseStart_914533 := by decide
  rcases family_descends (prefixWord ++ tailWord_914533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914540 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_914540 : Nat := 118140960795 + 914540 * 2 ^ 59
def prefixEnd_914540 : Nat := 4983230072969 + 3 ^ 40 * 914540 * 2
def baseEnd_914540 : Nat := 469598597762957091744113

theorem tailTrace_914540 : CollatzResearch.WordTrace tailWord_914540 prefixEnd_914540 469598597762957091744113 := by
  unfold tailWord_914540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678007053392622921054537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22237342737856830561406049 16678007053392622921054537)
  ·
    refine ⟨12508505290044467190790903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16678007053392622921054537 12508505290044467190790903)
    ·
      refine ⟨18762757935066700786186355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508505290044467190790903 18762757935066700786186355)
      ·
        refine ⟨28144136902600051179279533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18762757935066700786186355 28144136902600051179279533)
        ·
          refine ⟨10554051338475019192229825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28144136902600051179279533 10554051338475019192229825)
          ·
            refine ⟨7915538503856264394172369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10554051338475019192229825 7915538503856264394172369)
            ·
              refine ⟨5936653877892198295629277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7915538503856264394172369 5936653877892198295629277)
              ·
                refine ⟨2226245204209574360860979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5936653877892198295629277 2226245204209574360860979)
                ·
                  refine ⟨3339367806314361541291469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226245204209574360860979 3339367806314361541291469)
                  ·
                    refine ⟨1252262927367885577984301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339367806314361541291469 1252262927367885577984301)
                    ·
                      refine ⟨469598597762957091744113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252262927367885577984301 469598597762957091744113)
                      ·
                        rfl

theorem cell23_914540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_914540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914540 prefixEnd_914540 := by exact prefixLift 914540
  have htrace : WordTrace (prefixWord ++ tailWord_914540) baseStart_914540 baseEnd_914540 := by
    simpa [prefixWord, tailWord_914540, baseEnd_914540] using wordTrace_append hprefix tailTrace_914540
  have hstable : (prefixWord ++ tailWord_914540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914540).length < 2 ^ (prefixWord ++ tailWord_914540).sum := by decide
  have hdescent : baseEnd_914540 < baseStart_914540 := by decide
  rcases family_descends (prefixWord ++ tailWord_914540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914574 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_914574 : Nat := 118140960795 + 914574 * 2 ^ 59
def prefixEnd_914574 : Nat := 4983230072969 + 3 ^ 40 * 914574 * 2
def baseEnd_914574 : Nat := 469616056105209958718957

theorem tailTrace_914574 : CollatzResearch.WordTrace tailWord_914574 prefixEnd_914574 469616056105209958718957 := by
  unfold tailWord_914574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169656773582758706105847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22238169459108046432564517 4169656773582758706105847)
  ·
    refine ⟨6254485160374138059158771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169656773582758706105847 6254485160374138059158771)
    ·
      refine ⟨9381727740561207088738157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254485160374138059158771 9381727740561207088738157)
      ·
        refine ⟨3518147902710452658276809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9381727740561207088738157 3518147902710452658276809)
        ·
          refine ⟨2638610927032839493707607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518147902710452658276809 2638610927032839493707607)
          ·
            refine ⟨3957916390549259240561411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638610927032839493707607 3957916390549259240561411)
            ·
              refine ⟨5936874585823888860842117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957916390549259240561411 5936874585823888860842117)
              ·
                refine ⟨1113163984841979161407897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5936874585823888860842117 1113163984841979161407897)
                ·
                  refine ⟨834872988631484371055923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1113163984841979161407897 834872988631484371055923)
                  ·
                    refine ⟨1252309482947226556583885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834872988631484371055923 1252309482947226556583885)
                    ·
                      refine ⟨469616056105209958718957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252309482947226556583885 469616056105209958718957)
                      ·
                        rfl

theorem cell23_914574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_914574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914574 prefixEnd_914574 := by exact prefixLift 914574
  have htrace : WordTrace (prefixWord ++ tailWord_914574) baseStart_914574 baseEnd_914574 := by
    simpa [prefixWord, tailWord_914574, baseEnd_914574] using wordTrace_append hprefix tailTrace_914574
  have hstable : (prefixWord ++ tailWord_914574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914574).length < 2 ^ (prefixWord ++ tailWord_914574).sum := by decide
  have hdescent : baseEnd_914574 < baseStart_914574 := by decide
  rcases family_descends (prefixWord ++ tailWord_914574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914597 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_914597 : Nat := 118140960795 + 914597 * 2 ^ 59
def prefixEnd_914597 : Nat := 4983230072969 + 3 ^ 40 * 914597 * 2
def baseEnd_914597 : Nat := 469627866160263368731351

theorem tailTrace_914597 : CollatzResearch.WordTrace tailWord_914597 prefixEnd_914597 469627866160263368731351 := by
  unfold tailWord_914597
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358093067578744576934045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22238728711719163051289363 33358093067578744576934045)
  ·
    refine ⟨12509284900342029216350267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33358093067578744576934045 12509284900342029216350267)
    ·
      refine ⟨18763927350513043824525401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12509284900342029216350267 18763927350513043824525401)
      ·
        refine ⟨14072945512884782868394051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18763927350513043824525401 14072945512884782868394051)
        ·
          refine ⟨21109418269327174302591077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14072945512884782868394051 21109418269327174302591077)
          ·
            refine ⟨3958015925498845181735827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21109418269327174302591077 3958015925498845181735827)
            ·
              refine ⟨5937023888248267772603741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958015925498845181735827 5937023888248267772603741)
              ·
                refine ⟨2226383958093100414726403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5937023888248267772603741 2226383958093100414726403)
                ·
                  refine ⟨3339575937139650622089605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226383958093100414726403 3339575937139650622089605)
                  ·
                    refine ⟨626170488213684491641801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339575937139650622089605 626170488213684491641801)
                    ·
                      refine ⟨469627866160263368731351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626170488213684491641801 469627866160263368731351)
                      ·
                        rfl

theorem cell23_914597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_914597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914597 prefixEnd_914597 := by exact prefixLift 914597
  have htrace : WordTrace (prefixWord ++ tailWord_914597) baseStart_914597 baseEnd_914597 := by
    simpa [prefixWord, tailWord_914597, baseEnd_914597] using wordTrace_append hprefix tailTrace_914597
  have hstable : (prefixWord ++ tailWord_914597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914597).length < 2 ^ (prefixWord ++ tailWord_914597).sum := by decide
  have hdescent : baseEnd_914597 < baseStart_914597 := by decide
  rcases family_descends (prefixWord ++ tailWord_914597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914648 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_914648 : Nat := 118140960795 + 914648 * 2 ^ 59
def prefixEnd_914648 : Nat := 4983230072969 + 3 ^ 40 * 914648 * 2
def baseEnd_914648 : Nat := 469654053673642669193617

theorem tailTrace_914648 : CollatzResearch.WordTrace tailWord_914648 prefixEnd_914648 469654053673642669193617 := by
  unfold tailWord_914648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679976595196990143520299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22239968793595986858027065 16679976595196990143520299)
  ·
    refine ⟨25019964892795485215280449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16679976595196990143520299 25019964892795485215280449)
    ·
      refine ⟨18764973669596613911460337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25019964892795485215280449 18764973669596613911460337)
      ·
        refine ⟨14073730252197460433595253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18764973669596613911460337 14073730252197460433595253)
        ·
          refine ⟨1319412211143511915649555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14073730252197460433595253 1319412211143511915649555)
          ·
            refine ⟨1979118316715267873474333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319412211143511915649555 1979118316715267873474333)
            ·
              refine ⟨742169368768225452552875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979118316715267873474333 742169368768225452552875)
              ·
                refine ⟨1113254053152338178829313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742169368768225452552875 1113254053152338178829313)
                ·
                  refine ⟨834940539864253634121985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1113254053152338178829313 834940539864253634121985)
                  ·
                    refine ⟨626205404898190225591489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 834940539864253634121985 626205404898190225591489)
                    ·
                      refine ⟨469654053673642669193617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626205404898190225591489 469654053673642669193617)
                      ·
                        rfl

theorem cell23_914648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_914648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914648 prefixEnd_914648 := by exact prefixLift 914648
  have htrace : WordTrace (prefixWord ++ tailWord_914648) baseStart_914648 baseEnd_914648 := by
    simpa [prefixWord, tailWord_914648, baseEnd_914648] using wordTrace_append hprefix tailTrace_914648
  have hstable : (prefixWord ++ tailWord_914648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914648).length < 2 ^ (prefixWord ++ tailWord_914648).sum := by decide
  have hdescent : baseEnd_914648 < baseStart_914648 := by decide
  rcases family_descends (prefixWord ++ tailWord_914648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914671 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 5]
def baseStart_914671 : Nat := 118140960795 + 914671 * 2 ^ 59
def prefixEnd_914671 : Nat := 4983230072969 + 3 ^ 40 * 914671 * 2
def baseEnd_914671 : Nat := 52185095969855119911779

theorem tailTrace_914671 : CollatzResearch.WordTrace tailWord_914671 prefixEnd_914671 52185095969855119911779 := by
  unfold tailWord_914671
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360792069310655215127867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240528046207103476751911 33360792069310655215127867)
  ·
    refine ⟨50041188103965982822691801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33360792069310655215127867 50041188103965982822691801)
    ·
      refine ⟨37530891077974487117018851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50041188103965982822691801 37530891077974487117018851)
      ·
        refine ⟨56296336616961730675528277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37530891077974487117018851 56296336616961730675528277)
        ·
          refine ⟨659722694730020281353847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 56296336616961730675528277 659722694730020281353847)
          ·
            refine ⟨989584042095030422030771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659722694730020281353847 989584042095030422030771)
            ·
              refine ⟨1484376063142545633046157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989584042095030422030771 1484376063142545633046157)
              ·
                refine ⟨556641023678454612392309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484376063142545633046157 556641023678454612392309)
                ·
                  refine ⟨52185095969855119911779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556641023678454612392309 52185095969855119911779)
                  ·
                    rfl

theorem cell23_914671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 5].length) (baseStart_914671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914671 prefixEnd_914671 := by exact prefixLift 914671
  have htrace : WordTrace (prefixWord ++ tailWord_914671) baseStart_914671 baseEnd_914671 := by
    simpa [prefixWord, tailWord_914671, baseEnd_914671] using wordTrace_append hprefix tailTrace_914671
  have hstable : (prefixWord ++ tailWord_914671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914671).length < 2 ^ (prefixWord ++ tailWord_914671).sum := by decide
  have hdescent : baseEnd_914671 < baseStart_914671 := by decide
  rcases family_descends (prefixWord ++ tailWord_914671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914687 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_914687 : Nat := 118140960795 + 914687 * 2 ^ 59
def prefixEnd_914687 : Nat := 4983230072969 + 3 ^ 40 * 914687 * 2
def baseEnd_914687 : Nat := 469674079419168016605937

theorem tailTrace_914687 : CollatzResearch.WordTrace tailWord_914687 prefixEnd_914687 469674079419168016605937 := by
  unfold tailWord_914687
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361375637252689947710315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240917091501793298473543 33361375637252689947710315)
  ·
    refine ⟨50042063455879034921565473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33361375637252689947710315 50042063455879034921565473)
    ·
      refine ⟨37531547591909276191174105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50042063455879034921565473 37531547591909276191174105)
      ·
        refine ⟨28148660693931957143380579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37531547591909276191174105 28148660693931957143380579)
        ·
          refine ⟨42222991040897935715070869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28148660693931957143380579 42222991040897935715070869)
          ·
            refine ⟨1979202705042090736643947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42222991040897935715070869 1979202705042090736643947)
            ·
              refine ⟨2968804057563136104965921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979202705042090736643947 2968804057563136104965921)
              ·
                refine ⟨2226603043172352078724441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968804057563136104965921 2226603043172352078724441)
                ·
                  refine ⟨1669952282379264059043331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226603043172352078724441 1669952282379264059043331)
                  ·
                    refine ⟨2504928423568896088564997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669952282379264059043331 2504928423568896088564997)
                    ·
                      refine ⟨469674079419168016605937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2504928423568896088564997 469674079419168016605937)
                      ·
                        rfl

theorem cell23_914687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_914687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914687 prefixEnd_914687 := by exact prefixLift 914687
  have htrace : WordTrace (prefixWord ++ tailWord_914687) baseStart_914687 baseEnd_914687 := by
    simpa [prefixWord, tailWord_914687, baseEnd_914687] using wordTrace_append hprefix tailTrace_914687
  have hstable : (prefixWord ++ tailWord_914687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914687).length < 2 ^ (prefixWord ++ tailWord_914687).sum := by decide
  have hdescent : baseEnd_914687 < baseStart_914687 := by decide
  rcases family_descends (prefixWord ++ tailWord_914687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914724 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_914724 : Nat := 118140960795 + 914724 * 2 ^ 59
def prefixEnd_914724 : Nat := 4983230072969 + 3 ^ 40 * 914724 * 2
def baseEnd_914724 : Nat := 469693078203384371843267

theorem tailTrace_914724 : CollatzResearch.WordTrace tailWord_914724 prefixEnd_914724 469693078203384371843267 := by
  unfold tailWord_914724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681362569059322633403613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22241816758745763511204817 16681362569059322633403613)
  ·
    refine ⟨6255510963397245987526355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16681362569059322633403613 6255510963397245987526355)
    ·
      refine ⟨9383266445095868981289533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255510963397245987526355 9383266445095868981289533)
      ·
        refine ⟨3518724916910950867983575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9383266445095868981289533 3518724916910950867983575)
        ·
          refine ⟨5278087375366426301975363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518724916910950867983575 5278087375366426301975363)
          ·
            refine ⟨7917131063049639452963045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278087375366426301975363 7917131063049639452963045)
            ·
              refine ⟨1484462074321807397430571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7917131063049639452963045 1484462074321807397430571)
              ·
                refine ⟨2226693111482711096145857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484462074321807397430571 2226693111482711096145857)
                ·
                  refine ⟨1670019833612033322109393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226693111482711096145857 1670019833612033322109393)
                  ·
                    refine ⟨1252514875209024991582045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670019833612033322109393 1252514875209024991582045)
                    ·
                      refine ⟨469693078203384371843267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252514875209024991582045 469693078203384371843267)
                      ·
                        rfl

theorem cell23_914724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_914724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914724 prefixEnd_914724 := by exact prefixLift 914724
  have htrace : WordTrace (prefixWord ++ tailWord_914724) baseStart_914724 baseEnd_914724 := by
    simpa [prefixWord, tailWord_914724, baseEnd_914724] using wordTrace_append hprefix tailTrace_914724
  have hstable : (prefixWord ++ tailWord_914724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914724).length < 2 ^ (prefixWord ++ tailWord_914724).sum := by decide
  have hdescent : baseEnd_914724 < baseStart_914724 := by decide
  rcases family_descends (prefixWord ++ tailWord_914724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914748 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_914748 : Nat := 118140960795 + 914748 * 2 ^ 59
def prefixEnd_914748 : Nat := 4983230072969 + 3 ^ 40 * 914748 * 2
def baseEnd_914748 : Nat := 156568467246364092647719

theorem tailTrace_914748 : CollatzResearch.WordTrace tailWord_914748 prefixEnd_914748 156568467246364092647719 := by
  unfold tailWord_914748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681800245015848682840449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22242400326687798243787265 16681800245015848682840449)
  ·
    refine ⟨12511350183761886512130337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16681800245015848682840449 12511350183761886512130337)
    ·
      refine ⟨9383512637821414884097753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12511350183761886512130337 9383512637821414884097753)
      ·
        refine ⟨7037634478366061163073315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9383512637821414884097753 7037634478366061163073315)
        ·
          refine ⟨10556451717549091744609973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037634478366061163073315 10556451717549091744609973)
          ·
            refine ⟨989667348520227351057185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10556451717549091744609973 989667348520227351057185)
            ·
              refine ⟨742250511390170513292889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989667348520227351057185 742250511390170513292889)
              ·
                refine ⟨556687883542627884969667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742250511390170513292889 556687883542627884969667)
                ·
                  refine ⟨835031825313941827454501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556687883542627884969667 835031825313941827454501)
                  ·
                    refine ⟨156568467246364092647719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835031825313941827454501 156568467246364092647719)
                    ·
                      rfl

theorem cell23_914748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_914748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914748 prefixEnd_914748 := by exact prefixLift 914748
  have htrace : WordTrace (prefixWord ++ tailWord_914748) baseStart_914748 baseEnd_914748 := by
    simpa [prefixWord, tailWord_914748, baseEnd_914748] using wordTrace_append hprefix tailTrace_914748
  have hstable : (prefixWord ++ tailWord_914748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914748).length < 2 ^ (prefixWord ++ tailWord_914748).sum := by decide
  have hdescent : baseEnd_914748 < baseStart_914748 := by decide
  rcases family_descends (prefixWord ++ tailWord_914748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914777 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_914777 : Nat := 118140960795 + 914777 * 2 ^ 59
def prefixEnd_914777 : Nat := 4983230072969 + 3 ^ 40 * 914777 * 2
def baseEnd_914777 : Nat := 469720292678072664480523

theorem tailTrace_914777 : CollatzResearch.WordTrace tailWord_914777 prefixEnd_914777 469720292678072664480523 := by
  unfold tailWord_914777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364658206926635318486585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22243105471284423545657723 33364658206926635318486585)
  ·
    refine ⟨25023493655194976488864939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33364658206926635318486585 25023493655194976488864939)
    ·
      refine ⟨37535240482792464733297409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25023493655194976488864939 37535240482792464733297409)
      ·
        refine ⟨28151430362094348549973057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37535240482792464733297409 28151430362094348549973057)
        ·
          refine ⟨21113572771570761412479793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28151430362094348549973057 21113572771570761412479793)
          ·
            refine ⟨15835179578678071059359845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21113572771570761412479793 15835179578678071059359845)
            ·
              refine ⟨2969096171002138323629971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15835179578678071059359845 2969096171002138323629971)
              ·
                refine ⟨4453644256503207485444957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969096171002138323629971 4453644256503207485444957)
                ·
                  refine ⟨1670116596188702807041859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4453644256503207485444957 1670116596188702807041859)
                  ·
                    refine ⟨2505174894283054210562789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670116596188702807041859 2505174894283054210562789)
                    ·
                      refine ⟨469720292678072664480523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2505174894283054210562789 469720292678072664480523)
                      ·
                        rfl

theorem cell23_914777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_914777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914777 prefixEnd_914777 := by exact prefixLift 914777
  have htrace : WordTrace (prefixWord ++ tailWord_914777) baseStart_914777 baseEnd_914777 := by
    simpa [prefixWord, tailWord_914777, baseEnd_914777] using wordTrace_append hprefix tailTrace_914777
  have hstable : (prefixWord ++ tailWord_914777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914777).length < 2 ^ (prefixWord ++ tailWord_914777).sum := by decide
  have hdescent : baseEnd_914777 < baseStart_914777 := by decide
  rcases family_descends (prefixWord ++ tailWord_914777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914787 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 6]
def baseStart_914787 : Nat := 118140960795 + 914787 * 2 ^ 59
def prefixEnd_914787 : Nat := 4983230072969 + 3 ^ 40 * 914787 * 2
def baseEnd_914787 : Nat := 156575142494872541785159

theorem tailTrace_914787 : CollatzResearch.WordTrace tailWord_914787 prefixEnd_914787 156575142494872541785159 := by
  unfold tailWord_914787
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365022936890407026350615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22243348624593604684233743 33365022936890407026350615)
  ·
    refine ⟨50047534405335610539525923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33365022936890407026350615 50047534405335610539525923)
    ·
      refine ⟨75071301608003415809288885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50047534405335610539525923 75071301608003415809288885)
      ·
        refine ⟨7037934525750320232120833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75071301608003415809288885 7037934525750320232120833)
        ·
          refine ⟨5278450894312740174090625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7037934525750320232120833 5278450894312740174090625)
          ·
            refine ⟨3958838170734555130567969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278450894312740174090625 3958838170734555130567969)
            ·
              refine ⟨2969128628050916347925977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958838170734555130567969 2969128628050916347925977)
              ·
                refine ⟨2226846471038187260944483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969128628050916347925977 2226846471038187260944483)
                ·
                  refine ⟨3340269706557280891416725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226846471038187260944483 3340269706557280891416725)
                  ·
                    refine ⟨156575142494872541785159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3340269706557280891416725 156575142494872541785159)
                    ·
                      rfl

theorem cell23_914787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_914787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914787 prefixEnd_914787 := by exact prefixLift 914787
  have htrace : WordTrace (prefixWord ++ tailWord_914787) baseStart_914787 baseEnd_914787 := by
    simpa [prefixWord, tailWord_914787, baseEnd_914787] using wordTrace_append hprefix tailTrace_914787
  have hstable : (prefixWord ++ tailWord_914787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914787).length < 2 ^ (prefixWord ++ tailWord_914787).sum := by decide
  have hdescent : baseEnd_914787 < baseStart_914787 := by decide
  rcases family_descends (prefixWord ++ tailWord_914787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914788 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_914788 : Nat := 118140960795 + 914788 * 2 ^ 59
def prefixEnd_914788 : Nat := 4983230072969 + 3 ^ 40 * 914788 * 2
def baseEnd_914788 : Nat := 469725940965272121442973

theorem tailTrace_914788 : CollatzResearch.WordTrace tailWord_914788 prefixEnd_914788 469725940965272121442973 := by
  unfold tailWord_914788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16682529704943392098568509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22243372939924522798091345 16682529704943392098568509)
  ·
    refine ⟨6255948639353772036963191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16682529704943392098568509 6255948639353772036963191)
    ·
      refine ⟨9383922959030658055444787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255948639353772036963191 9383922959030658055444787)
      ·
        refine ⟨14075884438545987083167181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383922959030658055444787 14075884438545987083167181)
        ·
          refine ⟨5278456664454745156187693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14075884438545987083167181 5278456664454745156187693)
          ·
            refine ⟨1979421249170529433570385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5278456664454745156187693 1979421249170529433570385)
            ·
              refine ⟨1484565936877897075177789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979421249170529433570385 1484565936877897075177789)
              ·
                refine ⟨556712226329211403191671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484565936877897075177789 556712226329211403191671)
                ·
                  refine ⟨835068339493817104787507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556712226329211403191671 835068339493817104787507)
                  ·
                    refine ⟨1252602509240725657181261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835068339493817104787507 1252602509240725657181261)
                    ·
                      refine ⟨469725940965272121442973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252602509240725657181261 469725940965272121442973)
                      ·
                        rfl

theorem cell23_914788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_914788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914788 prefixEnd_914788 := by exact prefixLift 914788
  have htrace : WordTrace (prefixWord ++ tailWord_914788) baseStart_914788 baseEnd_914788 := by
    simpa [prefixWord, tailWord_914788, baseEnd_914788] using wordTrace_append hprefix tailTrace_914788
  have hstable : (prefixWord ++ tailWord_914788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914788).length < 2 ^ (prefixWord ++ tailWord_914788).sum := by decide
  have hdescent : baseEnd_914788 < baseStart_914788 := by decide
  rcases family_descends (prefixWord ++ tailWord_914788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914800 : List Nat := [2, 1, 1, 1, 4, 2, 12]
def baseStart_914800 : Nat := 118140960795 + 914800 * 2 ^ 59
def prefixEnd_914800 : Nat := 4983230072969 + 3 ^ 40 * 914800 * 2
def baseEnd_914800 : Nat := 5799161762137358944357

theorem tailTrace_914800 : CollatzResearch.WordTrace tailWord_914800 prefixEnd_914800 5799161762137358944357 := by
  unfold tailWord_914800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16682748542921655123286927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22243664723895540164382569 16682748542921655123286927)
  ·
    refine ⟨25024122814382482684930391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16682748542921655123286927 25024122814382482684930391)
    ·
      refine ⟨37536184221573724027395587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25024122814382482684930391 37536184221573724027395587)
      ·
        refine ⟨56304276332360586041093381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37536184221573724027395587 56304276332360586041093381)
        ·
          refine ⟨10557051812317609882705009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56304276332360586041093381 10557051812317609882705009)
          ·
            refine ⟨7917788859238207412028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10557051812317609882705009 7917788859238207412028757)
            ·
              refine ⟨5799161762137358944357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7917788859238207412028757 5799161762137358944357)
              ·
                rfl

theorem cell23_914800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 12].length) (baseStart_914800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914800 prefixEnd_914800 := by exact prefixLift 914800
  have htrace : WordTrace (prefixWord ++ tailWord_914800) baseStart_914800 baseEnd_914800 := by
    simpa [prefixWord, tailWord_914800, baseEnd_914800] using wordTrace_append hprefix tailTrace_914800
  have hstable : (prefixWord ++ tailWord_914800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914800).length < 2 ^ (prefixWord ++ tailWord_914800).sum := by decide
  have hdescent : baseEnd_914800 < baseStart_914800 := by decide
  rcases family_descends (prefixWord ++ tailWord_914800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914811 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 3, 2, 2]
def baseStart_914811 : Nat := 118140960795 + 914811 * 2 ^ 59
def prefixEnd_914811 : Nat := 4983230072969 + 3 ^ 40 * 914811 * 2
def baseEnd_914811 : Nat := 469737751020325531455367

theorem tailTrace_914811 : CollatzResearch.WordTrace tailWord_914811 prefixEnd_914811 469737751020325531455367 := by
  unfold tailWord_914811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365898288803459125224287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22243932192535639416816191 33365898288803459125224287)
  ·
    refine ⟨50048847433205188687836431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33365898288803459125224287 50048847433205188687836431)
    ·
      refine ⟨75073271149807783031754647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50048847433205188687836431 75073271149807783031754647)
      ·
        refine ⟨112609906724711674547631971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75073271149807783031754647 112609906724711674547631971)
        ·
          refine ⟨168914860087067511821447957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112609906724711674547631971 168914860087067511821447957)
          ·
            refine ⟨7917884066581289616630373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168914860087067511821447957 7917884066581289616630373)
            ·
              refine ⟨1484603262483991803118195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7917884066581289616630373 1484603262483991803118195)
              ·
                refine ⟨2226904893725987704677293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484603262483991803118195 2226904893725987704677293)
                ·
                  refine ⟨835089335147245389253985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2226904893725987704677293 835089335147245389253985)
                  ·
                    refine ⟨626317001360434041940489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835089335147245389253985 626317001360434041940489)
                    ·
                      refine ⟨469737751020325531455367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626317001360434041940489 469737751020325531455367)
                      ·
                        rfl

theorem cell23_914811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2, 2].length) (baseStart_914811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914811 prefixEnd_914811 := by exact prefixLift 914811
  have htrace : WordTrace (prefixWord ++ tailWord_914811) baseStart_914811 baseEnd_914811 := by
    simpa [prefixWord, tailWord_914811, baseEnd_914811] using wordTrace_append hprefix tailTrace_914811
  have hstable : (prefixWord ++ tailWord_914811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914811).length < 2 ^ (prefixWord ++ tailWord_914811).sum := by decide
  have hdescent : baseEnd_914811 < baseStart_914811 := by decide
  rcases family_descends (prefixWord ++ tailWord_914811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914824 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_914824 : Nat := 118140960795 + 914824 * 2 ^ 59
def prefixEnd_914824 : Nat := 4983230072969 + 3 ^ 40 * 914824 * 2
def baseEnd_914824 : Nat := 469744426268833980592807

theorem tailTrace_914824 : CollatzResearch.WordTrace tailWord_914824 prefixEnd_914824 469744426268833980592807 := by
  unfold tailWord_914824
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683186218878181172723763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22244248291837574896965017 16683186218878181172723763)
  ·
    refine ⟨25024779328317271759085645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16683186218878181172723763 25024779328317271759085645)
    ·
      refine ⟨9384292248118976909657117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25024779328317271759085645 9384292248118976909657117)
      ·
        refine ⟨3519109593044616341121419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9384292248118976909657117 3519109593044616341121419)
        ·
          refine ⟨5278664389566924511682129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519109593044616341121419 5278664389566924511682129)
          ·
            refine ⟨3958998292175193383761597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278664389566924511682129 3958998292175193383761597)
            ·
              refine ⟨1484624359565697518910599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3958998292175193383761597 1484624359565697518910599)
              ·
                refine ⟨2226936539348546278365899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484624359565697518910599 2226936539348546278365899)
                ·
                  refine ⟨3340404809022819417548849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226936539348546278365899 3340404809022819417548849)
                  ·
                    refine ⟨2505303606767114563161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340404809022819417548849 2505303606767114563161637)
                    ·
                      refine ⟨469744426268833980592807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2505303606767114563161637 469744426268833980592807)
                      ·
                        rfl

theorem cell23_914824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_914824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914824 prefixEnd_914824 := by exact prefixLift 914824
  have htrace : WordTrace (prefixWord ++ tailWord_914824) baseStart_914824 baseEnd_914824 := by
    simpa [prefixWord, tailWord_914824, baseEnd_914824] using wordTrace_append hprefix tailTrace_914824
  have hstable : (prefixWord ++ tailWord_914824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914824).length < 2 ^ (prefixWord ++ tailWord_914824).sum := by decide
  have hdescent : baseEnd_914824 < baseStart_914824 := by decide
  rcases family_descends (prefixWord ++ tailWord_914824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914845 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_914845 : Nat := 118140960795 + 914845 * 2 ^ 59
def prefixEnd_914845 : Nat := 4983230072969 + 3 ^ 40 * 914845 * 2
def baseEnd_914845 : Nat := 469755209362578398430211

theorem tailTrace_914845 : CollatzResearch.WordTrace tailWord_914845 prefixEnd_914845 469755209362578398430211 := by
  unfold tailWord_914845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367138370680282931961989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22244758913786855287974659 33367138370680282931961989)
  ·
    refine ⟨6256338444502553049742873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33367138370680282931961989 6256338444502553049742873)
    ·
      refine ⟨4692253833376914787307155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6256338444502553049742873 4692253833376914787307155)
      ·
        refine ⟨7038380750065372180960733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692253833376914787307155 7038380750065372180960733)
        ·
          refine ⟨2639392781274514567860275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7038380750065372180960733 2639392781274514567860275)
          ·
            refine ⟨3959089171911771851790413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639392781274514567860275 3959089171911771851790413)
            ·
              refine ⟨1484658439466914444421405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959089171911771851790413 1484658439466914444421405)
              ·
                refine ⟨556746914800092916658027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484658439466914444421405 556746914800092916658027)
                ·
                  refine ⟨835120372200139374987041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556746914800092916658027 835120372200139374987041)
                  ·
                    refine ⟨626340279150104531240281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835120372200139374987041 626340279150104531240281)
                    ·
                      refine ⟨469755209362578398430211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626340279150104531240281 469755209362578398430211)
                      ·
                        rfl

theorem cell23_914845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_914845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914845 prefixEnd_914845 := by exact prefixLift 914845
  have htrace : WordTrace (prefixWord ++ tailWord_914845) baseStart_914845 baseEnd_914845 := by
    simpa [prefixWord, tailWord_914845, baseEnd_914845] using wordTrace_append hprefix tailTrace_914845
  have hstable : (prefixWord ++ tailWord_914845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914845).length < 2 ^ (prefixWord ++ tailWord_914845).sum := by decide
  have hdescent : baseEnd_914845 < baseStart_914845 := by decide
  rcases family_descends (prefixWord ++ tailWord_914845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914877 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_914877 : Nat := 118140960795 + 914877 * 2 ^ 59
def prefixEnd_914877 : Nat := 4983230072969 + 3 ^ 40 * 914877 * 2
def baseEnd_914877 : Nat := 156590546914507424410021

theorem tailTrace_914877 : CollatzResearch.WordTrace tailWord_914877 prefixEnd_914877 156590546914507424410021 := by
  unfold tailWord_914877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368305506564352397126885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245537004376234931417923 33368305506564352397126885)
  ·
    refine ⟨6256557282480816074461291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33368305506564352397126885 6256557282480816074461291)
    ·
      refine ⟨9384835923721224111691937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256557282480816074461291 9384835923721224111691937)
      ·
        refine ⟨7038626942790918083768953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9384835923721224111691937 7038626942790918083768953)
        ·
          refine ⟨5278970207093188562826715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038626942790918083768953 5278970207093188562826715)
          ·
            refine ⟨7918455310639782844240073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278970207093188562826715 7918455310639782844240073)
            ·
              refine ⟨5938841482979837133180055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918455310639782844240073 5938841482979837133180055)
              ·
                refine ⟨8908262224469755699770083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938841482979837133180055 8908262224469755699770083)
                ·
                  refine ⟨13362393336704633549655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908262224469755699770083 13362393336704633549655125)
                  ·
                    refine ⟨156590546914507424410021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13362393336704633549655125 156590546914507424410021)
                    ·
                      rfl

theorem cell23_914877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_914877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914877 prefixEnd_914877 := by exact prefixLift 914877
  have htrace : WordTrace (prefixWord ++ tailWord_914877) baseStart_914877 baseEnd_914877 := by
    simpa [prefixWord, tailWord_914877, baseEnd_914877] using wordTrace_append hprefix tailTrace_914877
  have hstable : (prefixWord ++ tailWord_914877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914877).length < 2 ^ (prefixWord ++ tailWord_914877).sum := by decide
  have hdescent : baseEnd_914877 < baseStart_914877 := by decide
  rcases family_descends (prefixWord ++ tailWord_914877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914882 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_914882 : Nat := 118140960795 + 914882 * 2 ^ 59
def prefixEnd_914882 : Nat := 4983230072969 + 3 ^ 40 * 914882 * 2
def baseEnd_914882 : Nat := 469774208146794753667541

theorem tailTrace_914882 : CollatzResearch.WordTrace tailWord_914882 prefixEnd_914882 469774208146794753667541 := by
  unfold tailWord_914882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342121967886559562764725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22245658581030825500705933 8342121967886559562764725)
  ·
    refine ⟨782073934489364959009193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8342121967886559562764725 782073934489364959009193)
    ·
      refine ⟨586555450867023719256895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 782073934489364959009193 586555450867023719256895)
      ·
        refine ⟨879833176300535578885343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586555450867023719256895 879833176300535578885343)
        ·
          refine ⟨1319749764450803368328015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879833176300535578885343 1319749764450803368328015)
          ·
            refine ⟨1979624646676205052492023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319749764450803368328015 1979624646676205052492023)
            ·
              refine ⟨2969436970014307578738035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979624646676205052492023 2969436970014307578738035)
              ·
                refine ⟨4454155455021461368107053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969436970014307578738035 4454155455021461368107053)
                ·
                  refine ⟨1670308295633048013040145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4454155455021461368107053 1670308295633048013040145)
                  ·
                    refine ⟨1252731221724786009780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670308295633048013040145 1252731221724786009780109)
                    ·
                      refine ⟨469774208146794753667541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1252731221724786009780109 469774208146794753667541)
                      ·
                        rfl

theorem cell23_914882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_914882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914882 prefixEnd_914882 := by exact prefixLift 914882
  have htrace : WordTrace (prefixWord ++ tailWord_914882) baseStart_914882 baseEnd_914882 := by
    simpa [prefixWord, tailWord_914882, baseEnd_914882] using wordTrace_append hprefix tailTrace_914882
  have hstable : (prefixWord ++ tailWord_914882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914882).length < 2 ^ (prefixWord ++ tailWord_914882).sum := by decide
  have hdescent : baseEnd_914882 < baseStart_914882 := by decide
  rcases family_descends (prefixWord ++ tailWord_914882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914887 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_914887 : Nat := 118140960795 + 914887 * 2 ^ 59
def prefixEnd_914887 : Nat := 4983230072969 + 3 ^ 40 * 914887 * 2
def baseEnd_914887 : Nat := 469776775550067234105017

theorem tailTrace_914887 : CollatzResearch.WordTrace tailWord_914887 prefixEnd_914887 469776775550067234105017 := by
  unfold tailWord_914887
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368670236528124104990915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245780157685416069993943 33368670236528124104990915)
  ·
    refine ⟨50053005354792186157486373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368670236528124104990915 50053005354792186157486373)
    ·
      refine ⟨9384938504023534904528695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50053005354792186157486373 9384938504023534904528695)
      ·
        refine ⟨14077407756035302356793043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384938504023534904528695 14077407756035302356793043)
        ·
          refine ⟨21116111634052953535189565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14077407756035302356793043 21116111634052953535189565)
          ·
            refine ⟨7918541862769857575696087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21116111634052953535189565 7918541862769857575696087)
            ·
              refine ⟨11877812794154786363544131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918541862769857575696087 11877812794154786363544131)
              ·
                refine ⟨17816719191232179545316197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877812794154786363544131 17816719191232179545316197)
                ·
                  refine ⟨3340634848356033664746787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17816719191232179545316197 3340634848356033664746787)
                  ·
                    refine ⟨5010952272534050497120181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3340634848356033664746787 5010952272534050497120181)
                    ·
                      refine ⟨469776775550067234105017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5010952272534050497120181 469776775550067234105017)
                      ·
                        rfl

theorem cell23_914887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_914887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914887 prefixEnd_914887 := by exact prefixLift 914887
  have htrace : WordTrace (prefixWord ++ tailWord_914887) baseStart_914887 baseEnd_914887 := by
    simpa [prefixWord, tailWord_914887, baseEnd_914887] using wordTrace_append hprefix tailTrace_914887
  have hstable : (prefixWord ++ tailWord_914887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914887).length < 2 ^ (prefixWord ++ tailWord_914887).sum := by decide
  have hdescent : baseEnd_914887 < baseStart_914887 := by decide
  rcases family_descends (prefixWord ++ tailWord_914887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914897 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_914897 : Nat := 118140960795 + 914897 * 2 ^ 59
def prefixEnd_914897 : Nat := 4983230072969 + 3 ^ 40 * 914897 * 2
def baseEnd_914897 : Nat := 469781910356612194979971

theorem tailTrace_914897 : CollatzResearch.WordTrace tailWord_914897 prefixEnd_914897 469781910356612194979971 := by
  unfold tailWord_914897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33369034966491895812854945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22246023310994597208569963 33369034966491895812854945)
  ·
    refine ⟨25026776224868921859641209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33369034966491895812854945 25026776224868921859641209)
    ·
      refine ⟨18770082168651691394730907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25026776224868921859641209 18770082168651691394730907)
      ·
        refine ⟨28155123252977537092096361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18770082168651691394730907 28155123252977537092096361)
        ·
          refine ⟨21116342439733152819072271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28155123252977537092096361 21116342439733152819072271)
          ·
            refine ⟨31674513659599729228608407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21116342439733152819072271 31674513659599729228608407)
            ·
              refine ⟨47511770489399593842912611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31674513659599729228608407 47511770489399593842912611)
              ·
                refine ⟨71267655734099390764368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47511770489399593842912611 71267655734099390764368917)
                ·
                  refine ⟨3340671362535908942079793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71267655734099390764368917 3340671362535908942079793)
                  ·
                    refine ⟨2505503521901931706559845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340671362535908942079793 2505503521901931706559845)
                    ·
                      refine ⟨469781910356612194979971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2505503521901931706559845 469781910356612194979971)
                      ·
                        rfl

theorem cell23_914897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_914897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914897 prefixEnd_914897 := by exact prefixLift 914897
  have htrace : WordTrace (prefixWord ++ tailWord_914897) baseStart_914897 baseEnd_914897 := by
    simpa [prefixWord, tailWord_914897, baseEnd_914897] using wordTrace_append hprefix tailTrace_914897
  have hstable : (prefixWord ++ tailWord_914897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914897).length < 2 ^ (prefixWord ++ tailWord_914897).sum := by decide
  have hdescent : baseEnd_914897 < baseStart_914897 := by decide
  rcases family_descends (prefixWord ++ tailWord_914897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914901 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_914901 : Nat := 118140960795 + 914901 * 2 ^ 59
def prefixEnd_914901 : Nat := 4983230072969 + 3 ^ 40 * 914901 * 2
def baseEnd_914901 : Nat := 469783964279230179329953

theorem tailTrace_914901 : CollatzResearch.WordTrace tailWord_914901 prefixEnd_914901 469783964279230179329953 := by
  unfold tailWord_914901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33369180858477404496000557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22246120572318269664000371 33369180858477404496000557)
  ·
    refine ⟨12513442821929026686000209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33369180858477404496000557 12513442821929026686000209)
    ·
      refine ⟨9385082116446770014500157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12513442821929026686000209 9385082116446770014500157)
      ·
        refine ⟨3519405793667538755437559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9385082116446770014500157 3519405793667538755437559)
        ·
          refine ⟨5279108690501308133156339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519405793667538755437559 5279108690501308133156339)
          ·
            refine ⟨7918663035751962199734509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279108690501308133156339 7918663035751962199734509)
            ·
              refine ⟨2969498638406985824900441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7918663035751962199734509 2969498638406985824900441)
              ·
                refine ⟨2227123978805239368675331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969498638406985824900441 2227123978805239368675331)
                ·
                  refine ⟨3340685968207859053012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227123978805239368675331 3340685968207859053012997)
                  ·
                    refine ⟨626378619038973572439937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340685968207859053012997 626378619038973572439937)
                    ·
                      refine ⟨469783964279230179329953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626378619038973572439937 469783964279230179329953)
                      ·
                        rfl

theorem cell23_914901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_914901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914901 prefixEnd_914901 := by exact prefixLift 914901
  have htrace : WordTrace (prefixWord ++ tailWord_914901) baseStart_914901 baseEnd_914901 := by
    simpa [prefixWord, tailWord_914901, baseEnd_914901] using wordTrace_append hprefix tailTrace_914901
  have hstable : (prefixWord ++ tailWord_914901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914901).length < 2 ^ (prefixWord ++ tailWord_914901).sum := by decide
  have hdescent : baseEnd_914901 < baseStart_914901 := by decide
  rcases family_descends (prefixWord ++ tailWord_914901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914937 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_914937 : Nat := 118140960795 + 914937 * 2 ^ 59
def prefixEnd_914937 : Nat := 4983230072969 + 3 ^ 40 * 914937 * 2
def baseEnd_914937 : Nat := 156600816527597346159929

theorem tailTrace_914937 : CollatzResearch.WordTrace tailWord_914937 prefixEnd_914937 156600816527597346159929 := by
  unfold tailWord_914937
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370493886346982644311065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22246995924231321762874043 33370493886346982644311065)
  ·
    refine ⟨25027870414760236983233299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33370493886346982644311065 25027870414760236983233299)
    ·
      refine ⟨37541805622140355474849949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027870414760236983233299 37541805622140355474849949)
      ·
        refine ⟨14078177108302633303068731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37541805622140355474849949 14078177108302633303068731)
        ·
          refine ⟨21117265662453949954603097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14078177108302633303068731 21117265662453949954603097)
          ·
            refine ⟨15837949246840462465952323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21117265662453949954603097 15837949246840462465952323)
            ·
              refine ⟨23756923870260693698928485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15837949246840462465952323 23756923870260693698928485)
              ·
                refine ⟨4454423225673880068549091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23756923870260693698928485 4454423225673880068549091)
                ·
                  refine ⟨6681634838510820102823637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454423225673880068549091 6681634838510820102823637)
                  ·
                    refine ⟨156600816527597346159929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6681634838510820102823637 156600816527597346159929)
                    ·
                      rfl

theorem cell23_914937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_914937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914937 prefixEnd_914937 := by exact prefixLift 914937
  have htrace : WordTrace (prefixWord ++ tailWord_914937) baseStart_914937 baseEnd_914937 := by
    simpa [prefixWord, tailWord_914937, baseEnd_914937] using wordTrace_append hprefix tailTrace_914937
  have hstable : (prefixWord ++ tailWord_914937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914937).length < 2 ^ (prefixWord ++ tailWord_914937).sum := by decide
  have hdescent : baseEnd_914937 < baseStart_914937 := by decide
  rcases family_descends (prefixWord ++ tailWord_914937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914947 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_914947 : Nat := 118140960795 + 914947 * 2 ^ 59
def prefixEnd_914947 : Nat := 4983230072969 + 3 ^ 40 * 914947 * 2
def baseEnd_914947 : Nat := 469807584389336999354741

theorem tailTrace_914947 : CollatzResearch.WordTrace tailWord_914947 prefixEnd_914947 469807584389336999354741 := by
  unfold tailWord_914947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370858616310754352175095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22247239077540502901450063 33370858616310754352175095)
  ·
    refine ⟨50056287924466131528262643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370858616310754352175095 50056287924466131528262643)
    ·
      refine ⟨75084431886699197292393965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50056287924466131528262643 75084431886699197292393965)
      ·
        refine ⟨28156661957512198984647737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75084431886699197292393965 28156661957512198984647737)
        ·
          refine ⟨21117496468134149238485803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28156661957512198984647737 21117496468134149238485803)
          ·
            refine ⟨31676244702201223857728705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21117496468134149238485803 31676244702201223857728705)
            ·
              refine ⟨23757183526650917893296529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31676244702201223857728705 23757183526650917893296529)
              ·
                refine ⟨17817887644988188419972397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23757183526650917893296529 17817887644988188419972397)
                ·
                  refine ⟨6681707866870570657489649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17817887644988188419972397 6681707866870570657489649)
                  ·
                    refine ⟨5011280900152927993117237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681707866870570657489649 5011280900152927993117237)
                    ·
                      refine ⟨469807584389336999354741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5011280900152927993117237 469807584389336999354741)
                      ·
                        rfl

theorem cell23_914947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_914947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914947 prefixEnd_914947 := by exact prefixLift 914947
  have htrace : WordTrace (prefixWord ++ tailWord_914947) baseStart_914947 baseEnd_914947 := by
    simpa [prefixWord, tailWord_914947, baseEnd_914947] using wordTrace_append hprefix tailTrace_914947
  have hstable : (prefixWord ++ tailWord_914947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914947).length < 2 ^ (prefixWord ++ tailWord_914947).sum := by decide
  have hdescent : baseEnd_914947 < baseStart_914947 := by decide
  rcases family_descends (prefixWord ++ tailWord_914947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914954 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_914954 : Nat := 118140960795 + 914954 * 2 ^ 59
def prefixEnd_914954 : Nat := 4983230072969 + 3 ^ 40 * 914954 * 2
def baseEnd_914954 : Nat := 156603726251306157322403

theorem tailTrace_914954 : CollatzResearch.WordTrace tailWord_914954 prefixEnd_914954 156603726251306157322403 := by
  unfold tailWord_914954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342778481821348636919979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22247409284856929698453277 8342778481821348636919979)
  ·
    refine ⟨12514167722732022955379969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342778481821348636919979 12514167722732022955379969)
    ·
      refine ⟨9385625792049017216534977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12514167722732022955379969 9385625792049017216534977)
      ·
        refine ⟨7039219344036762912401233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9385625792049017216534977 7039219344036762912401233)
        ·
          refine ⟨5279414508027572184300925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7039219344036762912401233 5279414508027572184300925)
          ·
            refine ⟨1979780440510339569112847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5279414508027572184300925 1979780440510339569112847)
            ·
              refine ⟨2969670660765509353669271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979780440510339569112847 2969670660765509353669271)
              ·
                refine ⟨4454505991148264030503907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969670660765509353669271 4454505991148264030503907)
                ·
                  refine ⟨6681758986722396045755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454505991148264030503907 6681758986722396045755861)
                  ·
                    refine ⟨156603726251306157322403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6681758986722396045755861 156603726251306157322403)
                    ·
                      rfl

theorem cell23_914954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_914954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914954 prefixEnd_914954 := by exact prefixLift 914954
  have htrace : WordTrace (prefixWord ++ tailWord_914954) baseStart_914954 baseEnd_914954 := by
    simpa [prefixWord, tailWord_914954, baseEnd_914954] using wordTrace_append hprefix tailTrace_914954
  have hstable : (prefixWord ++ tailWord_914954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914954).length < 2 ^ (prefixWord ++ tailWord_914954).sum := by decide
  have hdescent : baseEnd_914954 < baseStart_914954 := by decide
  rcases family_descends (prefixWord ++ tailWord_914954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914958 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_914958 : Nat := 118140960795 + 914958 * 2 ^ 59
def prefixEnd_914958 : Nat := 4983230072969 + 3 ^ 40 * 914958 * 2
def baseEnd_914958 : Nat := 52201470297392939590799

theorem tailTrace_914958 : CollatzResearch.WordTrace tailWord_914958 prefixEnd_914958 52201470297392939590799 := by
  unfold tailWord_914958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171407477408862903853191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22247506546180602153883685 4171407477408862903853191)
  ·
    refine ⟨6257111216113294355779787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4171407477408862903853191 6257111216113294355779787)
    ·
      refine ⟨9385666824169941533669681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257111216113294355779787 9385666824169941533669681)
      ·
        refine ⟨7039250118127456150252261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9385666824169941533669681 7039250118127456150252261)
        ·
          refine ⟨1319859397148898028172299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7039250118127456150252261 1319859397148898028172299)
          ·
            refine ⟨1979789095723347042258449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319859397148898028172299 1979789095723347042258449)
            ·
              refine ⟨1484841821792510281693837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979789095723347042258449 1484841821792510281693837)
              ·
                refine ⟨556815683172191355635189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484841821792510281693837 556815683172191355635189)
                ·
                  refine ⟨52201470297392939590799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556815683172191355635189 52201470297392939590799)
                  ·
                    rfl

theorem cell23_914958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_914958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914958 prefixEnd_914958 := by exact prefixLift 914958
  have htrace : WordTrace (prefixWord ++ tailWord_914958) baseStart_914958 baseEnd_914958 := by
    simpa [prefixWord, tailWord_914958, baseEnd_914958] using wordTrace_append hprefix tailTrace_914958
  have hstable : (prefixWord ++ tailWord_914958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914958).length < 2 ^ (prefixWord ++ tailWord_914958).sum := by decide
  have hdescent : baseEnd_914958 < baseStart_914958 := by decide
  rcases family_descends (prefixWord ++ tailWord_914958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915001 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_915001 : Nat := 118140960795 + 915001 * 2 ^ 59
def prefixEnd_915001 : Nat := 4983230072969 + 3 ^ 40 * 915001 * 2
def baseEnd_915001 : Nat := 156611770781559929359831

theorem tailTrace_915001 : CollatzResearch.WordTrace tailWord_915001 prefixEnd_915001 156611770781559929359831 := by
  unfold tailWord_915001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372828158115121574640857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22248552105410081049760571 33372828158115121574640857)
  ·
    refine ⟨25029621118586341180980643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33372828158115121574640857 25029621118586341180980643)
    ·
      refine ⟨37544431677879511771470965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25029621118586341180980643 37544431677879511771470965)
      ·
        refine ⟨3519790469801204228575403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37544431677879511771470965 3519790469801204228575403)
        ·
          refine ⟨5279685704701806342863105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519790469801204228575403 5279685704701806342863105)
          ·
            refine ⟨3959764278526354757147329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279685704701806342863105 3959764278526354757147329)
            ·
              refine ⟨2969823208894766067860497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3959764278526354757147329 2969823208894766067860497)
              ·
                refine ⟨2227367406671074550895373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969823208894766067860497 2227367406671074550895373)
                ·
                  refine ⟨835262777501652956585765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2227367406671074550895373 835262777501652956585765)
                  ·
                    refine ⟨156611770781559929359831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835262777501652956585765 156611770781559929359831)
                    ·
                      rfl

theorem cell23_915001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_915001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915001 prefixEnd_915001 := by exact prefixLift 915001
  have htrace : WordTrace (prefixWord ++ tailWord_915001) baseStart_915001 baseEnd_915001 := by
    simpa [prefixWord, tailWord_915001, baseEnd_915001] using wordTrace_append hprefix tailTrace_915001
  have hstable : (prefixWord ++ tailWord_915001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915001).length < 2 ^ (prefixWord ++ tailWord_915001).sum := by decide
  have hdescent : baseEnd_915001 < baseStart_915001 := by decide
  rcases family_descends (prefixWord ++ tailWord_915001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915048 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 6]
def baseStart_915048 : Nat := 118140960795 + 915048 * 2 ^ 59
def prefixEnd_915048 : Nat := 4983230072969 + 3 ^ 40 * 915048 * 2
def baseEnd_915048 : Nat := 52206605103937900465753

theorem tailTrace_915048 : CollatzResearch.WordTrace tailWord_915048 prefixEnd_915048 52206605103937900465753 := by
  unfold tailWord_915048
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687271194472424300800899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22249694925963232401067865 16687271194472424300800899)
  ·
    refine ⟨25030906791708636451201349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16687271194472424300800899 25030906791708636451201349)
    ·
      refine ⟨4693295023445369334600253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25030906791708636451201349 4693295023445369334600253)
      ·
        refine ⟨1759985633792013500475095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4693295023445369334600253 1759985633792013500475095)
        ·
          refine ⟨2639978450688020250712643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759985633792013500475095 2639978450688020250712643)
          ·
            refine ⟨3959967676032030376068965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639978450688020250712643 3959967676032030376068965)
            ·
              refine ⟨742493939256005695512931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3959967676032030376068965 742493939256005695512931)
              ·
                refine ⟨1113740908884008543269397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742493939256005695512931 1113740908884008543269397)
                ·
                  refine ⟨52206605103937900465753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1113740908884008543269397 52206605103937900465753)
                  ·
                    rfl

theorem cell23_915048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_915048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915048 prefixEnd_915048 := by exact prefixLift 915048
  have htrace : WordTrace (prefixWord ++ tailWord_915048) baseStart_915048 baseEnd_915048 := by
    simpa [prefixWord, tailWord_915048, baseEnd_915048] using wordTrace_append hprefix tailTrace_915048
  have hstable : (prefixWord ++ tailWord_915048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915048).length < 2 ^ (prefixWord ++ tailWord_915048).sum := by decide
  have hdescent : baseEnd_915048 < baseStart_915048 := by decide
  rcases family_descends (prefixWord ++ tailWord_915048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915081 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_915081 : Nat := 118140960795 + 915081 * 2 ^ 59
def prefixEnd_915081 : Nat := 4983230072969 + 3 ^ 40 * 915081 * 2
def baseEnd_915081 : Nat := 469876390797039475079125

theorem tailTrace_915081 : CollatzResearch.WordTrace tailWord_915081 prefixEnd_915081 469876390797039475079125 := by
  unfold tailWord_915081
  simp only [CollatzResearch.WordTrace]
  refine ⟨33375745997825295237553097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22250497331883530158368731 33375745997825295237553097)
  ·
    refine ⟨25031809498368971428164823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33375745997825295237553097 25031809498368971428164823)
    ·
      refine ⟨37547714247553457142247235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25031809498368971428164823 37547714247553457142247235)
      ·
        refine ⟨56321571371330185713370853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37547714247553457142247235 56321571371330185713370853)
        ·
          refine ⟨10560294632124409821257035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56321571371330185713370853 10560294632124409821257035)
          ·
            refine ⟨15840441948186614731885553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10560294632124409821257035 15840441948186614731885553)
            ·
              refine ⟨11880331461139961048914165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15840441948186614731885553 11880331461139961048914165)
              ·
                refine ⟨1113781074481871348335703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11880331461139961048914165 1113781074481871348335703)
                ·
                  refine ⟨1670671611722807022503555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113781074481871348335703 1670671611722807022503555)
                  ·
                    refine ⟨2506007417584210533755333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670671611722807022503555 2506007417584210533755333)
                    ·
                      refine ⟨469876390797039475079125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2506007417584210533755333 469876390797039475079125)
                      ·
                        rfl

theorem cell23_915081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_915081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915081 prefixEnd_915081 := by exact prefixLift 915081
  have htrace : WordTrace (prefixWord ++ tailWord_915081) baseStart_915081 baseEnd_915081 := by
    simpa [prefixWord, tailWord_915081, baseEnd_915081] using wordTrace_append hprefix tailTrace_915081
  have hstable : (prefixWord ++ tailWord_915081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915081).length < 2 ^ (prefixWord ++ tailWord_915081).sum := by decide
  have hdescent : baseEnd_915081 < baseStart_915081 := by decide
  rcases family_descends (prefixWord ++ tailWord_915081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915108 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_915108 : Nat := 118140960795 + 915108 * 2 ^ 59
def prefixEnd_915108 : Nat := 4983230072969 + 3 ^ 40 * 915108 * 2
def baseEnd_915108 : Nat := 156630084924903623147167

theorem tailTrace_915108 : CollatzResearch.WordTrace tailWord_915108 prefixEnd_915108 156630084924903623147167 := by
  unfold tailWord_915108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688365384363739424392989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22251153845818319232523985 16688365384363739424392989)
  ·
    refine ⟨6258137019136402284147371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16688365384363739424392989 6258137019136402284147371)
    ·
      refine ⟨9387205528704603426221057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258137019136402284147371 9387205528704603426221057)
      ·
        refine ⟨7040404146528452569665793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9387205528704603426221057 7040404146528452569665793)
        ·
          refine ⟨5280303109896339427249345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7040404146528452569665793 5280303109896339427249345)
          ·
            refine ⟨3960227332422254570437009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280303109896339427249345 3960227332422254570437009)
            ·
              refine ⟨2970170499316690927827757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960227332422254570437009 2970170499316690927827757)
              ·
                refine ⟨1113813937243759097935409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970170499316690927827757 1113813937243759097935409)
                ·
                  refine ⟨835360452932819323451557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1113813937243759097935409 835360452932819323451557)
                  ·
                    refine ⟨156630084924903623147167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835360452932819323451557 156630084924903623147167)
                    ·
                      rfl

theorem cell23_915108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_915108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915108 prefixEnd_915108 := by exact prefixLift 915108
  have htrace : WordTrace (prefixWord ++ tailWord_915108) baseStart_915108 baseEnd_915108 := by
    simpa [prefixWord, tailWord_915108, baseEnd_915108] using wordTrace_append hprefix tailTrace_915108
  have hstable : (prefixWord ++ tailWord_915108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915108).length < 2 ^ (prefixWord ++ tailWord_915108).sum := by decide
  have hdescent : baseEnd_915108 < baseStart_915108 := by decide
  rcases family_descends (prefixWord ++ tailWord_915108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915132 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_915132 : Nat := 118140960795 + 915132 * 2 ^ 59
def prefixEnd_915132 : Nat := 4983230072969 + 3 ^ 40 * 915132 * 2
def baseEnd_915132 : Nat := 469902578310418775541391

theorem tailTrace_915132 : CollatzResearch.WordTrace tailWord_915132 prefixEnd_915132 469902578310418775541391 := by
  unfold tailWord_915132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688803060320265473829825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22251737413760353965106433 16688803060320265473829825)
  ·
    refine ⟨12516602295240199105372369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16688803060320265473829825 12516602295240199105372369)
    ·
      refine ⟨9387451721430149329029277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12516602295240199105372369 9387451721430149329029277)
      ·
        refine ⟨3520294395536305998385979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9387451721430149329029277 3520294395536305998385979)
        ·
          refine ⟨5280441593304458997578969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520294395536305998385979 5280441593304458997578969)
          ·
            refine ⟨3960331194978344248184227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280441593304458997578969 3960331194978344248184227)
            ·
              refine ⟨5940496792467516372276341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960331194978344248184227 5940496792467516372276341)
              ·
                refine ⟨556921574293829659900907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5940496792467516372276341 556921574293829659900907)
                ·
                  refine ⟨835382361440744489851361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556921574293829659900907 835382361440744489851361)
                  ·
                    refine ⟨626536771080558367388521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835382361440744489851361 626536771080558367388521)
                    ·
                      refine ⟨469902578310418775541391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626536771080558367388521 469902578310418775541391)
                      ·
                        rfl

theorem cell23_915132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_915132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915132 prefixEnd_915132 := by exact prefixLift 915132
  have htrace : WordTrace (prefixWord ++ tailWord_915132) baseStart_915132 baseEnd_915132 := by
    simpa [prefixWord, tailWord_915132, baseEnd_915132] using wordTrace_append hprefix tailTrace_915132
  have hstable : (prefixWord ++ tailWord_915132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915132).length < 2 ^ (prefixWord ++ tailWord_915132).sum := by decide
  have hdescent : baseEnd_915132 < baseStart_915132 := by decide
  rcases family_descends (prefixWord ++ tailWord_915132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915142 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_915142 : Nat := 118140960795 + 915142 * 2 ^ 59
def prefixEnd_915142 : Nat := 4983230072969 + 3 ^ 40 * 915142 * 2
def baseEnd_915142 : Nat := 156635904372321245472115

theorem tailTrace_915142 : CollatzResearch.WordTrace tailWord_915142 prefixEnd_915142 156635904372321245472115 := by
  unfold tailWord_915142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043061589081384457985115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22251980567069535103682453 1043061589081384457985115)
  ·
    refine ⟨1564592383622076686977673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043061589081384457985115 1564592383622076686977673)
    ·
      refine ⟨1173444287716557515233255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564592383622076686977673 1173444287716557515233255)
      ·
        refine ⟨1760166431574836272849883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173444287716557515233255 1760166431574836272849883)
        ·
          refine ⟨2640249647362254409274825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760166431574836272849883 2640249647362254409274825)
          ·
            refine ⟨1980187235521690806956119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640249647362254409274825 1980187235521690806956119)
            ·
              refine ⟨2970280853282536210434179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980187235521690806956119 2970280853282536210434179)
              ·
                refine ⟨4455421279923804315651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970280853282536210434179 4455421279923804315651269)
                ·
                  refine ⟨835391489985713309184613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4455421279923804315651269 835391489985713309184613)
                  ·
                    refine ⟨156635904372321245472115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835391489985713309184613 156635904372321245472115)
                    ·
                      rfl

theorem cell23_915142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_915142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915142 prefixEnd_915142 := by exact prefixLift 915142
  have htrace : WordTrace (prefixWord ++ tailWord_915142) baseStart_915142 baseEnd_915142 := by
    simpa [prefixWord, tailWord_915142, baseEnd_915142] using wordTrace_append hprefix tailTrace_915142
  have hstable : (prefixWord ++ tailWord_915142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915142).length < 2 ^ (prefixWord ++ tailWord_915142).sum := by decide
  have hdescent : baseEnd_915142 < baseStart_915142 := by decide
  rcases family_descends (prefixWord ++ tailWord_915142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915149 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_915149 : Nat := 118140960795 + 915149 * 2 ^ 59
def prefixEnd_915149 : Nat := 4983230072969 + 3 ^ 40 * 915149 * 2
def baseEnd_915149 : Nat := 469911307481545209028813

theorem tailTrace_915149 : CollatzResearch.WordTrace tailWord_915149 prefixEnd_915149 469911307481545209028813 := by
  unfold tailWord_915149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33378226161578942851028501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22252150774385961900685667 33378226161578942851028501)
  ·
    refine ⟨1564604351324012946141961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33378226161578942851028501 1564604351324012946141961)
    ·
      refine ⟨1173453263493009709606471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564604351324012946141961 1173453263493009709606471)
      ·
        refine ⟨1760179895239514564409707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173453263493009709606471 1760179895239514564409707)
        ·
          refine ⟨2640269842859271846614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760179895239514564409707 2640269842859271846614561)
          ·
            refine ⟨1980202382144453884960921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640269842859271846614561 1980202382144453884960921)
            ·
              refine ⟨1485151786608340413720691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980202382144453884960921 1485151786608340413720691)
              ·
                refine ⟨2227727679912510620581037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485151786608340413720691 2227727679912510620581037)
                ·
                  refine ⟨835397879967191482717889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2227727679912510620581037 835397879967191482717889)
                  ·
                    refine ⟨626548409975393612038417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835397879967191482717889 626548409975393612038417)
                    ·
                      refine ⟨469911307481545209028813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626548409975393612038417 469911307481545209028813)
                      ·
                        rfl

theorem cell23_915149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_915149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915149 prefixEnd_915149 := by exact prefixLift 915149
  have htrace : WordTrace (prefixWord ++ tailWord_915149) baseStart_915149 baseEnd_915149 := by
    simpa [prefixWord, tailWord_915149, baseEnd_915149] using wordTrace_append hprefix tailTrace_915149
  have hstable : (prefixWord ++ tailWord_915149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915149).length < 2 ^ (prefixWord ++ tailWord_915149).sum := by decide
  have hdescent : baseEnd_915149 < baseStart_915149 := by decide
  rcases family_descends (prefixWord ++ tailWord_915149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915201 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_915201 : Nat := 118140960795 + 915201 * 2 ^ 59
def prefixEnd_915201 : Nat := 4983230072969 + 3 ^ 40 * 915201 * 2
def baseEnd_915201 : Nat := 469938008475579005578573

theorem tailTrace_915201 : CollatzResearch.WordTrace tailWord_915201 prefixEnd_915201 469938008475579005578573 := by
  unfold tailWord_915201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380122757390555731921457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22253415171593703821280971 33380122757390555731921457)
  ·
    refine ⟨25035092068042916798941093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33380122757390555731921457 25035092068042916798941093)
    ·
      refine ⟨4694079762758046899801455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25035092068042916798941093 4694079762758046899801455)
      ·
        refine ⟨7041119644137070349702183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694079762758046899801455 7041119644137070349702183)
        ·
          refine ⟨10561679466205605524553275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041119644137070349702183 10561679466205605524553275)
          ·
            refine ⟨15842519199308408286829913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561679466205605524553275 15842519199308408286829913)
            ·
              refine ⟨11881889399481306215122435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15842519199308408286829913 11881889399481306215122435)
              ·
                refine ⟨17822834099221959322683653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11881889399481306215122435 17822834099221959322683653)
                ·
                  refine ⟨3341781393604117373003185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17822834099221959322683653 3341781393604117373003185)
                  ·
                    refine ⟨2506336045203088029752389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341781393604117373003185 2506336045203088029752389)
                    ·
                      refine ⟨469938008475579005578573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2506336045203088029752389 469938008475579005578573)
                      ·
                        rfl

theorem cell23_915201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_915201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915201 prefixEnd_915201 := by exact prefixLift 915201
  have htrace : WordTrace (prefixWord ++ tailWord_915201) baseStart_915201 baseEnd_915201 := by
    simpa [prefixWord, tailWord_915201, baseEnd_915201] using wordTrace_append hprefix tailTrace_915201
  have hstable : (prefixWord ++ tailWord_915201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915201).length < 2 ^ (prefixWord ++ tailWord_915201).sum := by decide
  have hdescent : baseEnd_915201 < baseStart_915201 := by decide
  rcases family_descends (prefixWord ++ tailWord_915201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915211 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 7]
def baseStart_915211 : Nat := 118140960795 + 915211 * 2 ^ 59
def prefixEnd_915211 : Nat := 4983230072969 + 3 ^ 40 * 915211 * 2
def baseEnd_915211 : Nat := 52215904809124885161503

theorem tailTrace_915211 : CollatzResearch.WordTrace tailWord_915211 prefixEnd_915211 52215904809124885161503 := by
  unfold tailWord_915211
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380487487354327439785487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22253658324902884959856991 33380487487354327439785487)
  ·
    refine ⟨50070731231031491159678231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33380487487354327439785487 50070731231031491159678231)
    ·
      refine ⟨75106096846547236739517347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50070731231031491159678231 75106096846547236739517347)
      ·
        refine ⟨112659145269820855109276021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75106096846547236739517347 112659145269820855109276021)
        ·
          refine ⟨10561794869045705166494627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112659145269820855109276021 10561794869045705166494627)
          ·
            refine ⟨15842692303568557749741941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561794869045705166494627 15842692303568557749741941)
            ·
              refine ⟨1485252403459552289038307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15842692303568557749741941 1485252403459552289038307)
              ·
                refine ⟨2227878605189328433557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485252403459552289038307 2227878605189328433557461)
                ·
                  refine ⟨52215904809124885161503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2227878605189328433557461 52215904809124885161503)
                  ·
                    rfl

theorem cell23_915211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 7].length) (baseStart_915211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915211 prefixEnd_915211 := by exact prefixLift 915211
  have htrace : WordTrace (prefixWord ++ tailWord_915211) baseStart_915211 baseEnd_915211 := by
    simpa [prefixWord, tailWord_915211, baseEnd_915211] using wordTrace_append hprefix tailTrace_915211
  have hstable : (prefixWord ++ tailWord_915211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915211).length < 2 ^ (prefixWord ++ tailWord_915211).sum := by decide
  have hdescent : baseEnd_915211 < baseStart_915211 := by decide
  rcases family_descends (prefixWord ++ tailWord_915211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915258 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_915258 : Nat := 118140960795 + 915258 * 2 ^ 59
def prefixEnd_915258 : Nat := 4983230072969 + 3 ^ 40 * 915258 * 2
def baseEnd_915258 : Nat := 156655758957628427521937

theorem tailTrace_915258 : CollatzResearch.WordTrace tailWord_915258 prefixEnd_915258 156655758957628427521937 := by
  unfold tailWord_915258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345550429546013616686607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22254801145456036311164285 8345550429546013616686607)
  ·
    refine ⟨12518325644319020425029911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8345550429546013616686607 12518325644319020425029911)
    ·
      refine ⟨18777488466478530637544867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518325644319020425029911 18777488466478530637544867)
      ·
        refine ⟨28166232699717795956317301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777488466478530637544867 28166232699717795956317301)
        ·
          refine ⟨2640584315598543370904747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28166232699717795956317301 2640584315598543370904747)
          ·
            refine ⟨3960876473397815056357121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640584315598543370904747 3960876473397815056357121)
            ·
              refine ⟨2970657355048361292267841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960876473397815056357121 2970657355048361292267841)
              ·
                refine ⟨2227993016286270969200881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970657355048361292267841 2227993016286270969200881)
                ·
                  refine ⟨1670994762214703226900661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227993016286270969200881 1670994762214703226900661)
                  ·
                    refine ⟨156655758957628427521937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1670994762214703226900661 156655758957628427521937)
                    ·
                      rfl

theorem cell23_915258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_915258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915258 prefixEnd_915258 := by exact prefixLift 915258
  have htrace : WordTrace (prefixWord ++ tailWord_915258) baseStart_915258 baseEnd_915258 := by
    simpa [prefixWord, tailWord_915258, baseEnd_915258] using wordTrace_append hprefix tailTrace_915258
  have hstable : (prefixWord ++ tailWord_915258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915258).length < 2 ^ (prefixWord ++ tailWord_915258).sum := by decide
  have hdescent : baseEnd_915258 < baseStart_915258 := by decide
  rcases family_descends (prefixWord ++ tailWord_915258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915262 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_915262 : Nat := 118140960795 + 915262 * 2 ^ 59
def prefixEnd_915262 : Nat := 4983230072969 + 3 ^ 40 * 915262 * 2
def baseEnd_915262 : Nat := 52218814532833696323977

theorem tailTrace_915262 : CollatzResearch.WordTrace tailWord_915262 prefixEnd_915262 52218814532833696323977 := by
  unfold tailWord_915262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172793451271195393736505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22254898406779708766594693 4172793451271195393736505)
  ·
    refine ⟨3129595088453396545302379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4172793451271195393736505 3129595088453396545302379)
    ·
      refine ⟨4694392632680094817953569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129595088453396545302379 4694392632680094817953569)
      ·
        refine ⟨3520794474510071113465177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694392632680094817953569 3520794474510071113465177)
        ·
          refine ⟨2640595855882553335098883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520794474510071113465177 2640595855882553335098883)
          ·
            refine ⟨3960893783823830002648325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640595855882553335098883 3960893783823830002648325)
            ·
              refine ⟨742667584466968125496561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3960893783823830002648325 742667584466968125496561)
              ·
                refine ⟨557000688350226094122421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742667584466968125496561 557000688350226094122421)
                ·
                  refine ⟨52218814532833696323977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557000688350226094122421 52218814532833696323977)
                  ·
                    rfl

theorem cell23_915262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_915262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915262 prefixEnd_915262 := by exact prefixLift 915262
  have htrace : WordTrace (prefixWord ++ tailWord_915262) baseStart_915262 baseEnd_915262 := by
    simpa [prefixWord, tailWord_915262, baseEnd_915262] using wordTrace_append hprefix tailTrace_915262
  have hstable : (prefixWord ++ tailWord_915262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915262).length < 2 ^ (prefixWord ++ tailWord_915262).sum := by decide
  have hdescent : baseEnd_915262 < baseStart_915262 := by decide
  rcases family_descends (prefixWord ++ tailWord_915262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915292 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_915292 : Nat := 118140960795 + 915292 * 2 ^ 59
def prefixEnd_915292 : Nat := 4983230072969 + 3 ^ 40 * 915292 * 2
def baseEnd_915292 : Nat := 156661578405046049846885

theorem tailTrace_915292 : CollatzResearch.WordTrace tailWord_915292 prefixEnd_915292 156661578405046049846885 := by
  unfold tailWord_915292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691720900030439136742065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22255627866707252182322753 16691720900030439136742065)
  ·
    refine ⟨12518790675022829352556549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16691720900030439136742065 12518790675022829352556549)
    ·
      refine ⟨2347273251566780503604353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12518790675022829352556549 2347273251566780503604353)
      ·
        refine ⟨1760454938675085377703265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2347273251566780503604353 1760454938675085377703265)
        ·
          refine ⟨1320341204006314033277449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760454938675085377703265 1320341204006314033277449)
          ·
            refine ⟨990255903004735524958087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320341204006314033277449 990255903004735524958087)
            ·
              refine ⟨1485383854507103287437131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990255903004735524958087 1485383854507103287437131)
              ·
                refine ⟨2228075781760654931155697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485383854507103287437131 2228075781760654931155697)
                ·
                  refine ⟨1671056836320491198366773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228075781760654931155697 1671056836320491198366773)
                  ·
                    refine ⟨156661578405046049846885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1671056836320491198366773 156661578405046049846885)
                    ·
                      rfl

theorem cell23_915292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_915292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915292 prefixEnd_915292 := by exact prefixLift 915292
  have htrace : WordTrace (prefixWord ++ tailWord_915292) baseStart_915292 baseEnd_915292 := by
    simpa [prefixWord, tailWord_915292, baseEnd_915292] using wordTrace_append hprefix tailTrace_915292
  have hstable : (prefixWord ++ tailWord_915292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915292).length < 2 ^ (prefixWord ++ tailWord_915292).sum := by decide
  have hdescent : baseEnd_915292 < baseStart_915292 := by decide
  rcases family_descends (prefixWord ++ tailWord_915292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915295 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_915295 : Nat := 118140960795 + 915295 * 2 ^ 59
def prefixEnd_915295 : Nat := 4983230072969 + 3 ^ 40 * 915295 * 2
def baseEnd_915295 : Nat := 469986275657101637803141

theorem tailTrace_915295 : CollatzResearch.WordTrace tailWord_915295 prefixEnd_915295 469986275657101637803141 := by
  unfold tailWord_915295
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383551219050009785843339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22255700812700006523895559 33383551219050009785843339)
  ·
    refine ⟨50075326828575014678765009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33383551219050009785843339 50075326828575014678765009)
    ·
      refine ⟨37556495121431261009073757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50075326828575014678765009 37556495121431261009073757)
      ·
        refine ⟨14083685670536722878402659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37556495121431261009073757 14083685670536722878402659)
        ·
          refine ⟨21125528505805084317603989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083685670536722878402659 21125528505805084317603989)
          ·
            refine ⟨990259148709613327387687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21125528505805084317603989 990259148709613327387687)
            ·
              refine ⟨1485388723064419991081531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990259148709613327387687 1485388723064419991081531)
              ·
                refine ⟨2228083084596629986622297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485388723064419991081531 2228083084596629986622297)
                ·
                  refine ⟨1671062313447472489966723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228083084596629986622297 1671062313447472489966723)
                  ·
                    refine ⟨2506593470171208734950085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1671062313447472489966723 2506593470171208734950085)
                    ·
                      refine ⟨469986275657101637803141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2506593470171208734950085 469986275657101637803141)
                      ·
                        rfl

theorem cell23_915295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_915295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915295 prefixEnd_915295 := by exact prefixLift 915295
  have htrace : WordTrace (prefixWord ++ tailWord_915295) baseStart_915295 baseEnd_915295 := by
    simpa [prefixWord, tailWord_915295, baseEnd_915295] using wordTrace_append hprefix tailTrace_915295
  have hstable : (prefixWord ++ tailWord_915295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915295).length < 2 ^ (prefixWord ++ tailWord_915295).sum := by decide
  have hdescent : baseEnd_915295 < baseStart_915295 := by decide
  rcases family_descends (prefixWord ++ tailWord_915295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915301 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 8]
def baseStart_915301 : Nat := 118140960795 + 915301 * 2 ^ 59
def prefixEnd_915301 : Nat := 4983230072969 + 3 ^ 40 * 915301 * 2
def baseEnd_915301 : Nat := 52221039615669846036457

theorem tailTrace_915301 : CollatzResearch.WordTrace tailWord_915301 prefixEnd_915301 52221039615669846036457 := by
  unfold tailWord_915301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383770057028272810561757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22255846704685515207041171 33383770057028272810561757)
  ·
    refine ⟨12518913771385602303960659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33383770057028272810561757 12518913771385602303960659)
    ·
      refine ⟨18778370657078403455940989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518913771385602303960659 18778370657078403455940989)
      ·
        refine ⟨7041888996404401295977871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18778370657078403455940989 7041888996404401295977871)
        ·
          refine ⟨10562833494606601943966807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041888996404401295977871 10562833494606601943966807)
          ·
            refine ⟨15844250241909902915950211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562833494606601943966807 15844250241909902915950211)
            ·
              refine ⟨23766375362864854373925317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844250241909902915950211 23766375362864854373925317)
              ·
                refine ⟨4456195380537160195110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23766375362864854373925317 4456195380537160195110997)
                ·
                  refine ⟨52221039615669846036457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4456195380537160195110997 52221039615669846036457)
                  ·
                    rfl

theorem cell23_915301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_915301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915301 prefixEnd_915301 := by exact prefixLift 915301
  have htrace : WordTrace (prefixWord ++ tailWord_915301) baseStart_915301 baseEnd_915301 := by
    simpa [prefixWord, tailWord_915301, baseEnd_915301] using wordTrace_append hprefix tailTrace_915301
  have hstable : (prefixWord ++ tailWord_915301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915301).length < 2 ^ (prefixWord ++ tailWord_915301).sum := by decide
  have hdescent : baseEnd_915301 < baseStart_915301 := by decide
  rcases family_descends (prefixWord ++ tailWord_915301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915321 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_915321 : Nat := 118140960795 + 915321 * 2 ^ 59
def prefixEnd_915321 : Nat := 4983230072969 + 3 ^ 40 * 915321 * 2
def baseEnd_915321 : Nat := 469999626154118536078021

theorem tailTrace_915321 : CollatzResearch.WordTrace tailWord_915321 prefixEnd_915321 469999626154118536078021 := by
  unfold tailWord_915321
  simp only [CollatzResearch.WordTrace]
  refine ⟨33384499516955816226289817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22256333011303877484193211 33384499516955816226289817)
  ·
    refine ⟨25038374637716862169717363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33384499516955816226289817 25038374637716862169717363)
    ·
      refine ⟨37557561956575293254576045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25038374637716862169717363 37557561956575293254576045)
      ·
        refine ⟨14084085733715734970466017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37557561956575293254576045 14084085733715734970466017)
        ·
          refine ⟨10563064300286801227849513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14084085733715734970466017 10563064300286801227849513)
          ·
            refine ⟨7922298225215100920887135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563064300286801227849513 7922298225215100920887135)
            ·
              refine ⟨11883447337822651381330703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922298225215100920887135 11883447337822651381330703)
              ·
                refine ⟨17825171006733977071996055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883447337822651381330703 17825171006733977071996055)
                ·
                  refine ⟨26737756510100965607994083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17825171006733977071996055 26737756510100965607994083)
                  ·
                    refine ⟨40106634765151448411991125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26737756510100965607994083 40106634765151448411991125)
                    ·
                      refine ⟨469999626154118536078021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 40106634765151448411991125 469999626154118536078021)
                      ·
                        rfl

theorem cell23_915321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_915321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915321 prefixEnd_915321 := by exact prefixLift 915321
  have htrace : WordTrace (prefixWord ++ tailWord_915321) baseStart_915321 baseEnd_915321 := by
    simpa [prefixWord, tailWord_915321, baseEnd_915321] using wordTrace_append hprefix tailTrace_915321
  have hstable : (prefixWord ++ tailWord_915321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915321).length < 2 ^ (prefixWord ++ tailWord_915321).sum := by decide
  have hdescent : baseEnd_915321 < baseStart_915321 := by decide
  rcases family_descends (prefixWord ++ tailWord_915321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915345 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_915345 : Nat := 118140960795 + 915345 * 2 ^ 59
def prefixEnd_915345 : Nat := 4983230072969 + 3 ^ 40 * 915345 * 2
def baseEnd_915345 : Nat := 470011949689826442177911

theorem tailTrace_915345 : CollatzResearch.WordTrace tailWord_915345 prefixEnd_915345 470011949689826442177911 := by
  unfold tailWord_915345
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385374868868868325163489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22256916579245912216775659 33385374868868868325163489)
  ·
    refine ⟨25039031151651651243872617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33385374868868868325163489 25039031151651651243872617)
    ·
      refine ⟨18779273363738738432904463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25039031151651651243872617 18779273363738738432904463)
      ·
        refine ⟨28168910045608107649356695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18779273363738738432904463 28168910045608107649356695)
        ·
          refine ⟨42253365068412161474035043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28168910045608107649356695 42253365068412161474035043)
          ·
            refine ⟨63380047602618242211052565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42253365068412161474035043 63380047602618242211052565)
            ·
              refine ⟨2970939731372730103643089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63380047602618242211052565 2970939731372730103643089)
              ·
                refine ⟨2228204798529547577732317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970939731372730103643089 2228204798529547577732317)
                ·
                  refine ⟨835576799448580341649619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228204798529547577732317 835576799448580341649619)
                  ·
                    refine ⟨1253365199172870512474429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835576799448580341649619 1253365199172870512474429)
                    ·
                      refine ⟨470011949689826442177911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1253365199172870512474429 470011949689826442177911)
                      ·
                        rfl

theorem cell23_915345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_915345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915345 prefixEnd_915345 := by exact prefixLift 915345
  have htrace : WordTrace (prefixWord ++ tailWord_915345) baseStart_915345 baseEnd_915345 := by
    simpa [prefixWord, tailWord_915345, baseEnd_915345] using wordTrace_append hprefix tailTrace_915345
  have hstable : (prefixWord ++ tailWord_915345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915345).length < 2 ^ (prefixWord ++ tailWord_915345).sum := by decide
  have hdescent : baseEnd_915345 < baseStart_915345 := by decide
  rcases family_descends (prefixWord ++ tailWord_915345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915379 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 1, 1, 3]
def baseStart_915379 : Nat := 118140960795 + 915379 * 2 ^ 59
def prefixEnd_915379 : Nat := 4983230072969 + 3 ^ 40 * 915379 * 2
def baseEnd_915379 : Nat := 470029408032079309152755

theorem tailTrace_915379 : CollatzResearch.WordTrace tailWord_915379 prefixEnd_915379 470029408032079309152755 := by
  unfold tailWord_915379
  simp only [CollatzResearch.WordTrace]
  refine ⟨33386614950745692131901191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22257743300497128087934127 33386614950745692131901191)
  ·
    refine ⟨50079922426118538197851787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33386614950745692131901191 50079922426118538197851787)
    ·
      refine ⟨75119883639177807296777681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50079922426118538197851787 75119883639177807296777681)
      ·
        refine ⟨56339912729383355472583261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75119883639177807296777681 56339912729383355472583261)
        ·
          refine ⟨21127467273518758302218723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56339912729383355472583261 21127467273518758302218723)
          ·
            refine ⟨31691200910278137453328085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127467273518758302218723 31691200910278137453328085)
            ·
              refine ⟨742762521334643846562377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31691200910278137453328085 742762521334643846562377)
              ·
                refine ⟨557071891000982884921783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742762521334643846562377 557071891000982884921783)
                ·
                  refine ⟨835607836501474327382675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557071891000982884921783 835607836501474327382675)
                  ·
                    refine ⟨1253411754752211491074013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835607836501474327382675 1253411754752211491074013)
                    ·
                      refine ⟨470029408032079309152755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1253411754752211491074013 470029408032079309152755)
                      ·
                        rfl

theorem cell23_915379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 1, 3].length) (baseStart_915379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915379 prefixEnd_915379 := by exact prefixLift 915379
  have htrace : WordTrace (prefixWord ++ tailWord_915379) baseStart_915379 baseEnd_915379 := by
    simpa [prefixWord, tailWord_915379, baseEnd_915379] using wordTrace_append hprefix tailTrace_915379
  have hstable : (prefixWord ++ tailWord_915379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915379).length < 2 ^ (prefixWord ++ tailWord_915379).sum := by decide
  have hdescent : baseEnd_915379 < baseStart_915379 := by decide
  rcases family_descends (prefixWord ++ tailWord_915379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915402 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_915402 : Nat := 118140960795 + 915402 * 2 ^ 59
def prefixEnd_915402 : Nat := 4983230072969 + 3 ^ 40 * 915402 * 2
def baseEnd_915402 : Nat := 470041218087132719165149

theorem tailTrace_915402 : CollatzResearch.WordTrace tailWord_915402 prefixEnd_915402 470041218087132719165149 := by
  unfold tailWord_915402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346863457415591764997115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22258302553108244706658973 8346863457415591764997115)
  ·
    refine ⟨12520295186123387647495673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346863457415591764997115 12520295186123387647495673)
    ·
      refine ⟨9390221389592540735621755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12520295186123387647495673 9390221389592540735621755)
      ·
        refine ⟨14085332084388811103432633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9390221389592540735621755 14085332084388811103432633)
        ·
          refine ⟨10563999063291608327574475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14085332084388811103432633 10563999063291608327574475)
          ·
            refine ⟨15845998594937412491361713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563999063291608327574475 15845998594937412491361713)
            ·
              refine ⟨11884498946203059368521285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15845998594937412491361713 11884498946203059368521285)
              ·
                refine ⟨2228343552413073631597741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11884498946203059368521285 2228343552413073631597741)
                ·
                  refine ⟨835628832154902611849153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228343552413073631597741 835628832154902611849153)
                  ·
                    refine ⟨626721624116176958886865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835628832154902611849153 626721624116176958886865)
                    ·
                      refine ⟨470041218087132719165149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626721624116176958886865 470041218087132719165149)
                      ·
                        rfl

theorem cell23_915402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_915402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915402 prefixEnd_915402 := by exact prefixLift 915402
  have htrace : WordTrace (prefixWord ++ tailWord_915402) baseStart_915402 baseEnd_915402 := by
    simpa [prefixWord, tailWord_915402, baseEnd_915402] using wordTrace_append hprefix tailTrace_915402
  have hstable : (prefixWord ++ tailWord_915402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915402).length < 2 ^ (prefixWord ++ tailWord_915402).sum := by decide
  have hdescent : baseEnd_915402 < baseStart_915402 := by decide
  rcases family_descends (prefixWord ++ tailWord_915402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915435 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 3]
def baseStart_915435 : Nat := 118140960795 + 915435 * 2 ^ 59
def prefixEnd_915435 : Nat := 4983230072969 + 3 ^ 40 * 915435 * 2
def baseEnd_915435 : Nat := 470058162948731090052497

theorem tailTrace_915435 : CollatzResearch.WordTrace tailWord_915435 prefixEnd_915435 470058162948731090052497 := by
  unfold tailWord_915435
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388657438542813695939759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22259104959028542463959839 33388657438542813695939759)
  ·
    refine ⟨50082986157814220543909639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388657438542813695939759 50082986157814220543909639)
    ·
      refine ⟨75124479236721330815864459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50082986157814220543909639 75124479236721330815864459)
      ·
        refine ⟨112686718855081996223796689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75124479236721330815864459 112686718855081996223796689)
        ·
          refine ⟨84515039141311497167847517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112686718855081996223796689 84515039141311497167847517)
          ·
            refine ⟨31693139677991811437942819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84515039141311497167847517 31693139677991811437942819)
            ·
              refine ⟨47539709516987717156914229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31693139677991811437942819 47539709516987717156914229)
              ·
                refine ⟨4456847767217598483460709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47539709516987717156914229 4456847767217598483460709)
                ·
                  refine ⟨835658956353299715648883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4456847767217598483460709 835658956353299715648883)
                  ·
                    refine ⟨1253488434529949573473325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835658956353299715648883 1253488434529949573473325)
                    ·
                      refine ⟨470058162948731090052497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1253488434529949573473325 470058162948731090052497)
                      ·
                        rfl

theorem cell23_915435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 3].length) (baseStart_915435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915435 prefixEnd_915435 := by exact prefixLift 915435
  have htrace : WordTrace (prefixWord ++ tailWord_915435) baseStart_915435 baseEnd_915435 := by
    simpa [prefixWord, tailWord_915435, baseEnd_915435] using wordTrace_append hprefix tailTrace_915435
  have hstable : (prefixWord ++ tailWord_915435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915435).length < 2 ^ (prefixWord ++ tailWord_915435).sum := by decide
  have hdescent : baseEnd_915435 < baseStart_915435 := by decide
  rcases family_descends (prefixWord ++ tailWord_915435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915452 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_915452 : Nat := 118140960795 + 915452 * 2 ^ 59
def prefixEnd_915452 : Nat := 4983230072969 + 3 ^ 40 * 915452 * 2
def baseEnd_915452 : Nat := 470066892119857523539919

theorem tailTrace_915452 : CollatzResearch.WordTrace tailWord_915452 prefixEnd_915452 470066892119857523539919 := by
  unfold tailWord_915452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694638739740612799654305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22259518319654150399539073 16694638739740612799654305)
  ·
    refine ⟨12520979054805459599740729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694638739740612799654305 12520979054805459599740729)
    ·
      refine ⟨9390734291104094699805547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12520979054805459599740729 9390734291104094699805547)
      ·
        refine ⟨14086101436656142049708321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9390734291104094699805547 14086101436656142049708321)
        ·
          refine ⟨10564576077492106537281241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14086101436656142049708321 10564576077492106537281241)
          ·
            refine ⟨7923432058119079902960931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10564576077492106537281241 7923432058119079902960931)
            ·
              refine ⟨11885148087178619854441397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923432058119079902960931 11885148087178619854441397)
              ·
                refine ⟨1114232633172995611353881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11885148087178619854441397 1114232633172995611353881)
                ·
                  refine ⟨835674474879746708515411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114232633172995611353881 835674474879746708515411)
                  ·
                    refine ⟨1253511712319620062773117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835674474879746708515411 1253511712319620062773117)
                    ·
                      refine ⟨470066892119857523539919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1253511712319620062773117 470066892119857523539919)
                      ·
                        rfl

theorem cell23_915452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_915452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915452 prefixEnd_915452 := by exact prefixLift 915452
  have htrace : WordTrace (prefixWord ++ tailWord_915452) baseStart_915452 baseEnd_915452 := by
    simpa [prefixWord, tailWord_915452, baseEnd_915452] using wordTrace_append hprefix tailTrace_915452
  have hstable : (prefixWord ++ tailWord_915452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915452).length < 2 ^ (prefixWord ++ tailWord_915452).sum := by decide
  have hdescent : baseEnd_915452 < baseStart_915452 := by decide
  rcases family_descends (prefixWord ++ tailWord_915452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915468 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_915468 : Nat := 118140960795 + 915468 * 2 ^ 59
def prefixEnd_915468 : Nat := 4983230072969 + 3 ^ 40 * 915468 * 2
def baseEnd_915468 : Nat := 156691702603443153646615

theorem tailTrace_915468 : CollatzResearch.WordTrace tailWord_915468 prefixEnd_915468 156691702603443153646615 := by
  unfold tailWord_915468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694930523711630165945529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22259907364948840221260705 16694930523711630165945529)
  ·
    refine ⟨12521197892783722624459147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694930523711630165945529 12521197892783722624459147)
    ·
      refine ⟨18781796839175583936688721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521197892783722624459147 18781796839175583936688721)
      ·
        refine ⟨14086347629381687952516541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18781796839175583936688721 14086347629381687952516541)
        ·
          refine ⟨5282380361018132982193703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14086347629381687952516541 5282380361018132982193703)
          ·
            refine ⟨7923570541527199473290555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282380361018132982193703 7923570541527199473290555)
            ·
              refine ⟨11885355812290799209935833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923570541527199473290555 11885355812290799209935833)
              ·
                refine ⟨8914016859218099407451875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11885355812290799209935833 8914016859218099407451875)
                ·
                  refine ⟨13371025288827149111177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914016859218099407451875 13371025288827149111177813)
                  ·
                    refine ⟨156691702603443153646615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13371025288827149111177813 156691702603443153646615)
                    ·
                      rfl

theorem cell23_915468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_915468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915468 prefixEnd_915468 := by exact prefixLift 915468
  have htrace : WordTrace (prefixWord ++ tailWord_915468) baseStart_915468 baseEnd_915468 := by
    simpa [prefixWord, tailWord_915468, baseEnd_915468] using wordTrace_append hprefix tailTrace_915468
  have hstable : (prefixWord ++ tailWord_915468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915468).length < 2 ^ (prefixWord ++ tailWord_915468).sum := by decide
  have hdescent : baseEnd_915468 < baseStart_915468 := by decide
  rcases family_descends (prefixWord ++ tailWord_915468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915485 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_915485 : Nat := 118140960795 + 915485 * 2 ^ 59
def prefixEnd_915485 : Nat := 4983230072969 + 3 ^ 40 * 915485 * 2
def baseEnd_915485 : Nat := 156694612327151964809089

theorem tailTrace_915485 : CollatzResearch.WordTrace tailWord_915485 prefixEnd_915485 156694612327151964809089 := by
  unfold tailWord_915485
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390481088361672235259909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22260320725574448156839939 33390481088361672235259909)
  ·
    refine ⟨6260715204067813544111233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33390481088361672235259909 6260715204067813544111233)
    ·
      refine ⟨4695536403050860158083425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6260715204067813544111233 4695536403050860158083425)
      ·
        refine ⟨3521652302288145118562569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695536403050860158083425 3521652302288145118562569)
        ·
          refine ⟨2641239226716108838921927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3521652302288145118562569 2641239226716108838921927)
          ·
            refine ⟨3961858840074163258382891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641239226716108838921927 3961858840074163258382891)
            ·
              refine ⟨5942788260111244887574337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961858840074163258382891 5942788260111244887574337)
              ·
                refine ⟨4457091195083433665680753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5942788260111244887574337 4457091195083433665680753)
                ·
                  refine ⟨3342818396312575249260565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457091195083433665680753 3342818396312575249260565)
                  ·
                    refine ⟨156694612327151964809089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3342818396312575249260565 156694612327151964809089)
                    ·
                      rfl

theorem cell23_915485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_915485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915485 prefixEnd_915485 := by exact prefixLift 915485
  have htrace : WordTrace (prefixWord ++ tailWord_915485) baseStart_915485 baseEnd_915485 := by
    simpa [prefixWord, tailWord_915485, baseEnd_915485] using wordTrace_append hprefix tailTrace_915485
  have hstable : (prefixWord ++ tailWord_915485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915485).length < 2 ^ (prefixWord ++ tailWord_915485).sum := by decide
  have hdescent : baseEnd_915485 < baseStart_915485 := by decide
  rcases family_descends (prefixWord ++ tailWord_915485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915505 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_915505 : Nat := 118140960795 + 915505 * 2 ^ 59
def prefixEnd_915505 : Nat := 4983230072969 + 3 ^ 40 * 915505 * 2
def baseEnd_915505 : Nat := 470094106594545816177175

theorem tailTrace_915505 : CollatzResearch.WordTrace tailWord_915505 prefixEnd_915505 470094106594545816177175 := by
  unfold tailWord_915505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33391210548289215650987969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22260807032192810433991979 33391210548289215650987969)
  ·
    refine ⟨25043407911216911738240977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33391210548289215650987969 25043407911216911738240977)
    ·
      refine ⟨18782555933412683803680733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25043407911216911738240977 18782555933412683803680733)
      ·
        refine ⟨7043458475029756426380275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18782555933412683803680733 7043458475029756426380275)
        ·
          refine ⟨10565187712544634639570413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043458475029756426380275 10565187712544634639570413)
          ·
            refine ⟨3961945392204237989838905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10565187712544634639570413 3961945392204237989838905)
            ·
              refine ⟨2971459044153178492379179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961945392204237989838905 2971459044153178492379179)
              ·
                refine ⟨4457188566229767738568769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971459044153178492379179 4457188566229767738568769)
                ·
                  refine ⟨3342891424672325803926577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457188566229767738568769 3342891424672325803926577)
                  ·
                    refine ⟨2507168568504244352944933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3342891424672325803926577 2507168568504244352944933)
                    ·
                      refine ⟨470094106594545816177175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2507168568504244352944933 470094106594545816177175)
                      ·
                        rfl

theorem cell23_915505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_915505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915505 prefixEnd_915505 := by exact prefixLift 915505
  have htrace : WordTrace (prefixWord ++ tailWord_915505) baseStart_915505 baseEnd_915505 := by
    simpa [prefixWord, tailWord_915505, baseEnd_915505] using wordTrace_append hprefix tailTrace_915505
  have hstable : (prefixWord ++ tailWord_915505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915505).length < 2 ^ (prefixWord ++ tailWord_915505).sum := by decide
  have hdescent : baseEnd_915505 < baseStart_915505 := by decide
  rcases family_descends (prefixWord ++ tailWord_915505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915509 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_915509 : Nat := 118140960795 + 915509 * 2 ^ 59
def prefixEnd_915509 : Nat := 4983230072969 + 3 ^ 40 * 915509 * 2
def baseEnd_915509 : Nat := 470096160517163800527157

theorem tailTrace_915509 : CollatzResearch.WordTrace tailWord_915509 prefixEnd_915509 470096160517163800527157 := by
  unfold tailWord_915509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33391356440274724334133581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22260904293516482889422387 33391356440274724334133581)
  ·
    refine ⟨12521758665103021625300093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33391356440274724334133581 12521758665103021625300093)
    ·
      refine ⟨4695659499413633109487535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12521758665103021625300093 4695659499413633109487535)
      ·
        refine ⟨7043489249120449664231303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695659499413633109487535 7043489249120449664231303)
        ·
          refine ⟨10565233873680674496346955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043489249120449664231303 10565233873680674496346955)
          ·
            refine ⟨15847850810521011744520433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10565233873680674496346955 15847850810521011744520433)
            ·
              refine ⟨11885888107890758808390325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15847850810521011744520433 11885888107890758808390325)
              ·
                refine ⟨1114302010114758638286593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11885888107890758808390325 1114302010114758638286593)
                ·
                  refine ⟨835726507586068978714945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114302010114758638286593 835726507586068978714945)
                  ·
                    refine ⟨626794880689551734036209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835726507586068978714945 626794880689551734036209)
                    ·
                      refine ⟨470096160517163800527157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626794880689551734036209 470096160517163800527157)
                      ·
                        rfl

theorem cell23_915509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_915509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915509 prefixEnd_915509 := by exact prefixLift 915509
  have htrace : WordTrace (prefixWord ++ tailWord_915509) baseStart_915509 baseEnd_915509 := by
    simpa [prefixWord, tailWord_915509, baseEnd_915509] using wordTrace_append hprefix tailTrace_915509
  have hstable : (prefixWord ++ tailWord_915509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915509).length < 2 ^ (prefixWord ++ tailWord_915509).sum := by decide
  have hdescent : baseEnd_915509 < baseStart_915509 := by decide
  rcases family_descends (prefixWord ++ tailWord_915509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915526 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_915526 : Nat := 118140960795 + 915526 * 2 ^ 59
def prefixEnd_915526 : Nat := 4983230072969 + 3 ^ 40 * 915526 * 2
def baseEnd_915526 : Nat := 470104889688290234014579

theorem tailTrace_915526 : CollatzResearch.WordTrace tailWord_915526 prefixEnd_915526 470104889688290234014579 := by
  unfold tailWord_915526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043499265037910507421951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22261317654142090825001621 1043499265037910507421951)
  ·
    refine ⟨1565248897556865761132927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043499265037910507421951 1565248897556865761132927)
    ·
      refine ⟨2347873346335298641699391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565248897556865761132927 2347873346335298641699391)
      ·
        refine ⟨3521810019502947962549087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347873346335298641699391 3521810019502947962549087)
        ·
          refine ⟨5282715029254421943823631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521810019502947962549087 5282715029254421943823631)
          ·
            refine ⟨7924072543881632915735447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282715029254421943823631 7924072543881632915735447)
            ·
              refine ⟨11886108815822449373603171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924072543881632915735447 11886108815822449373603171)
              ·
                refine ⟨17829163223733674060404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886108815822449373603171 17829163223733674060404757)
                ·
                  refine ⟨835742026112515971581473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17829163223733674060404757 835742026112515971581473)
                  ·
                    refine ⟨626806519584386978686105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835742026112515971581473 626806519584386978686105)
                    ·
                      refine ⟨470104889688290234014579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626806519584386978686105 470104889688290234014579)
                      ·
                        rfl

theorem cell23_915526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_915526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915526 prefixEnd_915526 := by exact prefixLift 915526
  have htrace : WordTrace (prefixWord ++ tailWord_915526) baseStart_915526 baseEnd_915526 := by
    simpa [prefixWord, tailWord_915526, baseEnd_915526] using wordTrace_append hprefix tailTrace_915526
  have hstable : (prefixWord ++ tailWord_915526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915526).length < 2 ^ (prefixWord ++ tailWord_915526).sum := by decide
  have hdescent : baseEnd_915526 < baseStart_915526 := by decide
  rcases family_descends (prefixWord ++ tailWord_915526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915532 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 5]
def baseStart_915532 : Nat := 118140960795 + 915532 * 2 ^ 59
def prefixEnd_915532 : Nat := 4983230072969 + 3 ^ 40 * 915532 * 2
def baseEnd_915532 : Nat := 52234218952468578948839

theorem tailTrace_915532 : CollatzResearch.WordTrace tailWord_915532 prefixEnd_915532 52234218952468578948839 := by
  unfold tailWord_915532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16696097659595699631110425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22261463546127599508147233 16696097659595699631110425)
  ·
    refine ⟨12522073244696774723332819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16696097659595699631110425 12522073244696774723332819)
    ·
      refine ⟨18783109867045162084999229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12522073244696774723332819 18783109867045162084999229)
      ·
        refine ⟨7043666200141935781874711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18783109867045162084999229 7043666200141935781874711)
        ·
          refine ⟨10565499300212903672812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043666200141935781874711 10565499300212903672812067)
          ·
            refine ⟨15848248950319355509218101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10565499300212903672812067 15848248950319355509218101)
            ·
              refine ⟨1485773339092439578989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15848248950319355509218101 1485773339092439578989197)
              ·
                refine ⟨557165002159664842120949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485773339092439578989197 557165002159664842120949)
                ·
                  refine ⟨52234218952468578948839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557165002159664842120949 52234218952468578948839)
                  ·
                    rfl

theorem cell23_915532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_915532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915532 prefixEnd_915532 := by exact prefixLift 915532
  have htrace : WordTrace (prefixWord ++ tailWord_915532) baseStart_915532 baseEnd_915532 := by
    simpa [prefixWord, tailWord_915532, baseEnd_915532] using wordTrace_append hprefix tailTrace_915532
  have hstable : (prefixWord ++ tailWord_915532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915532).length < 2 ^ (prefixWord ++ tailWord_915532).sum := by decide
  have hdescent : baseEnd_915532 < baseStart_915532 := by decide
  rcases family_descends (prefixWord ++ tailWord_915532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915545 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_915545 : Nat := 118140960795 + 915545 * 2 ^ 59
def prefixEnd_915545 : Nat := 4983230072969 + 3 ^ 40 * 915545 * 2
def baseEnd_915545 : Nat := 156704881940241886558997

theorem tailTrace_915545 : CollatzResearch.WordTrace tailWord_915545 prefixEnd_915545 156704881940241886558997 := by
  unfold tailWord_915545
  simp only [CollatzResearch.WordTrace]
  refine ⟨33392669468144302482444089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22261779645429534988296059 33392669468144302482444089)
  ·
    refine ⟨25044502101108226861833067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33392669468144302482444089 25044502101108226861833067)
    ·
      refine ⟨37566753151662340292749601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25044502101108226861833067 37566753151662340292749601)
      ·
        refine ⟨28175064863746755219562201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37566753151662340292749601 28175064863746755219562201)
        ·
          refine ⟨21131298647810066414671651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28175064863746755219562201 21131298647810066414671651)
          ·
            refine ⟨31696947971715099622007477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21131298647810066414671651 31696947971715099622007477)
            ·
              refine ⟨2971588872348290589563201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31696947971715099622007477 2971588872348290589563201)
              ·
                refine ⟨2228691654261217942172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971588872348290589563201 2228691654261217942172401)
                ·
                  refine ⟨1671518740695913456629301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228691654261217942172401 1671518740695913456629301)
                  ·
                    refine ⟨156704881940241886558997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1671518740695913456629301 156704881940241886558997)
                    ·
                      rfl

theorem cell23_915545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_915545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915545 prefixEnd_915545 := by exact prefixLift 915545
  have htrace : WordTrace (prefixWord ++ tailWord_915545) baseStart_915545 baseEnd_915545 := by
    simpa [prefixWord, tailWord_915545, baseEnd_915545] using wordTrace_append hprefix tailTrace_915545
  have hstable : (prefixWord ++ tailWord_915545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915545).length < 2 ^ (prefixWord ++ tailWord_915545).sum := by decide
  have hdescent : baseEnd_915545 < baseStart_915545 := by decide
  rcases family_descends (prefixWord ++ tailWord_915545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915549 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 7]
def baseStart_915549 : Nat := 118140960795 + 915549 * 2 ^ 59
def prefixEnd_915549 : Nat := 4983230072969 + 3 ^ 40 * 915549 * 2
def baseEnd_915549 : Nat := 52235188860371516002997

theorem tailTrace_915549 : CollatzResearch.WordTrace tailWord_915549 prefixEnd_915549 52235188860371516002997 := by
  unfold tailWord_915549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33392815360129811165589701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22261876906753207443726467 33392815360129811165589701)
  ·
    refine ⟨6261152880024339593548069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33392815360129811165589701 6261152880024339593548069)
    ·
      refine ⟨1173966165004563673790263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6261152880024339593548069 1173966165004563673790263)
      ·
        refine ⟨1760949247506845510685395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173966165004563673790263 1760949247506845510685395)
        ·
          refine ⟨2641423871260268266028093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760949247506845510685395 2641423871260268266028093)
          ·
            refine ⟨990533951722600599760535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2641423871260268266028093 990533951722600599760535)
            ·
              refine ⟨1485800927583900899640803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990533951722600599760535 1485800927583900899640803)
              ·
                refine ⟨2228701391375851349461205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485800927583900899640803 2228701391375851349461205)
                ·
                  refine ⟨52235188860371516002997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2228701391375851349461205 52235188860371516002997)
                  ·
                    rfl

theorem cell23_915549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_915549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915549 prefixEnd_915549 := by exact prefixLift 915549
  have htrace : WordTrace (prefixWord ++ tailWord_915549) baseStart_915549 baseEnd_915549 := by
    simpa [prefixWord, tailWord_915549, baseEnd_915549] using wordTrace_append hprefix tailTrace_915549
  have hstable : (prefixWord ++ tailWord_915549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915549).length < 2 ^ (prefixWord ++ tailWord_915549).sum := by decide
  have hdescent : baseEnd_915549 < baseStart_915549 := by decide
  rcases family_descends (prefixWord ++ tailWord_915549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915626 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_915626 : Nat := 118140960795 + 915626 * 2 ^ 59
def prefixEnd_915626 : Nat := 4983230072969 + 3 ^ 40 * 915626 * 2
def baseEnd_915626 : Nat := 156718745917913280921373

theorem tailTrace_915626 : CollatzResearch.WordTrace tailWord_915626 prefixEnd_915626 156718745917913280921373 := by
  unfold tailWord_915626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348905945212713329035683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22263749187233902210761821 8348905945212713329035683)
  ·
    refine ⟨12523358917819069993553525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348905945212713329035683 12523358917819069993553525)
    ·
      refine ⟨1174064898545537811895643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12523358917819069993553525 1174064898545537811895643)
      ·
        refine ⟨1761097347818306717843465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174064898545537811895643 1761097347818306717843465)
        ·
          refine ⟨1320823010863730038382599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761097347818306717843465 1320823010863730038382599)
          ·
            refine ⟨1981234516295595057573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320823010863730038382599 1981234516295595057573899)
            ·
              refine ⟨2971851774443392586360849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981234516295595057573899 2971851774443392586360849)
              ·
                refine ⟨2228888830832544439770637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971851774443392586360849 2228888830832544439770637)
                ·
                  refine ⟨835833311562204164913989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228888830832544439770637 835833311562204164913989)
                  ·
                    refine ⟨156718745917913280921373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835833311562204164913989 156718745917913280921373)
                    ·
                      rfl

theorem cell23_915626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_915626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915626 prefixEnd_915626 := by exact prefixLift 915626
  have htrace : WordTrace (prefixWord ++ tailWord_915626) baseStart_915626 baseEnd_915626 := by
    simpa [prefixWord, tailWord_915626, baseEnd_915626] using wordTrace_append hprefix tailTrace_915626
  have hstable : (prefixWord ++ tailWord_915626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915626).length < 2 ^ (prefixWord ++ tailWord_915626).sum := by decide
  have hdescent : baseEnd_915626 < baseStart_915626 := by decide
  rcases family_descends (prefixWord ++ tailWord_915626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915645 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_915645 : Nat := 118140960795 + 915645 * 2 ^ 59
def prefixEnd_915645 : Nat := 4983230072969 + 3 ^ 40 * 915645 * 2
def baseEnd_915645 : Nat := 470165993886175268426531

theorem tailTrace_915645 : CollatzResearch.WordTrace tailWord_915645 prefixEnd_915645 470165993886175268426531 := by
  unfold tailWord_915645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33396316767782019561084389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22264211178521346374056259 33396316767782019561084389)
  ·
    refine ⟨6261809393959128667703323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33396316767782019561084389 6261809393959128667703323)
    ·
      refine ⟨9392714090938693001554985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6261809393959128667703323 9392714090938693001554985)
      ·
        refine ⟨7044535568204019751166239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9392714090938693001554985 7044535568204019751166239)
        ·
          refine ⟨10566803352306029626749359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044535568204019751166239 10566803352306029626749359)
          ·
            refine ⟨15850205028459044440124039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10566803352306029626749359 15850205028459044440124039)
            ·
              refine ⟨23775307542688566660186059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15850205028459044440124039 23775307542688566660186059)
              ·
                refine ⟨35662961314032849990279089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23775307542688566660186059 35662961314032849990279089)
                ·
                  refine ⟨26747220985524637492709317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35662961314032849990279089 26747220985524637492709317)
                  ·
                    refine ⟨5015103934785869529882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26747220985524637492709317 5015103934785869529882997)
                    ·
                      refine ⟨470165993886175268426531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5015103934785869529882997 470165993886175268426531)
                      ·
                        rfl

theorem cell23_915645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_915645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915645 prefixEnd_915645 := by exact prefixLift 915645
  have htrace : WordTrace (prefixWord ++ tailWord_915645) baseStart_915645 baseEnd_915645 := by
    simpa [prefixWord, tailWord_915645, baseEnd_915645] using wordTrace_append hprefix tailTrace_915645
  have hstable : (prefixWord ++ tailWord_915645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915645).length < 2 ^ (prefixWord ++ tailWord_915645).sum := by decide
  have hdescent : baseEnd_915645 < baseStart_915645 := by decide
  rcases family_descends (prefixWord ++ tailWord_915645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915665 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_915665 : Nat := 118140960795 + 915665 * 2 ^ 59
def prefixEnd_915665 : Nat := 4983230072969 + 3 ^ 40 * 915665 * 2
def baseEnd_915665 : Nat := 156725421166421730058813

theorem tailTrace_915665 : CollatzResearch.WordTrace tailWord_915665 prefixEnd_915665 156725421166421730058813 := by
  unfold tailWord_915665
  simp only [CollatzResearch.WordTrace]
  refine ⟨33397046227709562976812449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22264697485139708651208299 33397046227709562976812449)
  ·
    refine ⟨25047784670782172232609337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33397046227709562976812449 25047784670782172232609337)
    ·
      refine ⟨18785838503086629174457003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25047784670782172232609337 18785838503086629174457003)
      ·
        refine ⟨28178757754629943761685505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18785838503086629174457003 28178757754629943761685505)
        ·
          refine ⟨21134068315972457821264129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28178757754629943761685505 21134068315972457821264129)
          ·
            refine ⟨15850551236979343365948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21134068315972457821264129 15850551236979343365948097)
            ·
              refine ⟨11887913427734507524461073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15850551236979343365948097 11887913427734507524461073)
              ·
                refine ⟨8915935070800880643345805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887913427734507524461073 8915935070800880643345805)
                ·
                  refine ⟨3343475651550330241254677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8915935070800880643345805 3343475651550330241254677)
                  ·
                    refine ⟨156725421166421730058813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3343475651550330241254677 156725421166421730058813)
                    ·
                      rfl

theorem cell23_915665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_915665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915665 prefixEnd_915665 := by exact prefixLift 915665
  have htrace : WordTrace (prefixWord ++ tailWord_915665) baseStart_915665 baseEnd_915665 := by
    simpa [prefixWord, tailWord_915665, baseEnd_915665] using wordTrace_append hprefix tailTrace_915665
  have hstable : (prefixWord ++ tailWord_915665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915665).length < 2 ^ (prefixWord ++ tailWord_915665).sum := by decide
  have hdescent : baseEnd_915665 < baseStart_915665 := by decide
  rcases family_descends (prefixWord ++ tailWord_915665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915666 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_915666 : Nat := 118140960795 + 915666 * 2 ^ 59
def prefixEnd_915666 : Nat := 4983230072969 + 3 ^ 40 * 915666 * 2
def baseEnd_915666 : Nat := 470176776979919686263935

theorem tailTrace_915666 : CollatzResearch.WordTrace tailWord_915666 prefixEnd_915666 470176776979919686263935 := by
  unfold tailWord_915666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8349270675176485036899713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22264721800470626765065901 8349270675176485036899713)
  ·
    refine ⟨6261953006382363777674785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8349270675176485036899713 6261953006382363777674785)
    ·
      refine ⟨4696464754786772833256089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6261953006382363777674785 4696464754786772833256089)
      ·
        refine ⟨3522348566090079624942067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4696464754786772833256089 3522348566090079624942067)
        ·
          refine ⟨5283522849135119437413101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522348566090079624942067 5283522849135119437413101)
          ·
            refine ⟨1981321068425669789029913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5283522849135119437413101 1981321068425669789029913)
            ·
              refine ⟨1485990801319252341772435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981321068425669789029913 1485990801319252341772435)
              ·
                refine ⟨2228986201978878512658653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485990801319252341772435 2228986201978878512658653)
                ·
                  refine ⟨835869825742079442246995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228986201978878512658653 835869825742079442246995)
                  ·
                    refine ⟨1253804738613119163370493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835869825742079442246995 1253804738613119163370493)
                    ·
                      refine ⟨470176776979919686263935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1253804738613119163370493 470176776979919686263935)
                      ·
                        rfl

theorem cell23_915666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_915666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915666 prefixEnd_915666 := by exact prefixLift 915666
  have htrace : WordTrace (prefixWord ++ tailWord_915666) baseStart_915666 baseEnd_915666 := by
    simpa [prefixWord, tailWord_915666, baseEnd_915666] using wordTrace_append hprefix tailTrace_915666
  have hstable : (prefixWord ++ tailWord_915666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915666).length < 2 ^ (prefixWord ++ tailWord_915666).sum := by decide
  have hdescent : baseEnd_915666 < baseStart_915666 := by decide
  rcases family_descends (prefixWord ++ tailWord_915666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_915675 : Nat := 118140960795 + 915675 * 2 ^ 59
def prefixEnd_915675 : Nat := 4983230072969 + 3 ^ 40 * 915675 * 2
def baseEnd_915675 : Nat := 470181398305810151051393

theorem tailTrace_915675 : CollatzResearch.WordTrace tailWord_915675 prefixEnd_915675 470181398305810151051393 := by
  unfold tailWord_915675
  simp only [CollatzResearch.WordTrace]
  refine ⟨33397410957673334684676479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22264940638448889789784319 33397410957673334684676479)
  ·
    refine ⟨50096116436510002027014719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33397410957673334684676479 50096116436510002027014719)
    ·
      refine ⟨75144174654765003040522079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50096116436510002027014719 75144174654765003040522079)
      ·
        refine ⟨112716261982147504560783119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75144174654765003040522079 112716261982147504560783119)
        ·
          refine ⟨169074392973221256841174679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112716261982147504560783119 169074392973221256841174679)
          ·
            refine ⟨253611589459831885261762019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169074392973221256841174679 253611589459831885261762019)
            ·
              refine ⟨380417384189747827892643029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253611589459831885261762019 380417384189747827892643029)
              ·
                refine ⟨8916032441947214716233821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 380417384189747827892643029 8916032441947214716233821)
                ·
                  refine ⟨3343512165730205518587683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8916032441947214716233821 3343512165730205518587683)
                  ·
                    refine ⟨5015268248595308277881525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343512165730205518587683 5015268248595308277881525)
                    ·
                      refine ⟨470181398305810151051393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5015268248595308277881525 470181398305810151051393)
                      ·
                        rfl

theorem cell23_915675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_915675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915675 prefixEnd_915675 := by exact prefixLift 915675
  have htrace : WordTrace (prefixWord ++ tailWord_915675) baseStart_915675 baseEnd_915675 := by
    simpa [prefixWord, tailWord_915675, baseEnd_915675] using wordTrace_append hprefix tailTrace_915675
  have hstable : (prefixWord ++ tailWord_915675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915675).length < 2 ^ (prefixWord ++ tailWord_915675).sum := by decide
  have hdescent : baseEnd_915675 < baseStart_915675 := by decide
  rcases family_descends (prefixWord ++ tailWord_915675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915772 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_915772 : Nat := 118140960795 + 915772 * 2 ^ 59
def prefixEnd_915772 : Nat := 4983230072969 + 3 ^ 40 * 915772 * 2
def baseEnd_915772 : Nat := 156743735309765423846149

theorem tailTrace_915772 : CollatzResearch.WordTrace tailWord_915772 prefixEnd_915772 156743735309765423846149 := by
  unfold tailWord_915772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16700474419160960125478785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22267299225547946833971713 16700474419160960125478785)
  ·
    refine ⟨12525355814370720094109089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16700474419160960125478785 12525355814370720094109089)
    ·
      refine ⟨9394016860778040070581817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12525355814370720094109089 9394016860778040070581817)
      ·
        refine ⟨7045512645583530052936363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394016860778040070581817 7045512645583530052936363)
        ·
          refine ⟨10568268968375295079404545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045512645583530052936363 10568268968375295079404545)
          ·
            refine ⟨7926201726281471309553409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10568268968375295079404545 7926201726281471309553409)
            ·
              refine ⟨5944651294711103482165057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926201726281471309553409 5944651294711103482165057)
              ·
                refine ⟨4458488471033327611623793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944651294711103482165057 4458488471033327611623793)
                ·
                  refine ⟨3343866353274995708717845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4458488471033327611623793 3343866353274995708717845)
                  ·
                    refine ⟨156743735309765423846149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3343866353274995708717845 156743735309765423846149)
                    ·
                      rfl

theorem cell23_915772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_915772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915772 prefixEnd_915772 := by exact prefixLift 915772
  have htrace : WordTrace (prefixWord ++ tailWord_915772) baseStart_915772 baseEnd_915772 := by
    simpa [prefixWord, tailWord_915772, baseEnd_915772] using wordTrace_append hprefix tailTrace_915772
  have hstable : (prefixWord ++ tailWord_915772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915772).length < 2 ^ (prefixWord ++ tailWord_915772).sum := by decide
  have hdescent : baseEnd_915772 < baseStart_915772 := by decide
  rcases family_descends (prefixWord ++ tailWord_915772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915792 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_915792 : Nat := 118140960795 + 915792 * 2 ^ 59
def prefixEnd_915792 : Nat := 4983230072969 + 3 ^ 40 * 915792 * 2
def baseEnd_915792 : Nat := 470241475542386193288355

theorem tailTrace_915792 : CollatzResearch.WordTrace tailWord_915792 prefixEnd_915792 470241475542386193288355 := by
  unfold tailWord_915792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16700839149124731833342815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22267785532166309111123753 16700839149124731833342815)
  ·
    refine ⟨25051258723687097750014223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16700839149124731833342815 25051258723687097750014223)
    ·
      refine ⟨37576888085530646625021335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25051258723687097750014223 37576888085530646625021335)
      ·
        refine ⟨56365332128295969937532003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37576888085530646625021335 56365332128295969937532003)
        ·
          refine ⟨84547998192443954906298005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56365332128295969937532003 84547998192443954906298005)
          ·
            refine ⟨3963187415270810386232719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84547998192443954906298005 3963187415270810386232719)
            ·
              refine ⟨5944781122906215579349079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963187415270810386232719 5944781122906215579349079)
              ·
                refine ⟨8917171684359323369023619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944781122906215579349079 8917171684359323369023619)
                ·
                  refine ⟨13375757526538985053535429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8917171684359323369023619 13375757526538985053535429)
                  ·
                    refine ⟨2507954536226059697537893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13375757526538985053535429 2507954536226059697537893)
                    ·
                      refine ⟨470241475542386193288355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2507954536226059697537893 470241475542386193288355)
                      ·
                        rfl

theorem cell23_915792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_915792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915792 prefixEnd_915792 := by exact prefixLift 915792
  have htrace : WordTrace (prefixWord ++ tailWord_915792) baseStart_915792 baseEnd_915792 := by
    simpa [prefixWord, tailWord_915792, baseEnd_915792] using wordTrace_append hprefix tailTrace_915792
  have hstable : (prefixWord ++ tailWord_915792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915792).length < 2 ^ (prefixWord ++ tailWord_915792).sum := by decide
  have hdescent : baseEnd_915792 < baseStart_915792 := by decide
  rcases family_descends (prefixWord ++ tailWord_915792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915796 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_915796 : Nat := 118140960795 + 915796 * 2 ^ 59
def prefixEnd_915796 : Nat := 4983230072969 + 3 ^ 40 * 915796 * 2
def baseEnd_915796 : Nat := 470243529465004177638337

theorem tailTrace_915796 : CollatzResearch.WordTrace tailWord_915796 prefixEnd_915796 470243529465004177638337 := by
  unfold tailWord_915796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16700912095117486174915621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22267882793489981566554161 16700912095117486174915621)
  ·
    refine ⟨3131421017834528657796679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16700912095117486174915621 3131421017834528657796679)
    ·
      refine ⟨4697131526751792986695019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131421017834528657796679 4697131526751792986695019)
      ·
        refine ⟨7045697290127689480042529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697131526751792986695019 7045697290127689480042529)
        ·
          refine ⟨5284272967595767110031897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7045697290127689480042529 5284272967595767110031897)
          ·
            refine ⟨3963204725696825332523923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5284272967595767110031897 3963204725696825332523923)
            ·
              refine ⟨5944807088545237998785885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963204725696825332523923 5944807088545237998785885)
              ·
                refine ⟨2229302658204464249544707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5944807088545237998785885 2229302658204464249544707)
                ·
                  refine ⟨3343953987306696374317061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229302658204464249544707 3343953987306696374317061)
                  ·
                    refine ⟨626991372620005570184449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343953987306696374317061 626991372620005570184449)
                    ·
                      refine ⟨470243529465004177638337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 626991372620005570184449 470243529465004177638337)
                      ·
                        rfl

theorem cell23_915796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_915796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915796 prefixEnd_915796 := by exact prefixLift 915796
  have htrace : WordTrace (prefixWord ++ tailWord_915796) baseStart_915796 baseEnd_915796 := by
    simpa [prefixWord, tailWord_915796, baseEnd_915796] using wordTrace_append hprefix tailTrace_915796
  have hstable : (prefixWord ++ tailWord_915796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915796).length < 2 ^ (prefixWord ++ tailWord_915796).sum := by decide
  have hdescent : baseEnd_915796 < baseStart_915796 := by decide
  rcases family_descends (prefixWord ++ tailWord_915796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915870 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_915870 : Nat := 118140960795 + 915870 * 2 ^ 59
def prefixEnd_915870 : Nat := 4983230072969 + 3 ^ 40 * 915870 * 2
def baseEnd_915870 : Nat := 52253503003715209790333

theorem tailTrace_915870 : CollatzResearch.WordTrace tailWord_915870 prefixEnd_915870 52253503003715209790333 := by
  unfold tailWord_915870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175565398995860373503133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22269682127977921992016709 4175565398995860373503133)
  ·
    refine ⟨1565837024623447640063675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4175565398995860373503133 1565837024623447640063675)
    ·
      refine ⟨2348755536935171460095513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565837024623447640063675 2348755536935171460095513)
      ·
        refine ⟨1761566652701378595071635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348755536935171460095513 1761566652701378595071635)
        ·
          refine ⟨2642349979052067892607453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761566652701378595071635 2642349979052067892607453)
          ·
            refine ⟨990881242144525459727795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2642349979052067892607453 990881242144525459727795)
            ·
              refine ⟨1486321863216788189591693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990881242144525459727795 1486321863216788189591693)
              ·
                refine ⟨557370698706295571096885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486321863216788189591693 557370698706295571096885)
                ·
                  refine ⟨52253503003715209790333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557370698706295571096885 52253503003715209790333)
                  ·
                    rfl

theorem cell23_915870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_915870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915870 prefixEnd_915870 := by exact prefixLift 915870
  have htrace : WordTrace (prefixWord ++ tailWord_915870) baseStart_915870 baseEnd_915870 := by
    simpa [prefixWord, tailWord_915870, baseEnd_915870] using wordTrace_append hprefix tailTrace_915870
  have hstable : (prefixWord ++ tailWord_915870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915870).length < 2 ^ (prefixWord ++ tailWord_915870).sum := by decide
  have hdescent : baseEnd_915870 < baseStart_915870 := by decide
  rcases family_descends (prefixWord ++ tailWord_915870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915974 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_915974 : Nat := 118140960795 + 915974 * 2 ^ 59
def prefixEnd_915974 : Nat := 4983230072969 + 3 ^ 40 * 915974 * 2
def baseEnd_915974 : Nat := 470334929021504481212519

theorem tailTrace_915974 : CollatzResearch.WordTrace tailWord_915974 prefixEnd_915974 470334929021504481212519 := by
  unfold tailWord_915974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044009886987190898431593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22272210922393405833207317 1044009886987190898431593)
  ·
    refine ⟨783007415240393173823695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044009886987190898431593 783007415240393173823695)
    ·
      refine ⟨1174511122860589760735543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783007415240393173823695 1174511122860589760735543)
      ·
        refine ⟨1761766684290884641103315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174511122860589760735543 1761766684290884641103315)
        ·
          refine ⟨2642650026436326961654973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761766684290884641103315 2642650026436326961654973)
          ·
            refine ⟨990993759913622610620615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2642650026436326961654973 990993759913622610620615)
            ·
              refine ⟨1486490639870433915930923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990993759913622610620615 1486490639870433915930923)
              ·
                refine ⟨2229735959805650873896385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486490639870433915930923 2229735959805650873896385)
                ·
                  refine ⟨1672301969854238155422289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229735959805650873896385 1672301969854238155422289)
                  ·
                    refine ⟨1254226477390678616566717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1672301969854238155422289 1254226477390678616566717)
                    ·
                      refine ⟨470334929021504481212519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254226477390678616566717 470334929021504481212519)
                      ·
                        rfl

theorem cell23_915974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_915974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915974 prefixEnd_915974 := by exact prefixLift 915974
  have htrace : WordTrace (prefixWord ++ tailWord_915974) baseStart_915974 baseEnd_915974 := by
    simpa [prefixWord, tailWord_915974, baseEnd_915974] using wordTrace_append hprefix tailTrace_915974
  have hstable : (prefixWord ++ tailWord_915974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915974).length < 2 ^ (prefixWord ++ tailWord_915974).sum := by decide
  have hdescent : baseEnd_915974 < baseStart_915974 := by decide
  rcases family_descends (prefixWord ++ tailWord_915974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915976 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_915976 : Nat := 118140960795 + 915976 * 2 ^ 59
def prefixEnd_915976 : Nat := 4983230072969 + 3 ^ 40 * 915976 * 2
def baseEnd_915976 : Nat := 470335955982813473387509

theorem tailTrace_915976 : CollatzResearch.WordTrace tailWord_915976 prefixEnd_915976 470335955982813473387509 := by
  unfold tailWord_915976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704194664791431545691891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22272259553055242060922521 16704194664791431545691891)
  ·
    refine ⟨25056291997187147318537837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16704194664791431545691891 25056291997187147318537837)
    ·
      refine ⟨9396109498945180244451689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25056291997187147318537837 9396109498945180244451689)
      ·
        refine ⟨7047082124208885183338767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9396109498945180244451689 7047082124208885183338767)
        ·
          refine ⟨10570623186313327775008151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047082124208885183338767 10570623186313327775008151)
          ·
            refine ⟨15855934779469991662512227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570623186313327775008151 15855934779469991662512227)
            ·
              refine ⟨23783902169204987493768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855934779469991662512227 23783902169204987493768341)
              ·
                refine ⟨1114870414181483788770391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23783902169204987493768341 1114870414181483788770391)
                ·
                  refine ⟨1672305621272225683155587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114870414181483788770391 1672305621272225683155587)
                  ·
                    refine ⟨2508458431908338524733381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672305621272225683155587 2508458431908338524733381)
                    ·
                      refine ⟨470335955982813473387509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2508458431908338524733381 470335955982813473387509)
                      ·
                        rfl

theorem cell23_915976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_915976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915976 prefixEnd_915976 := by exact prefixLift 915976
  have htrace : WordTrace (prefixWord ++ tailWord_915976) baseStart_915976 baseEnd_915976 := by
    simpa [prefixWord, tailWord_915976, baseEnd_915976] using wordTrace_append hprefix tailTrace_915976
  have hstable : (prefixWord ++ tailWord_915976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915976).length < 2 ^ (prefixWord ++ tailWord_915976).sum := by decide
  have hdescent : baseEnd_915976 < baseStart_915976 := by decide
  rcases family_descends (prefixWord ++ tailWord_915976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915980 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_915980 : Nat := 118140960795 + 915980 * 2 ^ 59
def prefixEnd_915980 : Nat := 4983230072969 + 3 ^ 40 * 915980 * 2
def baseEnd_915980 : Nat := 470338009905431457737491

theorem tailTrace_915980 : CollatzResearch.WordTrace tailWord_915980 prefixEnd_915980 470338009905431457737491 := by
  unfold tailWord_915980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704267610784185887264697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22272356814378914516352929 16704267610784185887264697)
  ·
    refine ⟨12528200708088139415448523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16704267610784185887264697 12528200708088139415448523)
    ·
      refine ⟨18792301062132209123172785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528200708088139415448523 18792301062132209123172785)
      ·
        refine ⟨14094225796599156842379589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18792301062132209123172785 14094225796599156842379589)
        ·
          refine ⟨2642667336862341907946173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14094225796599156842379589 2642667336862341907946173)
          ·
            refine ⟨991000251323378215479815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2642667336862341907946173 991000251323378215479815)
            ·
              refine ⟨1486500376985067323219723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991000251323378215479815 1486500376985067323219723)
              ·
                refine ⟨2229750565477600984829585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486500376985067323219723 2229750565477600984829585)
                ·
                  refine ⟨1672312924108200738622189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229750565477600984829585 1672312924108200738622189)
                  ·
                    refine ⟨627117346540575276983321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672312924108200738622189 627117346540575276983321)
                    ·
                      refine ⟨470338009905431457737491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627117346540575276983321 470338009905431457737491)
                      ·
                        rfl

theorem cell23_915980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_915980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_915980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_915980 prefixEnd_915980 := by exact prefixLift 915980
  have htrace : WordTrace (prefixWord ++ tailWord_915980) baseStart_915980 baseEnd_915980 := by
    simpa [prefixWord, tailWord_915980, baseEnd_915980] using wordTrace_append hprefix tailTrace_915980
  have hstable : (prefixWord ++ tailWord_915980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915980).length < 2 ^ (prefixWord ++ tailWord_915980).sum := by decide
  have hdescent : baseEnd_915980 < baseStart_915980 := by decide
  rcases family_descends (prefixWord ++ tailWord_915980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916003 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 2, 4]
def baseStart_916003 : Nat := 118140960795 + 916003 * 2 ^ 59
def prefixEnd_916003 : Nat := 4983230072969 + 3 ^ 40 * 916003 * 2
def baseEnd_916003 : Nat := 156783273320161622583295

theorem tailTrace_916003 : CollatzResearch.WordTrace tailWord_916003 prefixEnd_916003 156783273320161622583295 := by
  unfold tailWord_916003
  simp only [CollatzResearch.WordTrace]
  refine ⟨33409374100485046702616663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22272916066990031135077775 33409374100485046702616663)
  ·
    refine ⟨50114061150727570053924995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33409374100485046702616663 50114061150727570053924995)
    ·
      refine ⟨75171091726091355080887493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50114061150727570053924995 75171091726091355080887493)
      ·
        refine ⟨14094579698642129077666405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75171091726091355080887493 14094579698642129077666405)
        ·
          refine ⟨2642733693495399202062451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14094579698642129077666405 2642733693495399202062451)
          ·
            refine ⟨3964100540243098803093677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642733693495399202062451 3964100540243098803093677)
            ·
              refine ⟨1486537702591162051160129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3964100540243098803093677 1486537702591162051160129)
              ·
                refine ⟨1114903276943371538370097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486537702591162051160129 1114903276943371538370097)
                ·
                  refine ⟨836177457707528653777573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114903276943371538370097 836177457707528653777573)
                  ·
                    refine ⟨156783273320161622583295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836177457707528653777573 156783273320161622583295)
                    ·
                      rfl

theorem cell23_916003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 4].length) (baseStart_916003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916003 prefixEnd_916003 := by exact prefixLift 916003
  have htrace : WordTrace (prefixWord ++ tailWord_916003) baseStart_916003 baseEnd_916003 := by
    simpa [prefixWord, tailWord_916003, baseEnd_916003] using wordTrace_append hprefix tailTrace_916003
  have hstable : (prefixWord ++ tailWord_916003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916003).length < 2 ^ (prefixWord ++ tailWord_916003).sum := by decide
  have hdescent : baseEnd_916003 < baseStart_916003 := by decide
  rcases family_descends (prefixWord ++ tailWord_916003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916010 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_916010 : Nat := 118140960795 + 916010 * 2 ^ 59
def prefixEnd_916010 : Nat := 4983230072969 + 3 ^ 40 * 916010 * 2
def baseEnd_916010 : Nat := 470353414325066340362353

theorem tailTrace_916010 : CollatzResearch.WordTrace tailWord_916010 prefixEnd_916010 470353414325066340362353 := by
  unfold tailWord_916010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352407352864921724530371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22273086274306457932080989 8352407352864921724530371)
  ·
    refine ⟨12528611029297382586795557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352407352864921724530371 12528611029297382586795557)
    ·
      refine ⟨2349114567993259235024167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12528611029297382586795557 2349114567993259235024167)
      ·
        refine ⟨3523671851989888852536251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349114567993259235024167 3523671851989888852536251)
        ·
          refine ⟨5285507777984833278804377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523671851989888852536251 5285507777984833278804377)
          ·
            refine ⟨3964130833488624959103283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5285507777984833278804377 3964130833488624959103283)
            ·
              refine ⟨5946196250232937438654925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964130833488624959103283 5946196250232937438654925)
              ·
                refine ⟨2229823593837351539495597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5946196250232937438654925 2229823593837351539495597)
                ·
                  refine ⟨836183847689006827310849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2229823593837351539495597 836183847689006827310849)
                  ·
                    refine ⟨627137885766755120483137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836183847689006827310849 627137885766755120483137)
                    ·
                      refine ⟨470353414325066340362353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627137885766755120483137 470353414325066340362353)
                      ·
                        rfl

theorem cell23_916010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_916010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916010 prefixEnd_916010 := by exact prefixLift 916010
  have htrace : WordTrace (prefixWord ++ tailWord_916010) baseStart_916010 baseEnd_916010 := by
    simpa [prefixWord, tailWord_916010, baseEnd_916010] using wordTrace_append hprefix tailTrace_916010
  have hstable : (prefixWord ++ tailWord_916010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916010).length < 2 ^ (prefixWord ++ tailWord_916010).sum := by decide
  have hdescent : baseEnd_916010 < baseStart_916010 := by decide
  rcases family_descends (prefixWord ++ tailWord_916010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916033 : List Nat := [1, 2, 5, 1, 1, 4, 2, 7]
def baseStart_916033 : Nat := 118140960795 + 916033 * 2 ^ 59
def prefixEnd_916033 : Nat := 4983230072969 + 3 ^ 40 * 916033 * 2
def baseEnd_916033 : Nat := 17420934236300731495361

theorem tailTrace_916033 : CollatzResearch.WordTrace tailWord_916033 prefixEnd_916033 17420934236300731495361 := by
  unfold tailWord_916033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410468290376361826208753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22273645526917574550805835 33410468290376361826208753)
  ·
    refine ⟨25057851217782271369656565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33410468290376361826208753 25057851217782271369656565)
    ·
      refine ⟨2349173551667087940905303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25057851217782271369656565 2349173551667087940905303)
      ·
        refine ⟨3523760327500631911357955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349173551667087940905303 3523760327500631911357955)
        ·
          refine ⟨5285640491250947867036933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523760327500631911357955 5285640491250947867036933)
          ·
            refine ⟨991057592109552725069425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5285640491250947867036933 991057592109552725069425)
            ·
              refine ⟨743293194082164543802069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991057592109552725069425 743293194082164543802069)
              ·
                refine ⟨17420934236300731495361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 743293194082164543802069 17420934236300731495361)
                ·
                  rfl

theorem cell23_916033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 7].length) (baseStart_916033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916033 prefixEnd_916033 := by exact prefixLift 916033
  have htrace : WordTrace (prefixWord ++ tailWord_916033) baseStart_916033 baseEnd_916033 := by
    simpa [prefixWord, tailWord_916033, baseEnd_916033] using wordTrace_append hprefix tailTrace_916033
  have hstable : (prefixWord ++ tailWord_916033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916033).length < 2 ^ (prefixWord ++ tailWord_916033).sum := by decide
  have hdescent : baseEnd_916033 < baseStart_916033 := by decide
  rcases family_descends (prefixWord ++ tailWord_916033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916077 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_916077 : Nat := 118140960795 + 916077 * 2 ^ 59
def prefixEnd_916077 : Nat := 4983230072969 + 3 ^ 40 * 916077 * 2
def baseEnd_916077 : Nat := 470387817528917578224545

theorem tailTrace_916077 : CollatzResearch.WordTrace tailWord_916077 prefixEnd_916077 470387817528917578224545 := by
  unfold tailWord_916077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412073102216957340810485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22274715401477971560540323 33412073102216957340810485)
  ·
    refine ⟨3132381853332839750700983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33412073102216957340810485 3132381853332839750700983)
    ·
      refine ⟨4698572779999259626051475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3132381853332839750700983 4698572779999259626051475)
      ·
        refine ⟨7047859169998889439077213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698572779999259626051475 7047859169998889439077213)
        ·
          refine ⟨2642947188749583539653955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7047859169998889439077213 2642947188749583539653955)
          ·
            refine ⟨3964420783124375309480933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642947188749583539653955 3964420783124375309480933)
            ·
              refine ⟨743328896835820370527675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3964420783124375309480933 743328896835820370527675)
              ·
                refine ⟨1114993345253730555791513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743328896835820370527675 1114993345253730555791513)
                ·
                  refine ⟨836245008940297916843635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114993345253730555791513 836245008940297916843635)
                  ·
                    refine ⟨1254367513410446875265453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836245008940297916843635 1254367513410446875265453)
                    ·
                      refine ⟨470387817528917578224545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254367513410446875265453 470387817528917578224545)
                      ·
                        rfl

theorem cell23_916077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_916077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916077 prefixEnd_916077 := by exact prefixLift 916077
  have htrace : WordTrace (prefixWord ++ tailWord_916077) baseStart_916077 baseEnd_916077 := by
    simpa [prefixWord, tailWord_916077, baseEnd_916077] using wordTrace_append hprefix tailTrace_916077
  have hstable : (prefixWord ++ tailWord_916077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916077).length < 2 ^ (prefixWord ++ tailWord_916077).sum := by decide
  have hdescent : baseEnd_916077 < baseStart_916077 := by decide
  rcases family_descends (prefixWord ++ tailWord_916077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916083 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 6, 2, 2]
def baseStart_916083 : Nat := 118140960795 + 916083 * 2 ^ 59
def prefixEnd_916083 : Nat := 4983230072969 + 3 ^ 40 * 916083 * 2
def baseEnd_916083 : Nat := 470390898412844554749517

theorem tailTrace_916083 : CollatzResearch.WordTrace tailWord_916083 prefixEnd_916083 470390898412844554749517 := by
  unfold tailWord_916083
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412291940195220365528903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22274861293463480243685935 33412291940195220365528903)
  ·
    refine ⟨50118437910292830548293355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33412291940195220365528903 50118437910292830548293355)
    ·
      refine ⟨75177656865439245822440033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50118437910292830548293355 75177656865439245822440033)
      ·
        refine ⟨56383242649079434366830025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75177656865439245822440033 56383242649079434366830025)
        ·
          refine ⟨42287431986809575775122519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56383242649079434366830025 42287431986809575775122519)
          ·
            refine ⟨63431147980214363662683779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42287431986809575775122519 63431147980214363662683779)
            ·
              refine ⟨95146721970321545494025669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63431147980214363662683779 95146721970321545494025669)
              ·
                refine ⟨17840010369435289780129813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95146721970321545494025669 17840010369435289780129813)
                ·
                  refine ⟨836250486067279208443585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17840010369435289780129813 836250486067279208443585)
                  ·
                    refine ⟨627187864550459406332689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836250486067279208443585 627187864550459406332689)
                    ·
                      refine ⟨470390898412844554749517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627187864550459406332689 470390898412844554749517)
                      ·
                        rfl

theorem cell23_916083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2, 2].length) (baseStart_916083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916083 prefixEnd_916083 := by exact prefixLift 916083
  have htrace : WordTrace (prefixWord ++ tailWord_916083) baseStart_916083 baseEnd_916083 := by
    simpa [prefixWord, tailWord_916083, baseEnd_916083] using wordTrace_append hprefix tailTrace_916083
  have hstable : (prefixWord ++ tailWord_916083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916083).length < 2 ^ (prefixWord ++ tailWord_916083).sum := by decide
  have hdescent : baseEnd_916083 < baseStart_916083 := by decide
  rcases family_descends (prefixWord ++ tailWord_916083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916100 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_916100 : Nat := 118140960795 + 916100 * 2 ^ 59
def prefixEnd_916100 : Nat := 4983230072969 + 3 ^ 40 * 916100 * 2
def baseEnd_916100 : Nat := 470399627583970988236939

theorem tailTrace_916100 : CollatzResearch.WordTrace tailWord_916100 prefixEnd_916100 470399627583970988236939 := by
  unfold tailWord_916100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706455990566816134448877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22275274654089088179265169 16706455990566816134448877)
  ·
    refine ⟨6264920996462556050418329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16706455990566816134448877 6264920996462556050418329)
    ·
      refine ⟨4698690747346917037813747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6264920996462556050418329 4698690747346917037813747)
      ·
        refine ⟨7048036121020375556720621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698690747346917037813747 7048036121020375556720621)
        ·
          refine ⟨2643013545382640833770233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7048036121020375556720621 2643013545382640833770233)
          ·
            refine ⟨1982260159036980625327675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643013545382640833770233 1982260159036980625327675)
            ·
              refine ⟨2973390238555470937991513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982260159036980625327675 2973390238555470937991513)
              ·
                refine ⟨2230042678916603203493635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973390238555470937991513 2230042678916603203493635)
                ·
                  refine ⟨3345064018374904805240453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230042678916603203493635 3345064018374904805240453)
                  ·
                    refine ⟨627199503445294650982585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345064018374904805240453 627199503445294650982585)
                    ·
                      refine ⟨470399627583970988236939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627199503445294650982585 470399627583970988236939)
                      ·
                        rfl

theorem cell23_916100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_916100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916100 prefixEnd_916100 := by exact prefixLift 916100
  have htrace : WordTrace (prefixWord ++ tailWord_916100) baseStart_916100 baseEnd_916100 := by
    simpa [prefixWord, tailWord_916100, baseEnd_916100] using wordTrace_append hprefix tailTrace_916100
  have hstable : (prefixWord ++ tailWord_916100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916100).length < 2 ^ (prefixWord ++ tailWord_916100).sum := by decide
  have hdescent : baseEnd_916100 < baseStart_916100 := by decide
  rcases family_descends (prefixWord ++ tailWord_916100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916183 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 3, 4]
def baseStart_916183 : Nat := 118140960795 + 916183 * 2 ^ 59
def prefixEnd_916183 : Nat := 4983230072969 + 3 ^ 40 * 916183 * 2
def baseEnd_916183 : Nat := 156814082159431387833019

theorem tailTrace_916183 : CollatzResearch.WordTrace tailWord_916183 prefixEnd_916183 156814082159431387833019 := by
  unfold tailWord_916183
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415939239832937444169203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22277292826555291629446135 33415939239832937444169203)
  ·
    refine ⟨50123908859749406166253805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33415939239832937444169203 50123908859749406166253805)
    ·
      refine ⟨18796465822406027312345177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50123908859749406166253805 18796465822406027312345177)
      ·
        refine ⟨14097349366804520484258883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18796465822406027312345177 14097349366804520484258883)
        ·
          refine ⟨21146024050206780726388325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14097349366804520484258883 21146024050206780726388325)
          ·
            refine ⟨3964879509413771386197811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21146024050206780726388325 3964879509413771386197811)
            ·
              refine ⟨5947319264120657079296717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964879509413771386197811 5947319264120657079296717)
              ·
                refine ⟨2230244724045246404736269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5947319264120657079296717 2230244724045246404736269)
                ·
                  refine ⟨836341771516967401776101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2230244724045246404736269 836341771516967401776101)
                  ·
                    refine ⟨156814082159431387833019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836341771516967401776101 156814082159431387833019)
                    ·
                      rfl

theorem cell23_916183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_916183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916183 prefixEnd_916183 := by exact prefixLift 916183
  have htrace : WordTrace (prefixWord ++ tailWord_916183) baseStart_916183 baseEnd_916183 := by
    simpa [prefixWord, tailWord_916183, baseEnd_916183] using wordTrace_append hprefix tailTrace_916183
  have hstable : (prefixWord ++ tailWord_916183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916183).length < 2 ^ (prefixWord ++ tailWord_916183).sum := by decide
  have hdescent : baseEnd_916183 < baseStart_916183 := by decide
  rcases family_descends (prefixWord ++ tailWord_916183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916186 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_916186 : Nat := 118140960795 + 916186 * 2 ^ 59
def prefixEnd_916186 : Nat := 4983230072969 + 3 ^ 40 * 916186 * 2
def baseEnd_916186 : Nat := 470443786920257651761543

theorem tailTrace_916186 : CollatzResearch.WordTrace tailWord_916186 prefixEnd_916186 470443786920257651761543 := by
  unfold tailWord_916186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354012164705517239132103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22277365772548045971018941 8354012164705517239132103)
  ·
    refine ⟨12531018247058275858698155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354012164705517239132103 12531018247058275858698155)
    ·
      refine ⟨18796527370587413788047233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531018247058275858698155 18796527370587413788047233)
      ·
        refine ⟨14097395527940560341035425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18796527370587413788047233 14097395527940560341035425)
        ·
          refine ⟨10573046645955420255776569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14097395527940560341035425 10573046645955420255776569)
          ·
            refine ⟨7929784984466565191832427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573046645955420255776569 7929784984466565191832427)
            ·
              refine ⟨11894677476699847787748641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929784984466565191832427 11894677476699847787748641)
              ·
                refine ⟨8921008107524885840811481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11894677476699847787748641 8921008107524885840811481)
                ·
                  refine ⟨6690756080643664380608611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921008107524885840811481 6690756080643664380608611)
                  ·
                    refine ⟨10036134120965496570912917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690756080643664380608611 10036134120965496570912917)
                    ·
                      refine ⟨470443786920257651761543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10036134120965496570912917 470443786920257651761543)
                      ·
                        rfl

theorem cell23_916186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_916186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916186 prefixEnd_916186 := by exact prefixLift 916186
  have htrace : WordTrace (prefixWord ++ tailWord_916186) baseStart_916186 baseEnd_916186 := by
    simpa [prefixWord, tailWord_916186, baseEnd_916186] using wordTrace_append hprefix tailTrace_916186
  have hstable : (prefixWord ++ tailWord_916186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916186).length < 2 ^ (prefixWord ++ tailWord_916186).sum := by decide
  have hdescent : baseEnd_916186 < baseStart_916186 := by decide
  rcases family_descends (prefixWord ++ tailWord_916186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916193 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_916193 : Nat := 118140960795 + 916193 * 2 ^ 59
def prefixEnd_916193 : Nat := 4983230072969 + 3 ^ 40 * 916193 * 2
def baseEnd_916193 : Nat := 470447381284839124374011

theorem tailTrace_916193 : CollatzResearch.WordTrace tailWord_916193 prefixEnd_916193 470447381284839124374011 := by
  unfold tailWord_916193
  simp only [CollatzResearch.WordTrace]
  refine ⟨33416303969796709152033233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22277535979864472768022155 33416303969796709152033233)
  ·
    refine ⟨25062227977347531864024925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33416303969796709152033233 25062227977347531864024925)
    ·
      refine ⟨9398335491505324449009347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25062227977347531864024925 9398335491505324449009347)
      ·
        refine ⟨14097503237257986673514021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398335491505324449009347 14097503237257986673514021)
        ·
          refine ⟨2643281856985872501283879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14097503237257986673514021 2643281856985872501283879)
          ·
            refine ⟨3964922785478808751925819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643281856985872501283879 3964922785478808751925819)
            ·
              refine ⟨5947384178218213127888729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964922785478808751925819 5947384178218213127888729)
              ·
                refine ⟨4460538133663659845916547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947384178218213127888729 4460538133663659845916547)
                ·
                  refine ⟨6690807200495489768874821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460538133663659845916547 6690807200495489768874821)
                  ·
                    refine ⟨1254526350092904331664029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690807200495489768874821 1254526350092904331664029)
                    ·
                      refine ⟨470447381284839124374011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254526350092904331664029 470447381284839124374011)
                      ·
                        rfl

theorem cell23_916193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_916193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916193 prefixEnd_916193 := by exact prefixLift 916193
  have htrace : WordTrace (prefixWord ++ tailWord_916193) baseStart_916193 baseEnd_916193 := by
    simpa [prefixWord, tailWord_916193, baseEnd_916193] using wordTrace_append hprefix tailTrace_916193
  have hstable : (prefixWord ++ tailWord_916193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916193).length < 2 ^ (prefixWord ++ tailWord_916193).sum := by decide
  have hdescent : baseEnd_916193 < baseStart_916193 := by decide
  rcases family_descends (prefixWord ++ tailWord_916193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916236 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_916236 : Nat := 118140960795 + 916236 * 2 ^ 59
def prefixEnd_916236 : Nat := 4983230072969 + 3 ^ 40 * 916236 * 2
def baseEnd_916236 : Nat := 470469460952982456136313

theorem tailTrace_916236 : CollatzResearch.WordTrace tailWord_916236 prefixEnd_916236 470469460952982456136313 := by
  unfold tailWord_916236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708936154320463747924281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22278581539093951663899041 16708936154320463747924281)
  ·
    refine ⟨12531702115740347810943211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16708936154320463747924281 12531702115740347810943211)
    ·
      refine ⟨18797553173610521716414817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531702115740347810943211 18797553173610521716414817)
      ·
        refine ⟨14098164880207891287311113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18797553173610521716414817 14098164880207891287311113)
        ·
          refine ⟨10573623660155918465483335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14098164880207891287311113 10573623660155918465483335)
          ·
            refine ⟨15860435490233877698225003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573623660155918465483335 15860435490233877698225003)
            ·
              refine ⟨23790653235350816547337505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15860435490233877698225003 23790653235350816547337505)
              ·
                refine ⟨17842989926513112410503129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23790653235350816547337505 17842989926513112410503129)
                ·
                  refine ⟨13382242444884834307877347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17842989926513112410503129 13382242444884834307877347)
                  ·
                    refine ⟨20073363667327251461816021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13382242444884834307877347 20073363667327251461816021)
                    ·
                      refine ⟨470469460952982456136313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20073363667327251461816021 470469460952982456136313)
                      ·
                        rfl

theorem cell23_916236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_916236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916236 prefixEnd_916236 := by exact prefixLift 916236
  have htrace : WordTrace (prefixWord ++ tailWord_916236) baseStart_916236 baseEnd_916236 := by
    simpa [prefixWord, tailWord_916236, baseEnd_916236] using wordTrace_append hprefix tailTrace_916236
  have hstable : (prefixWord ++ tailWord_916236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916236).length < 2 ^ (prefixWord ++ tailWord_916236).sum := by decide
  have hdescent : baseEnd_916236 < baseStart_916236 := by decide
  rcases family_descends (prefixWord ++ tailWord_916236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916247 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 6]
def baseStart_916247 : Nat := 118140960795 + 916247 * 2 ^ 59
def prefixEnd_916247 : Nat := 4983230072969 + 3 ^ 40 * 916247 * 2
def baseEnd_916247 : Nat := 52275012137797990344307

theorem tailTrace_916247 : CollatzResearch.WordTrace tailWord_916247 prefixEnd_916247 52275012137797990344307 := by
  unfold tailWord_916247
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418273511601076374498995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22278849007734050916332663 33418273511601076374498995)
  ·
    refine ⟨50127410267401614561748493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33418273511601076374498995 50127410267401614561748493)
    ·
      refine ⟨18797778850275605460655685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50127410267401614561748493 18797778850275605460655685)
      ·
        refine ⟨3524583534426676023872941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18797778850275605460655685 3524583534426676023872941)
        ·
          refine ⟨1321718825410003508952353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3524583534426676023872941 1321718825410003508952353)
          ·
            refine ⟨991289119057502631714265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321718825410003508952353 991289119057502631714265)
            ·
              refine ⟨743466839293126973785699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991289119057502631714265 743466839293126973785699)
              ·
                refine ⟨1115200258939690460678549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743466839293126973785699 1115200258939690460678549)
                ·
                  refine ⟨52275012137797990344307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1115200258939690460678549 52275012137797990344307)
                  ·
                    rfl

theorem cell23_916247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 6].length) (baseStart_916247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916247 prefixEnd_916247 := by exact prefixLift 916247
  have htrace : WordTrace (prefixWord ++ tailWord_916247) baseStart_916247 baseEnd_916247 := by
    simpa [prefixWord, tailWord_916247, baseEnd_916247] using wordTrace_append hprefix tailTrace_916247
  have hstable : (prefixWord ++ tailWord_916247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916247).length < 2 ^ (prefixWord ++ tailWord_916247).sum := by decide
  have hdescent : baseEnd_916247 < baseStart_916247 := by decide
  rcases family_descends (prefixWord ++ tailWord_916247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916250 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_916250 : Nat := 118140960795 + 916250 * 2 ^ 59
def prefixEnd_916250 : Nat := 4983230072969 + 3 ^ 40 * 916250 * 2
def baseEnd_916250 : Nat := 470476649682145401361249

theorem tailTrace_916250 : CollatzResearch.WordTrace tailWord_916250 prefixEnd_916250 470476649682145401361249 := by
  unfold tailWord_916250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354595732647551971714551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22278921953726805257905469 8354595732647551971714551)
  ·
    refine ⟨12531893598971327957571827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354595732647551971714551 12531893598971327957571827)
    ·
      refine ⟨18797840398456991936357741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531893598971327957571827 18797840398456991936357741)
      ·
        refine ⟨7049190149421371976134153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18797840398456991936357741 7049190149421371976134153)
        ·
          refine ⟨5286892612066028982100615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7049190149421371976134153 5286892612066028982100615)
          ·
            refine ⟨7930338918099043473150923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286892612066028982100615 7930338918099043473150923)
            ·
              refine ⟨11895508377148565209726385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930338918099043473150923 11895508377148565209726385)
              ·
                refine ⟨8921631282861423907294789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895508377148565209726385 8921631282861423907294789)
                ·
                  refine ⟨1672805865536516982617773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8921631282861423907294789 1672805865536516982617773)
                  ·
                    refine ⟨627302199576193868481665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672805865536516982617773 627302199576193868481665)
                    ·
                      refine ⟨470476649682145401361249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627302199576193868481665 470476649682145401361249)
                      ·
                        rfl

theorem cell23_916250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_916250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916250 prefixEnd_916250 := by exact prefixLift 916250
  have htrace : WordTrace (prefixWord ++ tailWord_916250) baseStart_916250 baseEnd_916250 := by
    simpa [prefixWord, tailWord_916250, baseEnd_916250] using wordTrace_append hprefix tailTrace_916250
  have hstable : (prefixWord ++ tailWord_916250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916250).length < 2 ^ (prefixWord ++ tailWord_916250).sum := by decide
  have hdescent : baseEnd_916250 < baseStart_916250 := by decide
  rcases family_descends (prefixWord ++ tailWord_916250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916260 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_916260 : Nat := 118140960795 + 916260 * 2 ^ 59
def prefixEnd_916260 : Nat := 4983230072969 + 3 ^ 40 * 916260 * 2
def baseEnd_916260 : Nat := 156827261496230120745401

theorem tailTrace_916260 : CollatzResearch.WordTrace tailWord_916260 prefixEnd_916260 156827261496230120745401 := by
  unfold tailWord_916260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16709373830276989797361117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22279165107035986396481489 16709373830276989797361117)
  ·
    refine ⟨6266015186353871174010419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16709373830276989797361117 6266015186353871174010419)
    ·
      refine ⟨9399022779530806761015629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6266015186353871174010419 9399022779530806761015629)
      ·
        refine ⟨3524633542324052535380861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9399022779530806761015629 3524633542324052535380861)
        ·
          refine ⟨1321737578371519700767823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3524633542324052535380861 1321737578371519700767823)
          ·
            refine ⟨1982606367557279551151735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321737578371519700767823 1982606367557279551151735)
            ·
              refine ⟨2973909551335919326727603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982606367557279551151735 2973909551335919326727603)
              ·
                refine ⟨4460864327003878990091405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973909551335919326727603 4460864327003878990091405)
                ·
                  refine ⟨1672824122626454621284277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4460864327003878990091405 1672824122626454621284277)
                  ·
                    refine ⟨156827261496230120745401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1672824122626454621284277 156827261496230120745401)
                    ·
                      rfl

theorem cell23_916260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_916260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916260 prefixEnd_916260 := by exact prefixLift 916260
  have htrace : WordTrace (prefixWord ++ tailWord_916260) baseStart_916260 baseEnd_916260 := by
    simpa [prefixWord, tailWord_916260, baseEnd_916260] using wordTrace_append hprefix tailTrace_916260
  have hstable : (prefixWord ++ tailWord_916260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916260).length < 2 ^ (prefixWord ++ tailWord_916260).sum := by decide
  have hdescent : baseEnd_916260 < baseStart_916260 := by decide
  rcases family_descends (prefixWord ++ tailWord_916260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916273 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_916273 : Nat := 118140960795 + 916273 * 2 ^ 59
def prefixEnd_916273 : Nat := 4983230072969 + 3 ^ 40 * 916273 * 2
def baseEnd_916273 : Nat := 156829486579066270457881

theorem tailTrace_916273 : CollatzResearch.WordTrace tailWord_916273 prefixEnd_916273 156829486579066270457881 := by
  unfold tailWord_916273
  simp only [CollatzResearch.WordTrace]
  refine ⟨33419221809506882814945473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22279481206337921876630315 33419221809506882814945473)
  ·
    refine ⟨25064416357130162111209105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33419221809506882814945473 25064416357130162111209105)
    ·
      refine ⟨18798312267847621583406829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25064416357130162111209105 18798312267847621583406829)
      ·
        refine ⟨7049367100442858093777561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18798312267847621583406829 7049367100442858093777561)
        ·
          refine ⟨5287025325332143570333171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7049367100442858093777561 5287025325332143570333171)
          ·
            refine ⟨7930537987998215355499757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287025325332143570333171 7930537987998215355499757)
            ·
              refine ⟨2973951745499330758312409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7930537987998215355499757 2973951745499330758312409)
              ·
                refine ⟨2230463809124498068734307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973951745499330758312409 2230463809124498068734307)
                ·
                  refine ⟨3345695713686747103101461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230463809124498068734307 3345695713686747103101461)
                  ·
                    refine ⟨156829486579066270457881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3345695713686747103101461 156829486579066270457881)
                    ·
                      rfl

theorem cell23_916273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_916273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916273 prefixEnd_916273 := by exact prefixLift 916273
  have htrace : WordTrace (prefixWord ++ tailWord_916273) baseStart_916273 baseEnd_916273 := by
    simpa [prefixWord, tailWord_916273, baseEnd_916273] using wordTrace_append hprefix tailTrace_916273
  have hstable : (prefixWord ++ tailWord_916273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916273).length < 2 ^ (prefixWord ++ tailWord_916273).sum := by decide
  have hdescent : baseEnd_916273 < baseStart_916273 := by decide
  rcases family_descends (prefixWord ++ tailWord_916273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
