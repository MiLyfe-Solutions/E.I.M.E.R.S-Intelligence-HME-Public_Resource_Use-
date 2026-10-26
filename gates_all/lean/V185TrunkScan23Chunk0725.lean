import V185TrunkScan23Chunk0724

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4288330 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4288330 : Nat := 118140960795 + 4288330 * 2 ^ 59
def prefixEnd_4288330 : Nat := 4983230072969 + 3 ^ 40 * 4288330 * 2
def baseEnd_4288330 : Nat := 2201974495095312122853335

theorem tailTrace_4288330 : CollatzResearch.WordTrace tailWord_4288330 prefixEnd_4288330 2201974495095312122853335 := by
  unfold tailWord_4288330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39102061138530068325171611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104272163036080182200457629 39102061138530068325171611)
  ·
    refine ⟨58653091707795102487757417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39102061138530068325171611 58653091707795102487757417)
    ·
      refine ⟨43989818780846326865818063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58653091707795102487757417 43989818780846326865818063)
      ·
        refine ⟨65984728171269490298727095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43989818780846326865818063 65984728171269490298727095)
        ·
          refine ⟨98977092256904235448090643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65984728171269490298727095 98977092256904235448090643)
          ·
            refine ⟨148465638385356353172135965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98977092256904235448090643 148465638385356353172135965)
            ·
              refine ⟨55674614394508632439550987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148465638385356353172135965 55674614394508632439550987)
              ·
                refine ⟨83511921591762948659326481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55674614394508632439550987 83511921591762948659326481)
                ·
                  refine ⟨62633941193822211494494861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83511921591762948659326481 62633941193822211494494861)
                  ·
                    refine ⟨23487727947683329310435573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62633941193822211494494861 23487727947683329310435573)
                    ·
                      refine ⟨2201974495095312122853335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23487727947683329310435573 2201974495095312122853335)
                      ·
                        rfl

theorem cell23_4288330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4288330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288330 prefixEnd_4288330 := by exact prefixLift 4288330
  have htrace : WordTrace (prefixWord ++ tailWord_4288330) baseStart_4288330 baseEnd_4288330 := by
    simpa [prefixWord, tailWord_4288330, baseEnd_4288330] using wordTrace_append hprefix tailTrace_4288330
  have hstable : (prefixWord ++ tailWord_4288330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288330).length < 2 ^ (prefixWord ++ tailWord_4288330).sum := by decide
  have hdescent : baseEnd_4288330 < baseStart_4288330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288354 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4288354 : Nat := 118140960795 + 4288354 * 2 ^ 59
def prefixEnd_4288354 : Nat := 4983230072969 + 3 ^ 40 * 4288354 * 2
def baseEnd_4288354 : Nat := 733995606210340009651075

theorem tailTrace_4288354 : CollatzResearch.WordTrace tailWord_4288354 prefixEnd_4288354 733995606210340009651075 := by
  unfold tailWord_4288354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39102279976508331349890029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104272746604022216933040077 39102279976508331349890029)
  ·
    refine ⟨14663354991190624256208761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39102279976508331349890029 14663354991190624256208761)
    ·
      refine ⟨10997516243392968192156571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14663354991190624256208761 10997516243392968192156571)
      ·
        refine ⟨16496274365089452288234857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10997516243392968192156571 16496274365089452288234857)
        ·
          refine ⟨12372205773817089216176143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16496274365089452288234857 12372205773817089216176143)
          ·
            refine ⟨18558308660725633824264215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12372205773817089216176143 18558308660725633824264215)
            ·
              refine ⟨27837462991088450736396323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18558308660725633824264215 27837462991088450736396323)
              ·
                refine ⟨41756194486632676104594485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27837462991088450736396323 41756194486632676104594485)
                ·
                  refine ⟨3914643233121813384805733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41756194486632676104594485 3914643233121813384805733)
                  ·
                    refine ⟨733995606210340009651075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3914643233121813384805733 733995606210340009651075)
                    ·
                      rfl

theorem cell23_4288354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4288354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288354 prefixEnd_4288354 := by exact prefixLift 4288354
  have htrace : WordTrace (prefixWord ++ tailWord_4288354) baseStart_4288354 baseEnd_4288354 := by
    simpa [prefixWord, tailWord_4288354, baseEnd_4288354] using wordTrace_append hprefix tailTrace_4288354
  have hstable : (prefixWord ++ tailWord_4288354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288354).length < 2 ^ (prefixWord ++ tailWord_4288354).sum := by decide
  have hdescent : baseEnd_4288354 < baseStart_4288354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288364 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_4288364 : Nat := 118140960795 + 4288364 * 2 ^ 59
def prefixEnd_4288364 : Nat := 4983230072969 + 3 ^ 40 * 4288364 * 2
def baseEnd_4288364 : Nat := 2201991953437564989828179

theorem tailTrace_4288364 : CollatzResearch.WordTrace tailWord_4288364 prefixEnd_4288364 2201991953437564989828179 := by
  unfold tailWord_4288364
  simp only [CollatzResearch.WordTrace]
  refine ⟨78204742317998548553712073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104272989757331398071616097 78204742317998548553712073)
  ·
    refine ⟨58653556738498911415284055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78204742317998548553712073 58653556738498911415284055)
    ·
      refine ⟨87980335107748367122926083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58653556738498911415284055 87980335107748367122926083)
      ·
        refine ⟨131970502661622550684389125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87980335107748367122926083 131970502661622550684389125)
        ·
          refine ⟨24744469249054228253322961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131970502661622550684389125 24744469249054228253322961)
          ·
            refine ⟨18558351936790671189992221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24744469249054228253322961 18558351936790671189992221)
            ·
              refine ⟨6959381976296501696247083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18558351936790671189992221 6959381976296501696247083)
              ·
                refine ⟨10439072964444752544370625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959381976296501696247083 10439072964444752544370625)
                ·
                  refine ⟨7829304723333564408277969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10439072964444752544370625 7829304723333564408277969)
                  ·
                    refine ⟨5871978542500173306208477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7829304723333564408277969 5871978542500173306208477)
                    ·
                      refine ⟨2201991953437564989828179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5871978542500173306208477 2201991953437564989828179)
                      ·
                        rfl

theorem cell23_4288364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_4288364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288364 prefixEnd_4288364 := by exact prefixLift 4288364
  have htrace : WordTrace (prefixWord ++ tailWord_4288364) baseStart_4288364 baseEnd_4288364 := by
    simpa [prefixWord, tailWord_4288364, baseEnd_4288364] using wordTrace_append hprefix tailTrace_4288364
  have hstable : (prefixWord ++ tailWord_4288364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288364).length < 2 ^ (prefixWord ++ tailWord_4288364).sum := by decide
  have hdescent : baseEnd_4288364 < baseStart_4288364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288445 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_4288445 : Nat := 118140960795 + 4288445 * 2 ^ 59
def prefixEnd_4288445 : Nat := 4983230072969 + 3 ^ 40 * 4288445 * 2
def baseEnd_4288445 : Nat := 2202033545370579172915307

theorem tailTrace_4288445 : CollatzResearch.WordTrace tailWord_4288445 prefixEnd_4288445 2202033545370579172915307 := by
  unfold tailWord_4288445
  simp only [CollatzResearch.WordTrace]
  refine ⟨156412438948703647941122789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104274959299135765294081859 156412438948703647941122789)
  ·
    refine ⟨29327332302881933988960523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156412438948703647941122789 29327332302881933988960523)
    ·
      refine ⟨43990998454322900983440785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29327332302881933988960523 43990998454322900983440785)
      ·
        refine ⟨32993248840742175737580589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43990998454322900983440785 32993248840742175737580589)
        ·
          refine ⟨12372468315278315901592721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32993248840742175737580589 12372468315278315901592721)
          ·
            refine ⟨9279351236458736926194541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12372468315278315901592721 9279351236458736926194541)
            ·
              refine ⟨3479756713672026347322953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9279351236458736926194541 3479756713672026347322953)
              ·
                refine ⟨2609817535254019760492215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479756713672026347322953 2609817535254019760492215)
                ·
                  refine ⟨3914726302881029640738323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609817535254019760492215 3914726302881029640738323)
                  ·
                    refine ⟨5872089454321544461107485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914726302881029640738323 5872089454321544461107485)
                    ·
                      refine ⟨2202033545370579172915307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872089454321544461107485 2202033545370579172915307)
                      ·
                        rfl

theorem cell23_4288445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_4288445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288445 prefixEnd_4288445 := by exact prefixLift 4288445
  have htrace : WordTrace (prefixWord ++ tailWord_4288445) baseStart_4288445 baseEnd_4288445 := by
    simpa [prefixWord, tailWord_4288445, baseEnd_4288445] using wordTrace_append hprefix tailTrace_4288445
  have hstable : (prefixWord ++ tailWord_4288445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288445).length < 2 ^ (prefixWord ++ tailWord_4288445).sum := by decide
  have hdescent : baseEnd_4288445 < baseStart_4288445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288484 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_4288484 : Nat := 118140960795 + 4288484 * 2 ^ 59
def prefixEnd_4288484 : Nat := 4983230072969 + 3 ^ 40 * 4288484 * 2
def baseEnd_4288484 : Nat := 2202053571116104520327627

theorem tailTrace_4288484 : CollatzResearch.WordTrace tailWord_4288484 prefixEnd_4288484 2202053571116104520327627 := by
  unfold tailWord_4288484
  simp only [CollatzResearch.WordTrace]
  refine ⟨78206930697781178800896253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104275907597041571734528337 78206930697781178800896253)
  ·
    refine ⟨29327599011667942050336095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78206930697781178800896253 29327599011667942050336095)
    ·
      refine ⟨43991398517501913075504143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29327599011667942050336095 43991398517501913075504143)
      ·
        refine ⟨65987097776252869613256215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43991398517501913075504143 65987097776252869613256215)
        ·
          refine ⟨98980646664379304419884323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65987097776252869613256215 98980646664379304419884323)
          ·
            refine ⟨148470969996568956629826485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98980646664379304419884323 148470969996568956629826485)
            ·
              refine ⟨13919153437178339684046233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148470969996568956629826485 13919153437178339684046233)
              ·
                refine ⟨10439365077883754763034675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13919153437178339684046233 10439365077883754763034675)
                ·
                  refine ⟨15659047616825632144552013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10439365077883754763034675 15659047616825632144552013)
                  ·
                    refine ⟨5872142856309612054207005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15659047616825632144552013 5872142856309612054207005)
                    ·
                      refine ⟨2202053571116104520327627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872142856309612054207005 2202053571116104520327627)
                      ·
                        rfl

theorem cell23_4288484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_4288484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288484 prefixEnd_4288484 := by exact prefixLift 4288484
  have htrace : WordTrace (prefixWord ++ tailWord_4288484) baseStart_4288484 baseEnd_4288484 := by
    simpa [prefixWord, tailWord_4288484, baseEnd_4288484] using wordTrace_append hprefix tailTrace_4288484
  have hstable : (prefixWord ++ tailWord_4288484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288484).length < 2 ^ (prefixWord ++ tailWord_4288484).sum := by decide
  have hdescent : baseEnd_4288484 < baseStart_4288484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288502 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4288502 : Nat := 118140960795 + 4288502 * 2 ^ 59
def prefixEnd_4288502 : Nat := 4983230072969 + 3 ^ 40 * 4288502 * 2
def baseEnd_4288502 : Nat := 2202062813767885449902545

theorem tailTrace_4288502 : CollatzResearch.WordTrace tailWord_4288502 prefixEnd_4288502 2202062813767885449902545 := by
  unfold tailWord_4288502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775907369343571667246735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104276345272998097783965173 9775907369343571667246735)
  ·
    refine ⟨14663861054015357500870103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9775907369343571667246735 14663861054015357500870103)
    ·
      refine ⟨21995791581023036251305155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14663861054015357500870103 21995791581023036251305155)
      ·
        refine ⟨32993687371534554376957733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21995791581023036251305155 32993687371534554376957733)
        ·
          refine ⟨6186316382162728945679575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32993687371534554376957733 6186316382162728945679575)
          ·
            refine ⟨9279474573244093418519363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186316382162728945679575 9279474573244093418519363)
            ·
              refine ⟨13919211859866140127779045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9279474573244093418519363 13919211859866140127779045)
              ·
                refine ⟨2609852223724901273958571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13919211859866140127779045 2609852223724901273958571)
                ·
                  refine ⟨3914778335587351910937857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609852223724901273958571 3914778335587351910937857)
                  ·
                    refine ⟨2936083751690513933203393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3914778335587351910937857 2936083751690513933203393)
                    ·
                      refine ⟨2202062813767885449902545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936083751690513933203393 2202062813767885449902545)
                      ·
                        rfl

theorem cell23_4288502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4288502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288502 prefixEnd_4288502 := by exact prefixLift 4288502
  have htrace : WordTrace (prefixWord ++ tailWord_4288502) baseStart_4288502 baseEnd_4288502 := by
    simpa [prefixWord, tailWord_4288502, baseEnd_4288502] using wordTrace_append hprefix tailTrace_4288502
  have hstable : (prefixWord ++ tailWord_4288502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288502).length < 2 ^ (prefixWord ++ tailWord_4288502).sum := by decide
  have hdescent : baseEnd_4288502 < baseStart_4288502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288507 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_4288507 : Nat := 118140960795 + 4288507 * 2 ^ 59
def prefixEnd_4288507 : Nat := 4983230072969 + 3 ^ 40 * 4288507 * 2
def baseEnd_4288507 : Nat := 2202065381171157930340021

theorem tailTrace_4288507 : CollatzResearch.WordTrace tailWord_4288507 prefixEnd_4288507 2202065381171157930340021 := by
  unfold tailWord_4288507
  simp only [CollatzResearch.WordTrace]
  refine ⟨156414700274479032529879775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104276466849652688353253183 156414700274479032529879775)
  ·
    refine ⟨234622050411718548794819663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156414700274479032529879775 234622050411718548794819663)
    ·
      refine ⟨351933075617577823192229495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234622050411718548794819663 351933075617577823192229495)
      ·
        refine ⟨527899613426366734788344243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351933075617577823192229495 527899613426366734788344243)
        ·
          refine ⟨791849420139550102182516365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527899613426366734788344243 791849420139550102182516365)
          ·
            refine ⟨296943532552331288318443637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791849420139550102182516365 296943532552331288318443637)
            ·
              refine ⟨27838456176781058279854091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296943532552331288318443637 27838456176781058279854091)
              ·
                refine ⟨41757684265171587419781137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27838456176781058279854091 41757684265171587419781137)
                ·
                  refine ⟨31318263198878690564835853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41757684265171587419781137 31318263198878690564835853)
                  ·
                    refine ⟨11744348699579508961813445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31318263198878690564835853 11744348699579508961813445)
                    ·
                      refine ⟨2202065381171157930340021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11744348699579508961813445 2202065381171157930340021)
                      ·
                        rfl

theorem cell23_4288507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_4288507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288507 prefixEnd_4288507 := by exact prefixLift 4288507
  have htrace : WordTrace (prefixWord ++ tailWord_4288507) baseStart_4288507 baseEnd_4288507 := by
    simpa [prefixWord, tailWord_4288507, baseEnd_4288507] using wordTrace_append hprefix tailTrace_4288507
  have hstable : (prefixWord ++ tailWord_4288507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288507).length < 2 ^ (prefixWord ++ tailWord_4288507).sum := by decide
  have hdescent : baseEnd_4288507 < baseStart_4288507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288517 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_4288517 : Nat := 118140960795 + 4288517 * 2 ^ 59
def prefixEnd_4288517 : Nat := 4983230072969 + 3 ^ 40 * 4288517 * 2
def baseEnd_4288517 : Nat := 734023505325900963738325

theorem tailTrace_4288517 : CollatzResearch.WordTrace tailWord_4288517 prefixEnd_4288517 734023505325900963738325 := by
  unfold tailWord_4288517
  simp only [CollatzResearch.WordTrace]
  refine ⟨156415065004442804237743805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104276710002961869491829203 156415065004442804237743805)
  ·
    refine ⟨58655649376666051589153927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156415065004442804237743805 58655649376666051589153927)
    ·
      refine ⟨87983474064999077383730891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58655649376666051589153927 87983474064999077383730891)
      ·
        refine ⟨131975211097498616075596337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87983474064999077383730891 131975211097498616075596337)
        ·
          refine ⟨98981408323123962056697253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131975211097498616075596337 98981408323123962056697253)
          ·
            refine ⟨18559014060585742885630735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98981408323123962056697253 18559014060585742885630735)
            ·
              refine ⟨27838521090878614328446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18559014060585742885630735 27838521090878614328446103)
              ·
                refine ⟨41757781636317921492669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27838521090878614328446103 41757781636317921492669155)
                ·
                  refine ⟨62636672454476882239003733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41757781636317921492669155 62636672454476882239003733)
                  ·
                    refine ⟨734023505325900963738325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62636672454476882239003733 734023505325900963738325)
                    ·
                      rfl

theorem cell23_4288517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_4288517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288517 prefixEnd_4288517 := by exact prefixLift 4288517
  have htrace : WordTrace (prefixWord ++ tailWord_4288517) baseStart_4288517 baseEnd_4288517 := by
    simpa [prefixWord, tailWord_4288517, baseEnd_4288517] using wordTrace_append hprefix tailTrace_4288517
  have hstable : (prefixWord ++ tailWord_4288517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288517).length < 2 ^ (prefixWord ++ tailWord_4288517).sum := by decide
  have hdescent : baseEnd_4288517 < baseStart_4288517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288525 : List Nat := [1, 7, 1, 2, 1, 1, 3, 7]
def baseStart_4288525 : Nat := 118140960795 + 4288525 * 2 ^ 59
def prefixEnd_4288525 : Nat := 4983230072969 + 3 ^ 40 * 4288525 * 2
def baseEnd_4288525 : Nat := 81558319400849587404257

theorem tailTrace_4288525 : CollatzResearch.WordTrace tailWord_4288525 prefixEnd_4288525 81558319400849587404257 := by
  unfold tailWord_4288525
  simp only [CollatzResearch.WordTrace]
  refine ⟨156415356788413821604035029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104276904525609214402690019 156415356788413821604035029)
  ·
    refine ⟨3665984924728448943844571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 156415356788413821604035029 3665984924728448943844571)
    ·
      refine ⟨5498977387092673415766857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665984924728448943844571 5498977387092673415766857)
      ·
        refine ⟨4124233040319505061825143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5498977387092673415766857 4124233040319505061825143)
        ·
          refine ⟨6186349560479257592737715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124233040319505061825143 6186349560479257592737715)
          ·
            refine ⟨9279524340718886389106573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186349560479257592737715 9279524340718886389106573)
            ·
              refine ⟨3479821627769582395914965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9279524340718886389106573 3479821627769582395914965)
              ·
                refine ⟨81558319400849587404257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3479821627769582395914965 81558319400849587404257)
                ·
                  rfl

theorem cell23_4288525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 7].length) (baseStart_4288525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288525 prefixEnd_4288525 := by exact prefixLift 4288525
  have htrace : WordTrace (prefixWord ++ tailWord_4288525) baseStart_4288525 baseEnd_4288525 := by
    simpa [prefixWord, tailWord_4288525, baseEnd_4288525] using wordTrace_append hprefix tailTrace_4288525
  have hstable : (prefixWord ++ tailWord_4288525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288525).length < 2 ^ (prefixWord ++ tailWord_4288525).sum := by decide
  have hdescent : baseEnd_4288525 < baseStart_4288525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288537 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_4288537 : Nat := 118140960795 + 4288537 * 2 ^ 59
def prefixEnd_4288537 : Nat := 4983230072969 + 3 ^ 40 * 4288537 * 2
def baseEnd_4288537 : Nat := 2202080785590792812964883

theorem tailTrace_4288537 : CollatzResearch.WordTrace tailWord_4288537 prefixEnd_4288537 2202080785590792812964883 := by
  unfold tailWord_4288537
  simp only [CollatzResearch.WordTrace]
  refine ⟨156415794464370347653471865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104277196309580231768981243 156415794464370347653471865)
  ·
    refine ⟨117311845848277760740103899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156415794464370347653471865 117311845848277760740103899)
    ·
      refine ⟨175967768772416641110155849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117311845848277760740103899 175967768772416641110155849)
      ·
        refine ⟨131975826579312480832616887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175967768772416641110155849 131975826579312480832616887)
        ·
          refine ⟨197963739868968721248925331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131975826579312480832616887 197963739868968721248925331)
          ·
            refine ⟨296945609803453081873387997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197963739868968721248925331 296945609803453081873387997)
            ·
              refine ⟨111354603676294905702520499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296945609803453081873387997 111354603676294905702520499)
              ·
                refine ⟨167031905514442358553780749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111354603676294905702520499 167031905514442358553780749)
                ·
                  refine ⟨62636964567915884457667781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167031905514442358553780749 62636964567915884457667781)
                  ·
                    refine ⟨11744430856484228335812709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62636964567915884457667781 11744430856484228335812709)
                    ·
                      refine ⟨2202080785590792812964883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11744430856484228335812709 2202080785590792812964883)
                      ·
                        rfl

theorem cell23_4288537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_4288537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288537 prefixEnd_4288537 := by exact prefixLift 4288537
  have htrace : WordTrace (prefixWord ++ tailWord_4288537) baseStart_4288537 baseEnd_4288537 := by
    simpa [prefixWord, tailWord_4288537, baseEnd_4288537] using wordTrace_append hprefix tailTrace_4288537
  have hstable : (prefixWord ++ tailWord_4288537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288537).length < 2 ^ (prefixWord ++ tailWord_4288537).sum := by decide
  have hdescent : baseEnd_4288537 < baseStart_4288537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288547 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 9]
def baseStart_4288547 : Nat := 118140960795 + 4288547 * 2 ^ 59
def prefixEnd_4288547 : Nat := 4983230072969 + 3 ^ 40 * 4288547 * 2
def baseEnd_4288547 : Nat := 244676213377481974871093

theorem tailTrace_4288547 : CollatzResearch.WordTrace tailWord_4288547 prefixEnd_4288547 244676213377481974871093 := by
  unfold tailWord_4288547
  simp only [CollatzResearch.WordTrace]
  refine ⟨156416159194334119361335895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104277439462889412907557263 156416159194334119361335895)
  ·
    refine ⟨234624238791501179042003843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156416159194334119361335895 234624238791501179042003843)
    ·
      refine ⟨351936358187251768563005765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234624238791501179042003843 351936358187251768563005765)
      ·
        refine ⟨65988067160109706605563581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 351936358187251768563005765 65988067160109706605563581)
        ·
          refine ⟨24745525185041139977086343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65988067160109706605563581 24745525185041139977086343)
          ·
            refine ⟨37118287777561709965629515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24745525185041139977086343 37118287777561709965629515)
            ·
              refine ⟨55677431666342564948444273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37118287777561709965629515 55677431666342564948444273)
              ·
                refine ⟨41758073749756923711333205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55677431666342564948444273 41758073749756923711333205)
                ·
                  refine ⟨244676213377481974871093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41758073749756923711333205 244676213377481974871093)
                  ·
                    rfl

theorem cell23_4288547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 9].length) (baseStart_4288547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288547 prefixEnd_4288547 := by exact prefixLift 4288547
  have htrace : WordTrace (prefixWord ++ tailWord_4288547) baseStart_4288547 baseEnd_4288547 := by
    simpa [prefixWord, tailWord_4288547, baseEnd_4288547] using wordTrace_append hprefix tailTrace_4288547
  have hstable : (prefixWord ++ tailWord_4288547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288547).length < 2 ^ (prefixWord ++ tailWord_4288547).sum := by decide
  have hdescent : baseEnd_4288547 < baseStart_4288547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288552 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4288552 : Nat := 118140960795 + 4288552 * 2 ^ 59
def prefixEnd_4288552 : Nat := 4983230072969 + 3 ^ 40 * 4288552 * 2
def baseEnd_4288552 : Nat := 2202088487800610254277315

theorem tailTrace_4288552 : CollatzResearch.WordTrace tailWord_4288552 prefixEnd_4288552 2202088487800610254277315 := by
  unfold tailWord_4288552
  simp only [CollatzResearch.WordTrace]
  refine ⟨78208170779658002607633955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104277561039544003476845273 78208170779658002607633955)
  ·
    refine ⟨117312256169487003911450933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78208170779658002607633955 117312256169487003911450933)
    ·
      refine ⟨10998024015889406616698525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117312256169487003911450933 10998024015889406616698525)
      ·
        refine ⟨4124259005958527481261947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10998024015889406616698525 4124259005958527481261947)
        ·
          refine ⟨6186388508937791221892921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124259005958527481261947 6186388508937791221892921)
          ·
            refine ⟨4639791381703343416419691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6186388508937791221892921 4639791381703343416419691)
            ·
              refine ⟨6959687072555015124629537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639791381703343416419691 6959687072555015124629537)
              ·
                refine ⟨5219765304416261343472153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6959687072555015124629537 5219765304416261343472153)
                ·
                  refine ⟨3914823978312196007604115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5219765304416261343472153 3914823978312196007604115)
                  ·
                    refine ⟨5872235967468294011406173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914823978312196007604115 5872235967468294011406173)
                    ·
                      refine ⟨2202088487800610254277315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872235967468294011406173 2202088487800610254277315)
                      ·
                        rfl

theorem cell23_4288552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4288552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288552 prefixEnd_4288552 := by exact prefixLift 4288552
  have htrace : WordTrace (prefixWord ++ tailWord_4288552) baseStart_4288552 baseEnd_4288552 := by
    simpa [prefixWord, tailWord_4288552, baseEnd_4288552] using wordTrace_append hprefix tailTrace_4288552
  have hstable : (prefixWord ++ tailWord_4288552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288552).length < 2 ^ (prefixWord ++ tailWord_4288552).sum := by decide
  have hdescent : baseEnd_4288552 < baseStart_4288552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288587 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_4288587 : Nat := 118140960795 + 4288587 * 2 ^ 59
def prefixEnd_4288587 : Nat := 4983230072969 + 3 ^ 40 * 4288587 * 2
def baseEnd_4288587 : Nat := 2202106459623517617339653

theorem tailTrace_4288587 : CollatzResearch.WordTrace tailWord_4288587 prefixEnd_4288587 2202106459623517617339653 := by
  unfold tailWord_4288587
  simp only [CollatzResearch.WordTrace]
  refine ⟨156417618114189206192792015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104278412076126137461861343 156417618114189206192792015)
  ·
    refine ⟨234626427171283809289188023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156417618114189206192792015 234626427171283809289188023)
    ·
      refine ⟨351939640756925713933782035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234626427171283809289188023 351939640756925713933782035)
      ·
        refine ⟨527909461135388570900673053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351939640756925713933782035 527909461135388570900673053)
        ·
          refine ⟨197966047925770714087752395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527909461135388570900673053 197966047925770714087752395)
          ·
            refine ⟨296949071888656071131628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197966047925770714087752395 296949071888656071131628593)
            ·
              refine ⟨222711803916492053348721445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296949071888656071131628593 222711803916492053348721445)
              ·
                refine ⟨41758463234342260002885271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222711803916492053348721445 41758463234342260002885271)
                ·
                  refine ⟨62637694851513390004327907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41758463234342260002885271 62637694851513390004327907)
                  ·
                    refine ⟨93956542277270085006491861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62637694851513390004327907 93956542277270085006491861)
                    ·
                      refine ⟨2202106459623517617339653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93956542277270085006491861 2202106459623517617339653)
                      ·
                        rfl

theorem cell23_4288587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_4288587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288587 prefixEnd_4288587 := by exact prefixLift 4288587
  have htrace : WordTrace (prefixWord ++ tailWord_4288587) baseStart_4288587 baseEnd_4288587 := by
    simpa [prefixWord, tailWord_4288587, baseEnd_4288587] using wordTrace_append hprefix tailTrace_4288587
  have hstable : (prefixWord ++ tailWord_4288587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288587).length < 2 ^ (prefixWord ++ tailWord_4288587).sum := by decide
  have hdescent : baseEnd_4288587 < baseStart_4288587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288648 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4288648 : Nat := 118140960795 + 4288648 * 2 ^ 59
def prefixEnd_4288648 : Nat := 4983230072969 + 3 ^ 40 * 4288648 * 2
def baseEnd_4288648 : Nat := 2202137781943441878676873

theorem tailTrace_4288648 : CollatzResearch.WordTrace tailWord_4288648 prefixEnd_4288648 2202137781943441878676873 := by
  unfold tailWord_4288648
  simp only [CollatzResearch.WordTrace]
  refine ⟨78209921483484106805381299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104279895311312142407175065 78209921483484106805381299)
  ·
    refine ⟨117314882225226160208071949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78209921483484106805381299 117314882225226160208071949)
    ·
      refine ⟨43993080834459810078026981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117314882225226160208071949 43993080834459810078026981)
      ·
        refine ⟨8248702656461214389630059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43993080834459810078026981 8248702656461214389630059)
        ·
          refine ⟨12373053984691821584445089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248702656461214389630059 12373053984691821584445089)
          ·
            refine ⟨9279790488518866188333817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12373053984691821584445089 9279790488518866188333817)
            ·
              refine ⟨6959842866389149641250363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9279790488518866188333817 6959842866389149641250363)
              ·
                refine ⟨10439764299583724461875545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959842866389149641250363 10439764299583724461875545)
                ·
                  refine ⟨7829823224687793346406659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10439764299583724461875545 7829823224687793346406659)
                  ·
                    refine ⟨11744734837031690019609989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7829823224687793346406659 11744734837031690019609989)
                    ·
                      refine ⟨2202137781943441878676873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11744734837031690019609989 2202137781943441878676873)
                      ·
                        rfl

theorem cell23_4288648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4288648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288648 prefixEnd_4288648 := by exact prefixLift 4288648
  have htrace : WordTrace (prefixWord ++ tailWord_4288648) baseStart_4288648 baseEnd_4288648 := by
    simpa [prefixWord, tailWord_4288648, baseEnd_4288648] using wordTrace_append hprefix tailTrace_4288648
  have hstable : (prefixWord ++ tailWord_4288648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288648).length < 2 ^ (prefixWord ++ tailWord_4288648).sum := by decide
  have hdescent : baseEnd_4288648 < baseStart_4288648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288671 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 6]
def baseStart_4288671 : Nat := 118140960795 + 4288671 * 2 ^ 59
def prefixEnd_4288671 : Nat := 4983230072969 + 3 ^ 40 * 4288671 * 2
def baseEnd_4288671 : Nat := 244683287999832809854363

theorem tailTrace_4288671 : CollatzResearch.WordTrace tailWord_4288671 prefixEnd_4288671 244683287999832809854363 := by
  unfold tailWord_4288671
  simp only [CollatzResearch.WordTrace]
  refine ⟨156420681845884888538849867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104280454563923259025899911 156420681845884888538849867)
  ·
    refine ⟨234631022768827332808274801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156420681845884888538849867 234631022768827332808274801)
    ·
      refine ⟨175973267076620499606206101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234631022768827332808274801 175973267076620499606206101)
      ·
        refine ⟨8248746894216585919040911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175973267076620499606206101 8248746894216585919040911)
        ·
          refine ⟨12373120341324878878561367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248746894216585919040911 12373120341324878878561367)
          ·
            refine ⟨18559680511987318317842051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12373120341324878878561367 18559680511987318317842051)
            ·
              refine ⟨27839520767980977476763077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18559680511987318317842051 27839520767980977476763077)
              ·
                refine ⟨5219910143996433276893077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27839520767980977476763077 5219910143996433276893077)
                ·
                  refine ⟨244683287999832809854363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5219910143996433276893077 244683287999832809854363)
                  ·
                    rfl

theorem cell23_4288671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 6].length) (baseStart_4288671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288671 prefixEnd_4288671 := by exact prefixLift 4288671
  have htrace : WordTrace (prefixWord ++ tailWord_4288671) baseStart_4288671 baseEnd_4288671 := by
    simpa [prefixWord, tailWord_4288671, baseEnd_4288671] using wordTrace_append hprefix tailTrace_4288671
  have hstable : (prefixWord ++ tailWord_4288671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288671).length < 2 ^ (prefixWord ++ tailWord_4288671).sum := by decide
  have hdescent : baseEnd_4288671 < baseStart_4288671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288691 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 5, 2]
def baseStart_4288691 : Nat := 118140960795 + 4288691 * 2 ^ 59
def prefixEnd_4288691 : Nat := 4983230072969 + 3 ^ 40 * 4288691 * 2
def baseEnd_4288691 : Nat := 2202159861611585210439175

theorem tailTrace_4288691 : CollatzResearch.WordTrace tailWord_4288691 prefixEnd_4288691 2202159861611585210439175 := by
  unfold tailWord_4288691
  simp only [CollatzResearch.WordTrace]
  refine ⟨156421411305812431954577927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104280940870541621303051951 156421411305812431954577927)
  ·
    refine ⟨234632116958718647931866891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156421411305812431954577927 234632116958718647931866891)
    ·
      refine ⟨351948175438077971897800337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234632116958718647931866891 351948175438077971897800337)
      ·
        refine ⟨263961131578558478923350253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351948175438077971897800337 263961131578558478923350253)
        ·
          refine ⟨98985424341959429596256345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263961131578558478923350253 98985424341959429596256345)
          ·
            refine ⟨74239068256469572197192259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98985424341959429596256345 74239068256469572197192259)
            ·
              refine ⟨111358602384704358295788389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74239068256469572197192259 111358602384704358295788389)
              ·
                refine ⟨20879737947132067180460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111358602384704358295788389 20879737947132067180460323)
                ·
                  refine ⟨31319606920698100770690485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20879737947132067180460323 31319606920698100770690485)
                  ·
                    refine ⟨2936213148815446947252233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31319606920698100770690485 2936213148815446947252233)
                    ·
                      refine ⟨2202159861611585210439175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936213148815446947252233 2202159861611585210439175)
                      ·
                        rfl

theorem cell23_4288691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5, 2].length) (baseStart_4288691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288691 prefixEnd_4288691 := by exact prefixLift 4288691
  have htrace : WordTrace (prefixWord ++ tailWord_4288691) baseStart_4288691 baseEnd_4288691 := by
    simpa [prefixWord, tailWord_4288691, baseEnd_4288691] using wordTrace_append hprefix tailTrace_4288691
  have hstable : (prefixWord ++ tailWord_4288691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288691).length < 2 ^ (prefixWord ++ tailWord_4288691).sum := by decide
  have hdescent : baseEnd_4288691 < baseStart_4288691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288701 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_4288701 : Nat := 118140960795 + 4288701 * 2 ^ 59
def prefixEnd_4288701 : Nat := 4983230072969 + 3 ^ 40 * 4288701 * 2
def baseEnd_4288701 : Nat := 734054998806043390438043

theorem tailTrace_4288701 : CollatzResearch.WordTrace tailWord_4288701 prefixEnd_4288701 734054998806043390438043 := by
  unfold tailWord_4288701
  simp only [CollatzResearch.WordTrace]
  refine ⟨156421776035776203662441957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104281184023850802441627971 156421776035776203662441957)
  ·
    refine ⟨29329083006708038186707867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156421776035776203662441957 29329083006708038186707867)
    ·
      refine ⟨43993624510062057280061801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29329083006708038186707867 43993624510062057280061801)
      ·
        refine ⟨32995218382546542960046351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43993624510062057280061801 32995218382546542960046351)
        ·
          refine ⟨49492827573819814440069527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32995218382546542960046351 49492827573819814440069527)
          ·
            refine ⟨74239241360729721660104291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49492827573819814440069527 74239241360729721660104291)
            ·
              refine ⟨111358862041094582490156437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74239241360729721660104291 111358862041094582490156437)
              ·
                refine ⟨5219946658176308554226083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111358862041094582490156437 5219946658176308554226083)
                ·
                  refine ⟨7829919987264462831339125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5219946658176308554226083 7829919987264462831339125)
                  ·
                    refine ⟨734054998806043390438043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7829919987264462831339125 734054998806043390438043)
                    ·
                      rfl

theorem cell23_4288701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_4288701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288701 prefixEnd_4288701 := by exact prefixLift 4288701
  have htrace : WordTrace (prefixWord ++ tailWord_4288701) baseStart_4288701 baseEnd_4288701 := by
    simpa [prefixWord, tailWord_4288701, baseEnd_4288701] using wordTrace_append hprefix tailTrace_4288701
  have hstable : (prefixWord ++ tailWord_4288701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288701).length < 2 ^ (prefixWord ++ tailWord_4288701).sum := by decide
  have hdescent : baseEnd_4288701 < baseStart_4288701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288702 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_4288702 : Nat := 118140960795 + 4288702 * 2 ^ 59
def prefixEnd_4288702 : Nat := 4983230072969 + 3 ^ 40 * 4288702 * 2
def baseEnd_4288702 : Nat := 2202165509898784667401625

theorem tailTrace_4288702 : CollatzResearch.WordTrace tailWord_4288702 prefixEnd_4288702 2202165509898784667401625 := by
  unfold tailWord_4288702
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552726563596572604153545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104281208339181720555485573 19552726563596572604153545)
  ·
    refine ⟨14664544922697429453115159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19552726563596572604153545 14664544922697429453115159)
    ·
      refine ⟨21996817384046144179672739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14664544922697429453115159 21996817384046144179672739)
      ·
        refine ⟨32995226076069216269509109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21996817384046144179672739 32995226076069216269509109)
        ·
          refine ⟨3093302444631489025266479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32995226076069216269509109 3093302444631489025266479)
          ·
            refine ⟨4639953666947233537899719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093302444631489025266479 4639953666947233537899719)
            ·
              refine ⟨6959930500420850306849579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639953666947233537899719 6959930500420850306849579)
              ·
                refine ⟨10439895750631275460274369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959930500420850306849579 10439895750631275460274369)
                ·
                  refine ⟨7829921812973456595205777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10439895750631275460274369 7829921812973456595205777)
                  ·
                    refine ⟨5872441359730092446404333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7829921812973456595205777 5872441359730092446404333)
                    ·
                      refine ⟨2202165509898784667401625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872441359730092446404333 2202165509898784667401625)
                      ·
                        rfl

theorem cell23_4288702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_4288702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288702 prefixEnd_4288702 := by exact prefixLift 4288702
  have htrace : WordTrace (prefixWord ++ tailWord_4288702) baseStart_4288702 baseEnd_4288702 := by
    simpa [prefixWord, tailWord_4288702, baseEnd_4288702] using wordTrace_append hprefix tailTrace_4288702
  have hstable : (prefixWord ++ tailWord_4288702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288702).length < 2 ^ (prefixWord ++ tailWord_4288702).sum := by decide
  have hdescent : baseEnd_4288702 < baseStart_4288702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288715 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 1, 1, 3]
def baseStart_4288715 : Nat := 118140960795 + 4288715 * 2 ^ 59
def prefixEnd_4288715 : Nat := 4983230072969 + 3 ^ 40 * 4288715 * 2
def baseEnd_4288715 : Nat := 2202172185147293116539065

theorem tailTrace_4288715 : CollatzResearch.WordTrace tailWord_4288715 prefixEnd_4288715 2202172185147293116539065 := by
  unfold tailWord_4288715
  simp only [CollatzResearch.WordTrace]
  refine ⟨156422286657725484053451599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104281524438483656035634399 156422286657725484053451599)
  ·
    refine ⟨234633429986588226080177399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156422286657725484053451599 234633429986588226080177399)
    ·
      refine ⟨351950144979882339120266099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234633429986588226080177399 351950144979882339120266099)
      ·
        refine ⟨527925217469823508680399149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351950144979882339120266099 527925217469823508680399149)
        ·
          refine ⟨197971956551183815755149681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527925217469823508680399149 197971956551183815755149681)
          ·
            refine ⟨148478967413387861816362261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197971956551183815755149681 148478967413387861816362261)
            ·
              refine ⟨6959951597502556022641981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148478967413387861816362261 6959951597502556022641981)
              ·
                refine ⟨2609981849063458508490743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6959951597502556022641981 2609981849063458508490743)
                ·
                  refine ⟨3914972773595187762736115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609981849063458508490743 3914972773595187762736115)
                  ·
                    refine ⟨5872459160392781644104173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914972773595187762736115 5872459160392781644104173)
                    ·
                      refine ⟨2202172185147293116539065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872459160392781644104173 2202172185147293116539065)
                      ·
                        rfl

theorem cell23_4288715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 1, 3].length) (baseStart_4288715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288715 prefixEnd_4288715 := by exact prefixLift 4288715
  have htrace : WordTrace (prefixWord ++ tailWord_4288715) baseStart_4288715 baseEnd_4288715 := by
    simpa [prefixWord, tailWord_4288715, baseEnd_4288715] using wordTrace_append hprefix tailTrace_4288715
  have hstable : (prefixWord ++ tailWord_4288715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288715).length < 2 ^ (prefixWord ++ tailWord_4288715).sum := by decide
  have hdescent : baseEnd_4288715 < baseStart_4288715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288718 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_4288718 : Nat := 118140960795 + 4288718 * 2 ^ 59
def prefixEnd_4288718 : Nat := 4983230072969 + 3 ^ 40 * 4288718 * 2
def baseEnd_4288718 : Nat := 734057908529752201600517

theorem tailTrace_4288718 : CollatzResearch.WordTrace tailWord_4288718 prefixEnd_4288718 734057908529752201600517 := by
  unfold tailWord_4288718
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552799509589326945726351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104281597384476410377207205 19552799509589326945726351)
  ·
    refine ⟨29329199264383990418589527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19552799509589326945726351 29329199264383990418589527)
    ·
      refine ⟨43993798896575985627884291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29329199264383990418589527 43993798896575985627884291)
      ·
        refine ⟨65990698344863978441826437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43993798896575985627884291 65990698344863978441826437)
        ·
          refine ⟨12373255939661995957842457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65990698344863978441826437 12373255939661995957842457)
          ·
            refine ⟨9279941954746496968381843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12373255939661995957842457 9279941954746496968381843)
            ·
              refine ⟨13919912932119745452572765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9279941954746496968381843 13919912932119745452572765)
              ·
                refine ⟨5219967349544904544714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13919912932119745452572765 5219967349544904544714787)
                ·
                  refine ⟨7829951024317356817072181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5219967349544904544714787 7829951024317356817072181)
                  ·
                    refine ⟨734057908529752201600517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7829951024317356817072181 734057908529752201600517)
                    ·
                      rfl

theorem cell23_4288718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_4288718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288718 prefixEnd_4288718 := by exact prefixLift 4288718
  have htrace : WordTrace (prefixWord ++ tailWord_4288718) baseStart_4288718 baseEnd_4288718 := by
    simpa [prefixWord, tailWord_4288718, baseEnd_4288718] using wordTrace_append hprefix tailTrace_4288718
  have hstable : (prefixWord ++ tailWord_4288718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288718).length < 2 ^ (prefixWord ++ tailWord_4288718).sum := by decide
  have hdescent : baseEnd_4288718 < baseStart_4288718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288741 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4288741 : Nat := 118140960795 + 4288741 * 2 ^ 59
def prefixEnd_4288741 : Nat := 4983230072969 + 3 ^ 40 * 4288741 * 2
def baseEnd_4288741 : Nat := 2202185535644310014813945

theorem tailTrace_4288741 : CollatzResearch.WordTrace tailWord_4288741 prefixEnd_4288741 2202185535644310014813945 := by
  unfold tailWord_4288741
  simp only [CollatzResearch.WordTrace]
  refine ⟨156423234955631290493898077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104282156637087526995932051 156423234955631290493898077)
  ·
    refine ⟨58658713108361733935211779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156423234955631290493898077 58658713108361733935211779)
    ·
      refine ⟨87988069662542600902817669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58658713108361733935211779 87988069662542600902817669)
      ·
        refine ⟨16497763061726737669278313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87988069662542600902817669 16497763061726737669278313)
        ·
          refine ⟨12373322296295053251958735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16497763061726737669278313 12373322296295053251958735)
          ·
            refine ⟨18559983444442579877938103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12373322296295053251958735 18559983444442579877938103)
            ·
              refine ⟨27839975166663869816907155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18559983444442579877938103 27839975166663869816907155)
              ·
                refine ⟨41759962749995804725360733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27839975166663869816907155 41759962749995804725360733)
                ·
                  refine ⟨15659986031248426772010275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41759962749995804725360733 15659986031248426772010275)
                  ·
                    refine ⟨23489979046872640158015413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15659986031248426772010275 23489979046872640158015413)
                    ·
                      refine ⟨2202185535644310014813945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23489979046872640158015413 2202185535644310014813945)
                      ·
                        rfl

theorem cell23_4288741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4288741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288741 prefixEnd_4288741 := by exact prefixLift 4288741
  have htrace : WordTrace (prefixWord ++ tailWord_4288741) baseStart_4288741 baseEnd_4288741 := by
    simpa [prefixWord, tailWord_4288741, baseEnd_4288741] using wordTrace_append hprefix tailTrace_4288741
  have hstable : (prefixWord ++ tailWord_4288741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288741).length < 2 ^ (prefixWord ++ tailWord_4288741).sum := by decide
  have hdescent : baseEnd_4288741 < baseStart_4288741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288751 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_4288751 : Nat := 118140960795 + 4288751 * 2 ^ 59
def prefixEnd_4288751 : Nat := 4983230072969 + 3 ^ 40 * 4288751 * 2
def baseEnd_4288751 : Nat := 2202190670450854975688899

theorem tailTrace_4288751 : CollatzResearch.WordTrace tailWord_4288751 prefixEnd_4288751 2202190670450854975688899 := by
  unfold tailWord_4288751
  simp only [CollatzResearch.WordTrace]
  refine ⟨156423599685595062201762107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104282399790396708134508071 156423599685595062201762107)
  ·
    refine ⟨234635399528392593302643161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156423599685595062201762107 234635399528392593302643161)
    ·
      refine ⟨175976549646294444976982371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234635399528392593302643161 175976549646294444976982371)
      ·
        refine ⟨263964824469441667465473557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175976549646294444976982371 263964824469441667465473557)
        ·
          refine ⟨12373351147005078162444073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 263964824469441667465473557 12373351147005078162444073)
          ·
            refine ⟨9280013360253808621833055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12373351147005078162444073 9280013360253808621833055)
            ·
              refine ⟨13920020040380712932749583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9280013360253808621833055 13920020040380712932749583)
              ·
                refine ⟨20880030060571069399124375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13920020040380712932749583 20880030060571069399124375)
                ·
                  refine ⟨31320045090856604098686563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20880030060571069399124375 31320045090856604098686563)
                  ·
                    refine ⟨46980067636284906148029845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31320045090856604098686563 46980067636284906148029845)
                    ·
                      refine ⟨2202190670450854975688899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46980067636284906148029845 2202190670450854975688899)
                      ·
                        rfl

theorem cell23_4288751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_4288751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288751 prefixEnd_4288751 := by exact prefixLift 4288751
  have htrace : WordTrace (prefixWord ++ tailWord_4288751) baseStart_4288751 baseEnd_4288751 := by
    simpa [prefixWord, tailWord_4288751, baseEnd_4288751] using wordTrace_append hprefix tailTrace_4288751
  have hstable : (prefixWord ++ tailWord_4288751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288751).length < 2 ^ (prefixWord ++ tailWord_4288751).sum := by decide
  have hdescent : baseEnd_4288751 < baseStart_4288751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288758 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4288758 : Nat := 118140960795 + 4288758 * 2 ^ 59
def prefixEnd_4288758 : Nat := 4983230072969 + 3 ^ 40 * 4288758 * 2
def baseEnd_4288758 : Nat := 2202194264815436448301367

theorem tailTrace_4288758 : CollatzResearch.WordTrace tailWord_4288758 prefixEnd_4288758 2202194264815436448301367 := by
  unfold tailWord_4288758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776490937285606399829183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104282569997713134931511285 9776490937285606399829183)
  ·
    refine ⟨14664736405928409599743775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776490937285606399829183 14664736405928409599743775)
    ·
      refine ⟨21997104608892614399615663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14664736405928409599743775 21997104608892614399615663)
      ·
        refine ⟨32995656913338921599423495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21997104608892614399615663 32995656913338921599423495)
        ·
          refine ⟨49493485370008382399135243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32995656913338921599423495 49493485370008382399135243)
          ·
            refine ⟨74240228055012573598702865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49493485370008382399135243 74240228055012573598702865)
            ·
              refine ⟨55680171041259430199027149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74240228055012573598702865 55680171041259430199027149)
              ·
                refine ⟨20880064140472286324635181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55680171041259430199027149 20880064140472286324635181)
                ·
                  refine ⟨7830024052677107371738193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20880064140472286324635181 7830024052677107371738193)
                  ·
                    refine ⟨5872518039507830528803645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830024052677107371738193 5872518039507830528803645)
                    ·
                      refine ⟨2202194264815436448301367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872518039507830528803645 2202194264815436448301367)
                      ·
                        rfl

theorem cell23_4288758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4288758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288758 prefixEnd_4288758 := by exact prefixLift 4288758
  have htrace : WordTrace (prefixWord ++ tailWord_4288758) baseStart_4288758 baseEnd_4288758 := by
    simpa [prefixWord, tailWord_4288758, baseEnd_4288758] using wordTrace_append hprefix tailTrace_4288758
  have hstable : (prefixWord ++ tailWord_4288758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288758).length < 2 ^ (prefixWord ++ tailWord_4288758).sum := by decide
  have hdescent : baseEnd_4288758 < baseStart_4288758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288771 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3]
def baseStart_4288771 : Nat := 118140960795 + 4288771 * 2 ^ 59
def prefixEnd_4288771 : Nat := 4983230072969 + 3 ^ 40 * 4288771 * 2
def baseEnd_4288771 : Nat := 2202200940063944897438807

theorem tailTrace_4288771 : CollatzResearch.WordTrace tailWord_4288771 prefixEnd_4288771 2202200940063944897438807 := by
  unfold tailWord_4288771
  simp only [CollatzResearch.WordTrace]
  refine ⟨156424329145522605617490167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104282886097015070411660111 156424329145522605617490167)
  ·
    refine ⟨234636493718283908426235251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156424329145522605617490167 234636493718283908426235251)
    ·
      refine ⟨351954740577425862639352877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234636493718283908426235251 351954740577425862639352877)
      ·
        refine ⟨131983027716534698489757329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351954740577425862639352877 131983027716534698489757329)
        ·
          refine ⟨98987270787401023867317997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131983027716534698489757329 98987270787401023867317997)
          ·
            refine ⟨37120226545275383950244249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98987270787401023867317997 37120226545275383950244249)
            ·
              refine ⟨27840169908956537962683187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37120226545275383950244249 27840169908956537962683187)
              ·
                refine ⟨41760254863434806944024781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27840169908956537962683187 41760254863434806944024781)
                ·
                  refine ⟨15660095573788052604009293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41760254863434806944024781 15660095573788052604009293)
                  ·
                    refine ⟨5872535840170519726503485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15660095573788052604009293 5872535840170519726503485)
                    ·
                      refine ⟨2202200940063944897438807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872535840170519726503485 2202200940063944897438807)
                      ·
                        rfl

theorem cell23_4288771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_4288771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288771 prefixEnd_4288771 := by exact prefixLift 4288771
  have htrace : WordTrace (prefixWord ++ tailWord_4288771) baseStart_4288771 baseEnd_4288771 := by
    simpa [prefixWord, tailWord_4288771, baseEnd_4288771] using wordTrace_append hprefix tailTrace_4288771
  have hstable : (prefixWord ++ tailWord_4288771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288771).length < 2 ^ (prefixWord ++ tailWord_4288771).sum := by decide
  have hdescent : baseEnd_4288771 < baseStart_4288771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288775 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4288775 : Nat := 118140960795 + 4288775 * 2 ^ 59
def prefixEnd_4288775 : Nat := 4983230072969 + 3 ^ 40 * 4288775 * 2
def baseEnd_4288775 : Nat := 2202202993986562881788789

theorem tailTrace_4288775 : CollatzResearch.WordTrace tailWord_4288775 prefixEnd_4288775 2202202993986562881788789 := by
  unfold tailWord_4288775
  simp only [CollatzResearch.WordTrace]
  refine ⟨156424475037508114300635779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104282983358338742867090519 156424475037508114300635779)
  ·
    refine ⟨234636712556262171450953669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156424475037508114300635779 234636712556262171450953669)
    ·
      refine ⟨43994383604299157147053813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234636712556262171450953669 43994383604299157147053813)
      ·
        refine ⟨4124473462903045982536295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43994383604299157147053813 4124473462903045982536295)
        ·
          refine ⟨6186710194354568973804443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124473462903045982536295 6186710194354568973804443)
          ·
            refine ⟨9280065291531853460706665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186710194354568973804443 9280065291531853460706665)
            ·
              refine ⟨6960048968648890095529999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9280065291531853460706665 6960048968648890095529999)
              ·
                refine ⟨10440073452973335143294999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960048968648890095529999 10440073452973335143294999)
                ·
                  refine ⟨15660110179460002714942499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10440073452973335143294999 15660110179460002714942499)
                  ·
                    refine ⟨23490165269190004072413749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15660110179460002714942499 23490165269190004072413749)
                    ·
                      refine ⟨2202202993986562881788789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23490165269190004072413749 2202202993986562881788789)
                      ·
                        rfl

theorem cell23_4288775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4288775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288775 prefixEnd_4288775 := by exact prefixLift 4288775
  have htrace : WordTrace (prefixWord ++ tailWord_4288775) baseStart_4288775 baseEnd_4288775 := by
    simpa [prefixWord, tailWord_4288775, baseEnd_4288775] using wordTrace_append hprefix tailTrace_4288775
  have hstable : (prefixWord ++ tailWord_4288775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288775).length < 2 ^ (prefixWord ++ tailWord_4288775).sum := by decide
  have hdescent : baseEnd_4288775 < baseStart_4288775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288815 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 1, 3, 2]
def baseStart_4288815 : Nat := 118140960795 + 4288815 * 2 ^ 59
def prefixEnd_4288815 : Nat := 4983230072969 + 3 ^ 40 * 4288815 * 2
def baseEnd_4288815 : Nat := 2202223533212742725288605

theorem tailTrace_4288815 : CollatzResearch.WordTrace tailWord_4288815 prefixEnd_4288815 2202223533212742725288605 := by
  unfold tailWord_4288815
  simp only [CollatzResearch.WordTrace]
  refine ⟨156425933957363201132091899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104283955971575467421394599 156425933957363201132091899)
  ·
    refine ⟨234638900936044801698137849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156425933957363201132091899 234638900936044801698137849)
    ·
      refine ⟨175979175702033601273603387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234638900936044801698137849 175979175702033601273603387)
      ·
        refine ⟨263968763553050401910405081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175979175702033601273603387 263968763553050401910405081)
        ·
          refine ⟨197976572664787801432803811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263968763553050401910405081 197976572664787801432803811)
          ·
            refine ⟨296964858997181702149205717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197976572664787801432803811 296964858997181702149205717)
            ·
              refine ⟨6960113882746446144122009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 296964858997181702149205717 6960113882746446144122009)
              ·
                refine ⟨5220085412059834608091507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6960113882746446144122009 5220085412059834608091507)
                ·
                  refine ⟨7830128118089751912137261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220085412059834608091507 7830128118089751912137261)
                  ·
                    refine ⟨2936298044283656967051473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7830128118089751912137261 2936298044283656967051473)
                    ·
                      refine ⟨2202223533212742725288605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936298044283656967051473 2202223533212742725288605)
                      ·
                        rfl

theorem cell23_4288815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3, 2].length) (baseStart_4288815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288815 prefixEnd_4288815 := by exact prefixLift 4288815
  have htrace : WordTrace (prefixWord ++ tailWord_4288815) baseStart_4288815 baseEnd_4288815 := by
    simpa [prefixWord, tailWord_4288815, baseEnd_4288815] using wordTrace_append hprefix tailTrace_4288815
  have hstable : (prefixWord ++ tailWord_4288815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288815).length < 2 ^ (prefixWord ++ tailWord_4288815).sum := by decide
  have hdescent : baseEnd_4288815 < baseStart_4288815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288831 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_4288831 : Nat := 118140960795 + 4288831 * 2 ^ 59
def prefixEnd_4288831 : Nat := 4983230072969 + 3 ^ 40 * 4288831 * 2
def baseEnd_4288831 : Nat := 2202231748903214662688531

theorem tailTrace_4288831 : CollatzResearch.WordTrace tailWord_4288831 prefixEnd_4288831 2202231748903214662688531 := by
  unfold tailWord_4288831
  simp only [CollatzResearch.WordTrace]
  refine ⟨156426517525305235864674347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104284345016870157243116231 156426517525305235864674347)
  ·
    refine ⟨234639776287957853797011521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156426517525305235864674347 234639776287957853797011521)
    ·
      refine ⟨175979832215968390347758641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234639776287957853797011521 175979832215968390347758641)
      ·
        refine ⟨131984874161976292760818981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175979832215968390347758641 131984874161976292760818981)
        ·
          refine ⟨24747163905370554892653559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131984874161976292760818981 24747163905370554892653559)
          ·
            refine ⟨37120745858055832338980339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24747163905370554892653559 37120745858055832338980339)
            ·
              refine ⟨55681118787083748508470509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37120745858055832338980339 55681118787083748508470509)
              ·
                refine ⟨20880419545156405690676441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55681118787083748508470509 20880419545156405690676441)
                ·
                  refine ⟨15660314658867304268007331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20880419545156405690676441 15660314658867304268007331)
                  ·
                    refine ⟨23490471988300956402010997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15660314658867304268007331 23490471988300956402010997)
                    ·
                      refine ⟨2202231748903214662688531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23490471988300956402010997 2202231748903214662688531)
                      ·
                        rfl

theorem cell23_4288831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_4288831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288831 prefixEnd_4288831 := by exact prefixLift 4288831
  have htrace : WordTrace (prefixWord ++ tailWord_4288831) baseStart_4288831 baseEnd_4288831 := by
    simpa [prefixWord, tailWord_4288831, baseEnd_4288831] using wordTrace_append hprefix tailTrace_4288831
  have hstable : (prefixWord ++ tailWord_4288831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288831).length < 2 ^ (prefixWord ++ tailWord_4288831).sum := by decide
  have hdescent : baseEnd_4288831 < baseStart_4288831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288841 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_4288841 : Nat := 118140960795 + 4288841 * 2 ^ 59
def prefixEnd_4288841 : Nat := 4983230072969 + 3 ^ 40 * 4288841 * 2
def baseEnd_4288841 : Nat := 2202236883709759623563485

theorem tailTrace_4288841 : CollatzResearch.WordTrace tailWord_4288841 prefixEnd_4288841 2202236883709759623563485 := by
  unfold tailWord_4288841
  simp only [CollatzResearch.WordTrace]
  refine ⟨156426882255269007572538377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104284588170179338381692251 156426882255269007572538377)
  ·
    refine ⟨117320161691451755679403783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156426882255269007572538377 117320161691451755679403783)
    ·
      refine ⟨175980242537177633519105675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117320161691451755679403783 175980242537177633519105675)
      ·
        refine ⟨263970363805766450278658513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175980242537177633519105675 263970363805766450278658513)
        ·
          refine ⟨197977772854324837708993885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263970363805766450278658513 197977772854324837708993885)
          ·
            refine ⟨74241664820371814140872707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197977772854324837708993885 74241664820371814140872707)
            ·
              refine ⟨111362497230557721211309061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74241664820371814140872707 111362497230557721211309061)
              ·
                refine ⟨20880468230729572727120449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111362497230557721211309061 20880468230729572727120449)
                ·
                  refine ⟨15660351173047179545340337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20880468230729572727120449 15660351173047179545340337)
                  ·
                    refine ⟨11745263379785384659005253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15660351173047179545340337 11745263379785384659005253)
                    ·
                      refine ⟨2202236883709759623563485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11745263379785384659005253 2202236883709759623563485)
                      ·
                        rfl

theorem cell23_4288841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_4288841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288841 prefixEnd_4288841 := by exact prefixLift 4288841
  have htrace : WordTrace (prefixWord ++ tailWord_4288841) baseStart_4288841 baseEnd_4288841 := by
    simpa [prefixWord, tailWord_4288841, baseEnd_4288841] using wordTrace_append hprefix tailTrace_4288841
  have hstable : (prefixWord ++ tailWord_4288841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288841).length < 2 ^ (prefixWord ++ tailWord_4288841).sum := by decide
  have hdescent : baseEnd_4288841 < baseStart_4288841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288885 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 5]
def baseStart_4288885 : Nat := 118140960795 + 4288885 * 2 ^ 59
def prefixEnd_4288885 : Nat := 4983230072969 + 3 ^ 40 * 4288885 * 2
def baseEnd_4288885 : Nat := 244695497428728605712587

theorem tailTrace_4288885 : CollatzResearch.WordTrace tailWord_4288885 prefixEnd_4288885 244695497428728605712587 := by
  unfold tailWord_4288885
  simp only [CollatzResearch.WordTrace]
  refine ⟨156428487067109603087140109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104285658044739735391426739 156428487067109603087140109)
  ·
    refine ⟨58660682650166101157677541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156428487067109603087140109 58660682650166101157677541)
    ·
      refine ⟨10998877996906143967064539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58660682650166101157677541 10998877996906143967064539)
      ·
        refine ⟨16498316995359215950596809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10998877996906143967064539 16498316995359215950596809)
        ·
          refine ⟨12373737746519411962947607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16498316995359215950596809 12373737746519411962947607)
          ·
            refine ⟨18560606619779117944421411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12373737746519411962947607 18560606619779117944421411)
            ·
              refine ⟨27840909929668676916632117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18560606619779117944421411 27840909929668676916632117)
              ·
                refine ⟨2610085305906438460934261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27840909929668676916632117 2610085305906438460934261)
                ·
                  refine ⟨244695497428728605712587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610085305906438460934261 244695497428728605712587)
                  ·
                    rfl

theorem cell23_4288885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_4288885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288885 prefixEnd_4288885 := by exact prefixLift 4288885
  have htrace : WordTrace (prefixWord ++ tailWord_4288885) baseStart_4288885 baseEnd_4288885 := by
    simpa [prefixWord, tailWord_4288885, baseEnd_4288885] using wordTrace_append hprefix tailTrace_4288885
  have hstable : (prefixWord ++ tailWord_4288885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288885).length < 2 ^ (prefixWord ++ tailWord_4288885).sum := by decide
  have hdescent : baseEnd_4288885 < baseStart_4288885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288958 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_4288958 : Nat := 118140960795 + 4288958 * 2 ^ 59
def prefixEnd_4288958 : Nat := 4983230072969 + 3 ^ 40 * 4288958 * 2
def baseEnd_4288958 : Nat := 244699662327370629533383

theorem tailTrace_4288958 : CollatzResearch.WordTrace tailWord_4288958 prefixEnd_4288958 244699662327370629533383 := by
  unfold tailWord_4288958
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553893699480642069318441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104287433063896757703031685 19553893699480642069318441)
  ·
    refine ⟨14665420274610481551988831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19553893699480642069318441 14665420274610481551988831)
    ·
      refine ⟨21998130411915722327983247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14665420274610481551988831 21998130411915722327983247)
      ·
        refine ⟨32997195617873583491974871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21998130411915722327983247 32997195617873583491974871)
        ·
          refine ⟨49495793426810375237962307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32997195617873583491974871 49495793426810375237962307)
          ·
            refine ⟨74243690140215562856943461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49495793426810375237962307 74243690140215562856943461)
            ·
              refine ⟨13920691901290418035676899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74243690140215562856943461 13920691901290418035676899)
              ·
                refine ⟨20881037851935627053515349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13920691901290418035676899 20881037851935627053515349)
                ·
                  refine ⟨244699662327370629533383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20881037851935627053515349 244699662327370629533383)
                  ·
                    rfl

theorem cell23_4288958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_4288958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288958 prefixEnd_4288958 := by exact prefixLift 4288958
  have htrace : WordTrace (prefixWord ++ tailWord_4288958) baseStart_4288958 baseEnd_4288958 := by
    simpa [prefixWord, tailWord_4288958, baseEnd_4288958] using wordTrace_append hprefix tailTrace_4288958
  have hstable : (prefixWord ++ tailWord_4288958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288958).length < 2 ^ (prefixWord ++ tailWord_4288958).sum := by decide
  have hdescent : baseEnd_4288958 < baseStart_4288958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288971 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 9]
def baseStart_4288971 : Nat := 118140960795 + 4288971 * 2 ^ 59
def prefixEnd_4288971 : Nat := 4983230072969 + 3 ^ 40 * 4288971 * 2
def baseEnd_4288971 : Nat := 734101212064948038312629

theorem tailTrace_4288971 : CollatzResearch.WordTrace tailWord_4288971 prefixEnd_4288971 734101212064948038312629 := by
  unfold tailWord_4288971
  simp only [CollatzResearch.WordTrace]
  refine ⟨156431623744798039774770767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104287749163198693183180511 156431623744798039774770767)
  ·
    refine ⟨234647435617197059662156151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156431623744798039774770767 234647435617197059662156151)
    ·
      refine ⟨351971153425795589493234227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234647435617197059662156151 351971153425795589493234227)
      ·
        refine ⟨527956730138693384239851341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351971153425795589493234227 527956730138693384239851341)
        ·
          refine ⟨197983773802010019089944253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527956730138693384239851341 197983773802010019089944253)
          ·
            refine ⟨74243915175753757158729095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197983773802010019089944253 74243915175753757158729095)
            ·
              refine ⟨111365872763630635738093643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74243915175753757158729095 111365872763630635738093643)
              ·
                refine ⟨167048809145445953607140465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111365872763630635738093643 167048809145445953607140465)
                ·
                  refine ⟨125286606859084465205355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167048809145445953607140465 125286606859084465205355349)
                  ·
                    refine ⟨734101212064948038312629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125286606859084465205355349 734101212064948038312629)
                    ·
                      rfl

theorem cell23_4288971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_4288971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288971 prefixEnd_4288971 := by exact prefixLift 4288971
  have htrace : WordTrace (prefixWord ++ tailWord_4288971) baseStart_4288971 baseEnd_4288971 := by
    simpa [prefixWord, tailWord_4288971, baseEnd_4288971] using wordTrace_append hprefix tailTrace_4288971
  have hstable : (prefixWord ++ tailWord_4288971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288971).length < 2 ^ (prefixWord ++ tailWord_4288971).sum := by decide
  have hdescent : baseEnd_4288971 < baseStart_4288971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4288985 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_4288985 : Nat := 118140960795 + 4288985 * 2 ^ 59
def prefixEnd_4288985 : Nat := 4983230072969 + 3 ^ 40 * 4288985 * 2
def baseEnd_4288985 : Nat := 2202310824924007060162823

theorem tailTrace_4288985 : CollatzResearch.WordTrace tailWord_4288985 prefixEnd_4288985 2202310824924007060162823 := by
  unfold tailWord_4288985
  simp only [CollatzResearch.WordTrace]
  refine ⟨156432134366747320165780409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104288089577831546777186939 156432134366747320165780409)
  ·
    refine ⟨117324100775060490124335307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156432134366747320165780409 117324100775060490124335307)
    ·
      refine ⟨175986151162590735186502961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117324100775060490124335307 175986151162590735186502961)
      ·
        refine ⟨131989613371943051389877221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175986151162590735186502961 131989613371943051389877221)
        ·
          refine ⟨24748052507239322135601979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131989613371943051389877221 24748052507239322135601979)
          ·
            refine ⟨37122078760858983203402969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24748052507239322135601979 37122078760858983203402969)
            ·
              refine ⟨27841559070644237402552227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37122078760858983203402969 27841559070644237402552227)
              ·
                refine ⟨41762338605966356103828341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27841559070644237402552227 41762338605966356103828341)
                ·
                  refine ⟨3915219244309345884733907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41762338605966356103828341 3915219244309345884733907)
                  ·
                    refine ⟨5872828866464018827100861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915219244309345884733907 5872828866464018827100861)
                    ·
                      refine ⟨2202310824924007060162823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872828866464018827100861 2202310824924007060162823)
                      ·
                        rfl

theorem cell23_4288985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_4288985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4288985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4288985 prefixEnd_4288985 := by exact prefixLift 4288985
  have htrace : WordTrace (prefixWord ++ tailWord_4288985) baseStart_4288985 baseEnd_4288985 := by
    simpa [prefixWord, tailWord_4288985, baseEnd_4288985] using wordTrace_append hprefix tailTrace_4288985
  have hstable : (prefixWord ++ tailWord_4288985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4288985).length < 2 ^ (prefixWord ++ tailWord_4288985).sum := by decide
  have hdescent : baseEnd_4288985 < baseStart_4288985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4288985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289013 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4289013 : Nat := 118140960795 + 4289013 * 2 ^ 59
def prefixEnd_4289013 : Nat := 4983230072969 + 3 ^ 40 * 4289013 * 2
def baseEnd_4289013 : Nat := 734108400794110983537565

theorem tailTrace_4289013 : CollatzResearch.WordTrace tailWord_4289013 prefixEnd_4289013 734108400794110983537565 := by
  unfold tailWord_4289013
  simp only [CollatzResearch.WordTrace]
  refine ⟨156433155610645880947799693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104288770407097253965199795 156433155610645880947799693)
  ·
    refine ⟨58662433353992205355424885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156433155610645880947799693 58662433353992205355424885)
    ·
      refine ⟨5499603126936769252071083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58662433353992205355424885 5499603126936769252071083)
      ·
        refine ⟨8249404690405153878106625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499603126936769252071083 8249404690405153878106625)
        ·
          refine ⟨6187053517803865408579969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8249404690405153878106625 6187053517803865408579969)
          ·
            refine ⟨4640290138352899056434977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6187053517803865408579969 4640290138352899056434977)
            ·
              refine ⟨3480217603764674292326233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640290138352899056434977 3480217603764674292326233)
              ·
                refine ⟨2610163202823505719244675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3480217603764674292326233 2610163202823505719244675)
                ·
                  refine ⟨3915244804235258578867013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610163202823505719244675 3915244804235258578867013)
                  ·
                    refine ⟨734108400794110983537565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3915244804235258578867013 734108400794110983537565)
                    ·
                      rfl

theorem cell23_4289013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4289013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289013 prefixEnd_4289013 := by exact prefixLift 4289013
  have htrace : WordTrace (prefixWord ++ tailWord_4289013) baseStart_4289013 baseEnd_4289013 := by
    simpa [prefixWord, tailWord_4289013, baseEnd_4289013] using wordTrace_append hprefix tailTrace_4289013
  have hstable : (prefixWord ++ tailWord_4289013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289013).length < 2 ^ (prefixWord ++ tailWord_4289013).sum := by decide
  have hdescent : baseEnd_4289013 < baseStart_4289013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289025 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4289025 : Nat := 118140960795 + 4289025 * 2 ^ 59
def prefixEnd_4289025 : Nat := 4983230072969 + 3 ^ 40 * 4289025 * 2
def baseEnd_4289025 : Nat := 2202331364150186903662639

theorem tailTrace_4289025 : CollatzResearch.WordTrace tailWord_4289025 prefixEnd_4289025 2202331364150186903662639 := by
  unfold tailWord_4289025
  simp only [CollatzResearch.WordTrace]
  refine ⟨156433593286602406997236529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104289062191068271331491019 156433593286602406997236529)
  ·
    refine ⟨117325194964951805247927397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156433593286602406997236529 117325194964951805247927397)
    ·
      refine ⟨21998474055928463483986387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117325194964951805247927397 21998474055928463483986387)
      ·
        refine ⟨32997711083892695225979581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21998474055928463483986387 32997711083892695225979581)
        ·
          refine ⟨12374141656459760709742343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32997711083892695225979581 12374141656459760709742343)
          ·
            refine ⟨18561212484689641064613515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12374141656459760709742343 18561212484689641064613515)
            ·
              refine ⟨27841818727034461596920273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18561212484689641064613515 27841818727034461596920273)
              ·
                refine ⟨20881364045275846197690205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27841818727034461596920273 20881364045275846197690205)
                ·
                  refine ⟨7830511516978442324133827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20881364045275846197690205 7830511516978442324133827)
                  ·
                    refine ⟨11745767275467663486200741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7830511516978442324133827 11745767275467663486200741)
                    ·
                      refine ⟨2202331364150186903662639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11745767275467663486200741 2202331364150186903662639)
                      ·
                        rfl

theorem cell23_4289025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4289025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289025 prefixEnd_4289025 := by exact prefixLift 4289025
  have htrace : WordTrace (prefixWord ++ tailWord_4289025) baseStart_4289025 baseEnd_4289025 := by
    simpa [prefixWord, tailWord_4289025, baseEnd_4289025] using wordTrace_append hprefix tailTrace_4289025
  have hstable : (prefixWord ++ tailWord_4289025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289025).length < 2 ^ (prefixWord ++ tailWord_4289025).sum := by decide
  have hdescent : baseEnd_4289025 < baseStart_4289025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289035 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 6]
def baseStart_4289035 : Nat := 118140960795 + 4289035 * 2 ^ 59
def prefixEnd_4289035 : Nat := 4983230072969 + 3 ^ 40 * 4289035 * 2
def baseEnd_4289035 : Nat := 734112166318910621512531

theorem tailTrace_4289035 : CollatzResearch.WordTrace tailWord_4289035 prefixEnd_4289035 734112166318910621512531 := by
  unfold tailWord_4289035
  simp only [CollatzResearch.WordTrace]
  refine ⟨156433958016566178705100559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104289305344377452470067039 156433958016566178705100559)
  ·
    refine ⟨234650937024849268057650839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156433958016566178705100559 234650937024849268057650839)
    ·
      refine ⟨351976405537273902086476259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234650937024849268057650839 351976405537273902086476259)
      ·
        refine ⟨527964608305910853129714389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351976405537273902086476259 527964608305910853129714389)
        ·
          refine ⟨12374170507169785620227681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 527964608305910853129714389 12374170507169785620227681)
          ·
            refine ⟨9280627880377339215170761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12374170507169785620227681 9280627880377339215170761)
            ·
              refine ⟨6960470910283004411378071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9280627880377339215170761 6960470910283004411378071)
              ·
                refine ⟨10440706365424506617067107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960470910283004411378071 10440706365424506617067107)
                ·
                  refine ⟨15661059548136759925600661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10440706365424506617067107 15661059548136759925600661)
                  ·
                    refine ⟨734112166318910621512531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15661059548136759925600661 734112166318910621512531)
                    ·
                      rfl

theorem cell23_4289035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].length) (baseStart_4289035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289035 prefixEnd_4289035 := by exact prefixLift 4289035
  have htrace : WordTrace (prefixWord ++ tailWord_4289035) baseStart_4289035 baseEnd_4289035 := by
    simpa [prefixWord, tailWord_4289035, baseEnd_4289035] using wordTrace_append hprefix tailTrace_4289035
  have hstable : (prefixWord ++ tailWord_4289035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289035).length < 2 ^ (prefixWord ++ tailWord_4289035).sum := by decide
  have hdescent : baseEnd_4289035 < baseStart_4289035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289045 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_4289045 : Nat := 118140960795 + 4289045 * 2 ^ 59
def prefixEnd_4289045 : Nat := 4983230072969 + 3 ^ 40 * 4289045 * 2
def baseEnd_4289045 : Nat := 2202341633763276825412547

theorem tailTrace_4289045 : CollatzResearch.WordTrace tailWord_4289045 prefixEnd_4289045 2202341633763276825412547 := by
  unfold tailWord_4289045
  simp only [CollatzResearch.WordTrace]
  refine ⟨156434322746529950412964589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104289548497686633608643059 156434322746529950412964589)
  ·
    refine ⟨58662871029948731404861721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156434322746529950412964589 58662871029948731404861721)
    ·
      refine ⟨43997153272461548553646291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58662871029948731404861721 43997153272461548553646291)
      ·
        refine ⟨65995729908692322830469437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43997153272461548553646291 65995729908692322830469437)
        ·
          refine ⟨24748398715759621061426039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65995729908692322830469437 24748398715759621061426039)
          ·
            refine ⟨37122598073639431592139059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24748398715759621061426039 37122598073639431592139059)
            ·
              refine ⟨55683897110459147388208589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37122598073639431592139059 55683897110459147388208589)
              ·
                refine ⟨20881461416422180270578221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55683897110459147388208589 20881461416422180270578221)
                ·
                  refine ⟨7830548031158317601466833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20881461416422180270578221 7830548031158317601466833)
                  ·
                    refine ⟨5872911023368738201100125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830548031158317601466833 5872911023368738201100125)
                    ·
                      refine ⟨2202341633763276825412547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5872911023368738201100125 2202341633763276825412547)
                      ·
                        rfl

theorem cell23_4289045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_4289045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289045 prefixEnd_4289045 := by exact prefixLift 4289045
  have htrace : WordTrace (prefixWord ++ tailWord_4289045) baseStart_4289045 baseEnd_4289045 := by
    simpa [prefixWord, tailWord_4289045, baseEnd_4289045] using wordTrace_append hprefix tailTrace_4289045
  have hstable : (prefixWord ++ tailWord_4289045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289045).length < 2 ^ (prefixWord ++ tailWord_4289045).sum := by decide
  have hdescent : baseEnd_4289045 < baseStart_4289045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289056 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_4289056 : Nat := 118140960795 + 4289056 * 2 ^ 59
def prefixEnd_4289056 : Nat := 4983230072969 + 3 ^ 40 * 4289056 * 2
def baseEnd_4289056 : Nat := 734115760683492094124999

theorem tailTrace_4289056 : CollatzResearch.WordTrace tailWord_4289056 prefixEnd_4289056 734115760683492094124999 := by
  unfold tailWord_4289056
  simp only [CollatzResearch.WordTrace]
  refine ⟨78217361974745049645807511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104289815966326732861076681 78217361974745049645807511)
  ·
    refine ⟨117326042962117574468711267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78217361974745049645807511 117326042962117574468711267)
    ·
      refine ⟨175989064443176361703066901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117326042962117574468711267 175989064443176361703066901)
      ·
        refine ⟨8249487395773891954831261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175989064443176361703066901 8249487395773891954831261)
        ·
          refine ⟨3093557773415209483061723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8249487395773891954831261 3093557773415209483061723)
          ·
            refine ⟨4640336660122814224592585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093557773415209483061723 4640336660122814224592585)
            ·
              refine ⟨3480252495092110668444439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640336660122814224592585 3480252495092110668444439)
              ·
                refine ⟨5220378742638166002666659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480252495092110668444439 5220378742638166002666659)
                ·
                  refine ⟨7830568113957249003999989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220378742638166002666659 7830568113957249003999989)
                  ·
                    refine ⟨734115760683492094124999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7830568113957249003999989 734115760683492094124999)
                    ·
                      rfl

theorem cell23_4289056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_4289056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289056 prefixEnd_4289056 := by exact prefixLift 4289056
  have htrace : WordTrace (prefixWord ++ tailWord_4289056) baseStart_4289056 baseEnd_4289056 := by
    simpa [prefixWord, tailWord_4289056, baseEnd_4289056] using wordTrace_append hprefix tailTrace_4289056
  have hstable : (prefixWord ++ tailWord_4289056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289056).length < 2 ^ (prefixWord ++ tailWord_4289056).sum := by decide
  have hdescent : baseEnd_4289056 < baseStart_4289056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289059 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 1, 1, 4]
def baseStart_4289059 : Nat := 118140960795 + 4289059 * 2 ^ 59
def prefixEnd_4289059 : Nat := 4983230072969 + 3 ^ 40 * 4289059 * 2
def baseEnd_4289059 : Nat := 2202348822492439770637483

theorem tailTrace_4289059 : CollatzResearch.WordTrace tailWord_4289059 prefixEnd_4289059 2202348822492439770637483 := by
  unfold tailWord_4289059
  simp only [CollatzResearch.WordTrace]
  refine ⟨156434833368479230803974231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104289888912319487202649487 156434833368479230803974231)
  ·
    refine ⟨234652250052718846205961347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156434833368479230803974231 234652250052718846205961347)
    ·
      refine ⟨351978375079078269308942021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234652250052718846205961347 351978375079078269308942021)
      ·
        refine ⟨65995945327327175495426629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 351978375079078269308942021 65995945327327175495426629)
        ·
          refine ⟨12374239748873845405392493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65995945327327175495426629 12374239748873845405392493)
          ·
            refine ⟨4640339905827692027022185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12374239748873845405392493 4640339905827692027022185)
            ·
              refine ⟨3480254929370769020266639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640339905827692027022185 3480254929370769020266639)
              ·
                refine ⟨5220382394056153530399959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480254929370769020266639 5220382394056153530399959)
                ·
                  refine ⟨7830573591084230295599939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220382394056153530399959 7830573591084230295599939)
                  ·
                    refine ⟨11745860386626345443399909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7830573591084230295599939 11745860386626345443399909)
                    ·
                      refine ⟨2202348822492439770637483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11745860386626345443399909 2202348822492439770637483)
                      ·
                        rfl

theorem cell23_4289059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_4289059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289059 prefixEnd_4289059 := by exact prefixLift 4289059
  have htrace : WordTrace (prefixWord ++ tailWord_4289059) baseStart_4289059 baseEnd_4289059 := by
    simpa [prefixWord, tailWord_4289059, baseEnd_4289059] using wordTrace_append hprefix tailTrace_4289059
  have hstable : (prefixWord ++ tailWord_4289059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289059).length < 2 ^ (prefixWord ++ tailWord_4289059).sum := by decide
  have hdescent : baseEnd_4289059 < baseStart_4289059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289086 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_4289086 : Nat := 118140960795 + 4289086 * 2 ^ 59
def prefixEnd_4289086 : Nat := 4983230072969 + 3 ^ 40 * 4289086 * 2
def baseEnd_4289086 : Nat := 734120895490037054999953

theorem tailTrace_4289086 : CollatzResearch.WordTrace tailWord_4289086 prefixEnd_4289086 734120895490037054999953 := by
  unfold tailWord_4289086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554477267422676801900889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104290545426254276276804741 19554477267422676801900889)
  ·
    refine ⟨14665857950567007601425667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19554477267422676801900889 14665857950567007601425667)
    ·
      refine ⟨21998786925850511402138501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14665857950567007601425667 21998786925850511402138501)
      ·
        refine ⟨4124772548596970887900969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21998786925850511402138501 4124772548596970887900969)
        ·
          refine ⟨3093579411447728165925727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4124772548596970887900969 3093579411447728165925727)
          ·
            refine ⟨4640369117171592248888591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093579411447728165925727 4640369117171592248888591)
            ·
              refine ⟨6960553675757388373332887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640369117171592248888591 6960553675757388373332887)
              ·
                refine ⟨10440830513636082559999331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960553675757388373332887 10440830513636082559999331)
                ·
                  refine ⟨15661245770454123839998997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10440830513636082559999331 15661245770454123839998997)
                  ·
                    refine ⟨734120895490037054999953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15661245770454123839998997 734120895490037054999953)
                    ·
                      rfl

theorem cell23_4289086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_4289086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289086 prefixEnd_4289086 := by exact prefixLift 4289086
  have htrace : WordTrace (prefixWord ++ tailWord_4289086) baseStart_4289086 baseEnd_4289086 := by
    simpa [prefixWord, tailWord_4289086, baseEnd_4289086] using wordTrace_append hprefix tailTrace_4289086
  have hstable : (prefixWord ++ tailWord_4289086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289086).length < 2 ^ (prefixWord ++ tailWord_4289086).sum := by decide
  have hdescent : baseEnd_4289086 < baseStart_4289086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289102 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_4289102 : Nat := 118140960795 + 4289102 * 2 ^ 59
def prefixEnd_4289102 : Nat := 4983230072969 + 3 ^ 40 * 4289102 * 2
def baseEnd_4289102 : Nat := 2202370902160583102399785

theorem tailTrace_4289102 : CollatzResearch.WordTrace tailWord_4289102 prefixEnd_4289102 2202370902160583102399785 := by
  unfold tailWord_4289102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554550213415431143473695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104290934471548966098526373 19554550213415431143473695)
  ·
    refine ⟨29331825320123146715210543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19554550213415431143473695 29331825320123146715210543)
    ·
      refine ⟨43997737980184720072815815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29331825320123146715210543 43997737980184720072815815)
      ·
        refine ⟨65996606970277080109223723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43997737980184720072815815 65996606970277080109223723)
        ·
          refine ⟨98994910455415620163835585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65996606970277080109223723 98994910455415620163835585)
          ·
            refine ⟨74246182841561715122876689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98994910455415620163835585 74246182841561715122876689)
            ·
              refine ⟨55684637131171286342157517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74246182841561715122876689 55684637131171286342157517)
              ·
                refine ⟨20881738924189232378309069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55684637131171286342157517 20881738924189232378309069)
                ·
                  refine ⟨7830652096570962141865901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20881738924189232378309069 7830652096570962141865901)
                  ·
                    refine ⟨2936494536214110803199713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7830652096570962141865901 2936494536214110803199713)
                    ·
                      refine ⟨2202370902160583102399785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936494536214110803199713 2202370902160583102399785)
                      ·
                        rfl

theorem cell23_4289102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_4289102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289102 prefixEnd_4289102 := by exact prefixLift 4289102
  have htrace : WordTrace (prefixWord ++ tailWord_4289102) baseStart_4289102 baseEnd_4289102 := by
    simpa [prefixWord, tailWord_4289102, baseEnd_4289102] using wordTrace_append hprefix tailTrace_4289102
  have hstable : (prefixWord ++ tailWord_4289102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289102).length < 2 ^ (prefixWord ++ tailWord_4289102).sum := by decide
  have hdescent : baseEnd_4289102 < baseStart_4289102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289242 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_4289242 : Nat := 118140960795 + 4289242 * 2 ^ 59
def prefixEnd_4289242 : Nat := 4983230072969 + 3 ^ 40 * 4289242 * 2
def baseEnd_4289242 : Nat := 2202442789452212554649141

theorem tailTrace_4289242 : CollatzResearch.WordTrace tailWord_4289242 prefixEnd_4289242 2202442789452212554649141 := by
  unfold tailWord_4289242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39110376981704063264471495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104294338617877502038590653 39110376981704063264471495)
  ·
    refine ⟨58665565472556094896707243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39110376981704063264471495 58665565472556094896707243)
    ·
      refine ⟨87998348208834142345060865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58665565472556094896707243 87998348208834142345060865)
      ·
        refine ⟨65998761156625606758795649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87998348208834142345060865 65998761156625606758795649)
        ·
          refine ⟨49499070867469205069096737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65998761156625606758795649 49499070867469205069096737)
          ·
            refine ⟨37124303150601903801822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49499070867469205069096737 37124303150601903801822553)
            ·
              refine ⟨27843227362951427851366915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37124303150601903801822553 27843227362951427851366915)
              ·
                refine ⟨41764841044427141777050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27843227362951427851366915 41764841044427141777050373)
                ·
                  refine ⟨7830907695830089083196945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41764841044427141777050373 7830907695830089083196945)
                  ·
                    refine ⟨5873180771872566812397709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830907695830089083196945 5873180771872566812397709)
                    ·
                      refine ⟨2202442789452212554649141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873180771872566812397709 2202442789452212554649141)
                      ·
                        rfl

theorem cell23_4289242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_4289242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289242 prefixEnd_4289242 := by exact prefixLift 4289242
  have htrace : WordTrace (prefixWord ++ tailWord_4289242) baseStart_4289242 baseEnd_4289242 := by
    simpa [prefixWord, tailWord_4289242, baseEnd_4289242] using wordTrace_append hprefix tailTrace_4289242
  have hstable : (prefixWord ++ tailWord_4289242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289242).length < 2 ^ (prefixWord ++ tailWord_4289242).sum := by decide
  have hdescent : baseEnd_4289242 < baseStart_4289242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289249 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_4289249 : Nat := 118140960795 + 4289249 * 2 ^ 59
def prefixEnd_4289249 : Nat := 4983230072969 + 3 ^ 40 * 4289249 * 2
def baseEnd_4289249 : Nat := 734148794605598009087203

theorem tailTrace_4289249 : CollatzResearch.WordTrace tailWord_4289249 prefixEnd_4289249 734148794605598009087203 := by
  unfold tailWord_4289249
  simp only [CollatzResearch.WordTrace]
  refine ⟨156441763237790893253390801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104294508825193928835593867 156441763237790893253390801)
  ·
    refine ⟨117331322428343169940043101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156441763237790893253390801 117331322428343169940043101)
    ·
      refine ⟨43999245910628688727516163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117331322428343169940043101 43999245910628688727516163)
      ·
        refine ⟨65998868865943033091274245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43999245910628688727516163 65998868865943033091274245)
        ·
          refine ⟨12374787912364318704613921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65998868865943033091274245 12374787912364318704613921)
          ·
            refine ⟨9281090934273239028460441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12374787912364318704613921 9281090934273239028460441)
            ·
              refine ⟨6960818200704929271345331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281090934273239028460441 6960818200704929271345331)
              ·
                refine ⟨10441227301057393907017997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960818200704929271345331 10441227301057393907017997)
                ·
                  refine ⟨3915460237896522715131749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10441227301057393907017997 3915460237896522715131749)
                  ·
                    refine ⟨734148794605598009087203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3915460237896522715131749 734148794605598009087203)
                    ·
                      rfl

theorem cell23_4289249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_4289249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289249 prefixEnd_4289249 := by exact prefixLift 4289249
  have htrace : WordTrace (prefixWord ++ tailWord_4289249) baseStart_4289249 baseEnd_4289249 := by
    simpa [prefixWord, tailWord_4289249, baseEnd_4289249] using wordTrace_append hprefix tailTrace_4289249
  have hstable : (prefixWord ++ tailWord_4289249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289249).length < 2 ^ (prefixWord ++ tailWord_4289249).sum := by decide
  have hdescent : baseEnd_4289249 < baseStart_4289249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289265 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_4289265 : Nat := 118140960795 + 4289265 * 2 ^ 59
def prefixEnd_4289265 : Nat := 4983230072969 + 3 ^ 40 * 4289265 * 2
def baseEnd_4289265 : Nat := 2202454599507265964661535

theorem tailTrace_4289265 : CollatzResearch.WordTrace tailWord_4289265 prefixEnd_4289265 2202454599507265964661535 := by
  unfold tailWord_4289265
  simp only [CollatzResearch.WordTrace]
  refine ⟨156442346805732927985973249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104294897870488618657315499 156442346805732927985973249)
  ·
    refine ⟨117331760104299695989479937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156442346805732927985973249 117331760104299695989479937)
    ·
      refine ⟨87998820078224771992109953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117331760104299695989479937 87998820078224771992109953)
      ·
        refine ⟨65999115058668578994082465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87998820078224771992109953 65999115058668578994082465)
        ·
          refine ⟨49499336294001434245561849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65999115058668578994082465 49499336294001434245561849)
          ·
            refine ⟨37124502220501075684171387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49499336294001434245561849 37124502220501075684171387)
            ·
              refine ⟨55686753330751613526257081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37124502220501075684171387 55686753330751613526257081)
              ·
                refine ⟨41765064998063710144692811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55686753330751613526257081 41765064998063710144692811)
                ·
                  refine ⟨62647597497095565217039217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41765064998063710144692811 62647597497095565217039217)
                  ·
                    refine ⟨46985698122821673912779413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62647597497095565217039217 46985698122821673912779413)
                    ·
                      refine ⟨2202454599507265964661535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46985698122821673912779413 2202454599507265964661535)
                      ·
                        rfl

theorem cell23_4289265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_4289265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289265 prefixEnd_4289265 := by exact prefixLift 4289265
  have htrace : WordTrace (prefixWord ++ tailWord_4289265) baseStart_4289265 baseEnd_4289265 := by
    simpa [prefixWord, tailWord_4289265, baseEnd_4289265] using wordTrace_append hprefix tailTrace_4289265
  have hstable : (prefixWord ++ tailWord_4289265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289265).length < 2 ^ (prefixWord ++ tailWord_4289265).sum := by decide
  have hdescent : baseEnd_4289265 < baseStart_4289265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289275 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 7, 5]
def baseStart_4289275 : Nat := 118140960795 + 4289275 * 2 ^ 59
def prefixEnd_4289275 : Nat := 4983230072969 + 3 ^ 40 * 4289275 * 2
def baseEnd_4289275 : Nat := 734153244771270308512163

theorem tailTrace_4289275 : CollatzResearch.WordTrace tailWord_4289275 prefixEnd_4289275 734153244771270308512163 := by
  unfold tailWord_4289275
  simp only [CollatzResearch.WordTrace]
  refine ⟨156442711535696699693837279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104295141023797799795891519 156442711535696699693837279)
  ·
    refine ⟨234664067303545049540755919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156442711535696699693837279 234664067303545049540755919)
    ·
      refine ⟨351996100955317574311133879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234664067303545049540755919 351996100955317574311133879)
      ·
        refine ⟨527994151432976361466700819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351996100955317574311133879 527994151432976361466700819)
        ·
          refine ⟨791991227149464542200051229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527994151432976361466700819 791991227149464542200051229)
          ·
            refine ⟨296996710181049203325019211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791991227149464542200051229 296996710181049203325019211)
            ·
              refine ⟨445495065271573804987528817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296996710181049203325019211 445495065271573804987528817)
              ·
                refine ⟨334121298953680353740646613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445495065271573804987528817 334121298953680353740646613)
                ·
                  refine ⟨7830967944226883290796405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 334121298953680353740646613 7830967944226883290796405)
                  ·
                    refine ⟨734153244771270308512163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7830967944226883290796405 734153244771270308512163)
                    ·
                      rfl

theorem cell23_4289275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].length) (baseStart_4289275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289275 prefixEnd_4289275 := by exact prefixLift 4289275
  have htrace : WordTrace (prefixWord ++ tailWord_4289275) baseStart_4289275 baseEnd_4289275 := by
    simpa [prefixWord, tailWord_4289275, baseEnd_4289275] using wordTrace_append hprefix tailTrace_4289275
  have hstable : (prefixWord ++ tailWord_4289275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289275).length < 2 ^ (prefixWord ++ tailWord_4289275).sum := by decide
  have hdescent : baseEnd_4289275 < baseStart_4289275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289299 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 2, 3, 2]
def baseStart_4289299 : Nat := 118140960795 + 4289299 * 2 ^ 59
def prefixEnd_4289299 : Nat := 4983230072969 + 3 ^ 40 * 4289299 * 2
def baseEnd_4289299 : Nat := 2202472057849518831636379

theorem tailTrace_4289299 : CollatzResearch.WordTrace tailWord_4289299 prefixEnd_4289299 2202472057849518831636379 := by
  unfold tailWord_4289299
  simp only [CollatzResearch.WordTrace]
  refine ⟨156443586887609751792710951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104295724591739834528473967 156443586887609751792710951)
  ·
    refine ⟨234665380331414627689066427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156443586887609751792710951 234665380331414627689066427)
    ·
      refine ⟨351998070497121941533599641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234665380331414627689066427 351998070497121941533599641)
      ·
        refine ⟨263998552872841456150199731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351998070497121941533599641 263998552872841456150199731)
        ·
          refine ⟨395997829309262184225299597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263998552872841456150199731 395997829309262184225299597)
          ·
            refine ⟨148499185990973319084487349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395997829309262184225299597 148499185990973319084487349)
            ·
              refine ⟨13921798686653748664170689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148499185990973319084487349 13921798686653748664170689)
              ·
                refine ⟨10441349014990311498128017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13921798686653748664170689 10441349014990311498128017)
                ·
                  refine ⟨7831011761242733623596013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10441349014990311498128017 7831011761242733623596013)
                  ·
                    refine ⟨2936629410466025108848505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7831011761242733623596013 2936629410466025108848505)
                    ·
                      refine ⟨2202472057849518831636379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936629410466025108848505 2202472057849518831636379)
                      ·
                        rfl

theorem cell23_4289299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3, 2].length) (baseStart_4289299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289299 prefixEnd_4289299 := by exact prefixLift 4289299
  have htrace : WordTrace (prefixWord ++ tailWord_4289299) baseStart_4289299 baseEnd_4289299 := by
    simpa [prefixWord, tailWord_4289299, baseEnd_4289299] using wordTrace_append hprefix tailTrace_4289299
  have hstable : (prefixWord ++ tailWord_4289299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289299).length < 2 ^ (prefixWord ++ tailWord_4289299).sum := by decide
  have hdescent : baseEnd_4289299 < baseStart_4289299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289305 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_4289305 : Nat := 118140960795 + 4289305 * 2 ^ 59
def prefixEnd_4289305 : Nat := 4983230072969 + 3 ^ 40 * 4289305 * 2
def baseEnd_4289305 : Nat := 734158379577815269387117

theorem tailTrace_4289305 : CollatzResearch.WordTrace tailWord_4289305 prefixEnd_4289305 734158379577815269387117 := by
  unfold tailWord_4289305
  simp only [CollatzResearch.WordTrace]
  refine ⟨156443805725588014817429369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104295870483725343211619579 156443805725588014817429369)
  ·
    refine ⟨117332854294191011113072027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156443805725588014817429369 117332854294191011113072027)
    ·
      refine ⟨175999281441286516669608041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117332854294191011113072027 175999281441286516669608041)
      ·
        refine ⟨131999461080964887502206031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175999281441286516669608041 131999461080964887502206031)
        ·
          refine ⟨197999191621447331253309047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131999461080964887502206031 197999191621447331253309047)
          ·
            refine ⟨296998787432170996879963571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197999191621447331253309047 296998787432170996879963571)
            ·
              refine ⟨445498181148256495319945357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296998787432170996879963571 445498181148256495319945357)
              ·
                refine ⟨167061817930596185744979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445498181148256495319945357 167061817930596185744979509)
                ·
                  refine ⟨15662045430993392413591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167061817930596185744979509 15662045430993392413591829)
                  ·
                    refine ⟨734158379577815269387117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15662045430993392413591829 734158379577815269387117)
                    ·
                      rfl

theorem cell23_4289305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_4289305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289305 prefixEnd_4289305 := by exact prefixLift 4289305
  have htrace : WordTrace (prefixWord ++ tailWord_4289305) baseStart_4289305 baseEnd_4289305 := by
    simpa [prefixWord, tailWord_4289305, baseEnd_4289305] using wordTrace_append hprefix tailTrace_4289305
  have hstable : (prefixWord ++ tailWord_4289305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289305).length < 2 ^ (prefixWord ++ tailWord_4289305).sum := by decide
  have hdescent : baseEnd_4289305 < baseStart_4289305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289326 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4289326 : Nat := 118140960795 + 4289326 * 2 ^ 59
def prefixEnd_4289326 : Nat := 4983230072969 + 3 ^ 40 * 4289326 * 2
def baseEnd_4289326 : Nat := 734161973942396741999585

theorem tailTrace_4289326 : CollatzResearch.WordTrace tailWord_4289326 prefixEnd_4289326 734161973942396741999585 := by
  unfold tailWord_4289326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19555571457313991925492979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104296381105674623602629221 19555571457313991925492979)
  ·
    refine ⟨29333357185970987888239469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19555571457313991925492979 29333357185970987888239469)
    ·
      refine ⟨11000008944739120458089801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29333357185970987888239469 11000008944739120458089801)
      ·
        refine ⟨8250006708554340343567351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11000008944739120458089801 8250006708554340343567351)
        ·
          refine ⟨12375010062831510515351027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250006708554340343567351 12375010062831510515351027)
          ·
            refine ⟨18562515094247265773026541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375010062831510515351027 18562515094247265773026541)
            ·
              refine ⟨6960943160342724664884953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18562515094247265773026541 6960943160342724664884953)
              ·
                refine ⟨5220707370257043498663715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6960943160342724664884953 5220707370257043498663715)
                ·
                  refine ⟨7831061055385565247995573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220707370257043498663715 7831061055385565247995573)
                  ·
                    refine ⟨734161973942396741999585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7831061055385565247995573 734161973942396741999585)
                    ·
                      rfl

theorem cell23_4289326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4289326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289326 prefixEnd_4289326 := by exact prefixLift 4289326
  have htrace : WordTrace (prefixWord ++ tailWord_4289326) baseStart_4289326 baseEnd_4289326 := by
    simpa [prefixWord, tailWord_4289326, baseEnd_4289326] using wordTrace_append hprefix tailTrace_4289326
  have hstable : (prefixWord ++ tailWord_4289326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289326).length < 2 ^ (prefixWord ++ tailWord_4289326).sum := by decide
  have hdescent : baseEnd_4289326 < baseStart_4289326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289335 : List Nat := [1, 1, 3, 1, 2, 1, 3, 11]
def baseStart_4289335 : Nat := 118140960795 + 4289335 * 2 ^ 59
def prefixEnd_4289335 : Nat := 4983230072969 + 3 ^ 40 * 4289335 * 2
def baseEnd_4289335 : Nat := 81573723820484470029119

theorem tailTrace_4289335 : CollatzResearch.WordTrace tailWord_4289335 prefixEnd_4289335 81573723820484470029119 := by
  unfold tailWord_4289335
  simp only [CollatzResearch.WordTrace]
  refine ⟨156444899915479329941021459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104296599943652886627347639 156444899915479329941021459)
  ·
    refine ⟨234667349873218994911532189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156444899915479329941021459 234667349873218994911532189)
    ·
      refine ⟨88000256202457123091824571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234667349873218994911532189 88000256202457123091824571)
      ·
        refine ⟨132000384303685684637736857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88000256202457123091824571 132000384303685684637736857)
        ·
          refine ⟨99000288227764263478302643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132000384303685684637736857 99000288227764263478302643)
          ·
            refine ⟨148500432341646395217453965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99000288227764263478302643 148500432341646395217453965)
            ·
              refine ⟨55687662128117398206545237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148500432341646395217453965 55687662128117398206545237)
              ·
                refine ⟨81573723820484470029119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55687662128117398206545237 81573723820484470029119)
                ·
                  rfl

theorem cell23_4289335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 11].length) (baseStart_4289335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289335 prefixEnd_4289335 := by exact prefixLift 4289335
  have htrace : WordTrace (prefixWord ++ tailWord_4289335) baseStart_4289335 baseEnd_4289335 := by
    simpa [prefixWord, tailWord_4289335, baseEnd_4289335] using wordTrace_append hprefix tailTrace_4289335
  have hstable : (prefixWord ++ tailWord_4289335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289335).length < 2 ^ (prefixWord ++ tailWord_4289335).sum := by decide
  have hdescent : baseEnd_4289335 < baseStart_4289335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289355 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_4289355 : Nat := 118140960795 + 4289355 * 2 ^ 59
def prefixEnd_4289355 : Nat := 4983230072969 + 3 ^ 40 * 4289355 * 2
def baseEnd_4289355 : Nat := 2202500812766170612536121

theorem tailTrace_4289355 : CollatzResearch.WordTrace tailWord_4289355 prefixEnd_4289355 2202500812766170612536121 := by
  unfold tailWord_4289355
  simp only [CollatzResearch.WordTrace]
  refine ⟨156445629375406873356749519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104297086250271248904499679 156445629375406873356749519)
  ·
    refine ⟨234668444063110310035124279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156445629375406873356749519 234668444063110310035124279)
    ·
      refine ⟨352002666094665465052686419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234668444063110310035124279 352002666094665465052686419)
      ·
        refine ⟨528003999141998197579029629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352002666094665465052686419 528003999141998197579029629)
        ·
          refine ⟨198001499678249324092136111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528003999141998197579029629 198001499678249324092136111)
          ·
            refine ⟨297002249517373986138204167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198001499678249324092136111 297002249517373986138204167)
            ·
              refine ⟨445503374276060979207306251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297002249517373986138204167 445503374276060979207306251)
              ·
                refine ⟨668255061414091468810959377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445503374276060979207306251 668255061414091468810959377)
                ·
                  refine ⟨501191296060568601608219533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668255061414091468810959377 501191296060568601608219533)
                  ·
                    refine ⟨187946736022713225603082325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501191296060568601608219533 187946736022713225603082325)
                    ·
                      refine ⟨2202500812766170612536121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187946736022713225603082325 2202500812766170612536121)
                      ·
                        rfl

theorem cell23_4289355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_4289355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289355 prefixEnd_4289355 := by exact prefixLift 4289355
  have htrace : WordTrace (prefixWord ++ tailWord_4289355) baseStart_4289355 baseEnd_4289355 := by
    simpa [prefixWord, tailWord_4289355, baseEnd_4289355] using wordTrace_append hprefix tailTrace_4289355
  have hstable : (prefixWord ++ tailWord_4289355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289355).length < 2 ^ (prefixWord ++ tailWord_4289355).sum := by decide
  have hdescent : baseEnd_4289355 < baseStart_4289355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289356 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_4289356 : Nat := 118140960795 + 4289356 * 2 ^ 59
def prefixEnd_4289356 : Nat := 4983230072969 + 3 ^ 40 * 4289356 * 2
def baseEnd_4289356 : Nat := 734167108748941702874539

theorem tailTrace_4289356 : CollatzResearch.WordTrace tailWord_4289356 prefixEnd_4289356 734167108748941702874539 := by
  unfold tailWord_4289356
  simp only [CollatzResearch.WordTrace]
  refine ⟨78222832924201625263767961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104297110565602167018357281 78222832924201625263767961)
  ·
    refine ⟨58667124693151218947825971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78222832924201625263767961 58667124693151218947825971)
    ·
      refine ⟨88000687039726828421738957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58667124693151218947825971 88000687039726828421738957)
      ·
        refine ⟨33000257639897560658152109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88000687039726828421738957 33000257639897560658152109)
        ·
          refine ⟨12375096614961585246807041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33000257639897560658152109 12375096614961585246807041)
          ·
            refine ⟨9281322461221188935105281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12375096614961585246807041 9281322461221188935105281)
            ·
              refine ⟨6960991845915891701328961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281322461221188935105281 6960991845915891701328961)
              ·
                refine ⟨5220743884436918775996721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6960991845915891701328961 5220743884436918775996721)
                ·
                  refine ⟨3915557913327689081997541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5220743884436918775996721 3915557913327689081997541)
                  ·
                    refine ⟨734167108748941702874539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3915557913327689081997541 734167108748941702874539)
                    ·
                      rfl

theorem cell23_4289356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_4289356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289356 prefixEnd_4289356 := by exact prefixLift 4289356
  have htrace : WordTrace (prefixWord ++ tailWord_4289356) baseStart_4289356 baseEnd_4289356 := by
    simpa [prefixWord, tailWord_4289356, baseEnd_4289356] using wordTrace_append hprefix tailTrace_4289356
  have hstable : (prefixWord ++ tailWord_4289356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289356).length < 2 ^ (prefixWord ++ tailWord_4289356).sum := by decide
  have hdescent : baseEnd_4289356 < baseStart_4289356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289379 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3]
def baseStart_4289379 : Nat := 118140960795 + 4289379 * 2 ^ 59
def prefixEnd_4289379 : Nat := 4983230072969 + 3 ^ 40 * 4289379 * 2
def baseEnd_4289379 : Nat := 2202513136301878518636011

theorem tailTrace_4289379 : CollatzResearch.WordTrace tailWord_4289379 prefixEnd_4289379 2202513136301878518636011 := by
  unfold tailWord_4289379
  simp only [CollatzResearch.WordTrace]
  refine ⟨156446504727319925455623191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104297669818213283637082127 156446504727319925455623191)
  ·
    refine ⟨234669757090979888183434787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156446504727319925455623191 234669757090979888183434787)
    ·
      refine ⟨352004635636469832275152181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234669757090979888183434787 352004635636469832275152181)
      ·
        refine ⟨33000434590919046775795517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 352004635636469832275152181 33000434590919046775795517)
        ·
          refine ⟨12375162971594642540923319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33000434590919046775795517 12375162971594642540923319)
          ·
            refine ⟨18562744457391963811384979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375162971594642540923319 18562744457391963811384979)
            ·
              refine ⟨27844116686087945717077469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18562744457391963811384979 27844116686087945717077469)
              ·
                refine ⟨10441543757282979643904051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27844116686087945717077469 10441543757282979643904051)
                ·
                  refine ⟨15662315635924469465856077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10441543757282979643904051 15662315635924469465856077)
                  ·
                    refine ⟨5873368363471676049696029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15662315635924469465856077 5873368363471676049696029)
                    ·
                      refine ⟨2202513136301878518636011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873368363471676049696029 2202513136301878518636011)
                      ·
                        rfl

theorem cell23_4289379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_4289379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289379 prefixEnd_4289379 := by exact prefixLift 4289379
  have htrace : WordTrace (prefixWord ++ tailWord_4289379) baseStart_4289379 baseEnd_4289379 := by
    simpa [prefixWord, tailWord_4289379, baseEnd_4289379] using wordTrace_append hprefix tailTrace_4289379
  have hstable : (prefixWord ++ tailWord_4289379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289379).length < 2 ^ (prefixWord ++ tailWord_4289379).sum := by decide
  have hdescent : baseEnd_4289379 < baseStart_4289379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289413 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_4289413 : Nat := 118140960795 + 4289413 * 2 ^ 59
def prefixEnd_4289413 : Nat := 4983230072969 + 3 ^ 40 * 4289413 * 2
def baseEnd_4289413 : Nat := 2202530594644131385610855

theorem tailTrace_4289413 : CollatzResearch.WordTrace tailWord_4289413 prefixEnd_4289413 2202530594644131385610855 := by
  unfold tailWord_4289413
  simp only [CollatzResearch.WordTrace]
  refine ⟨156447744809196749262360893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104298496539464499508240595 156447744809196749262360893)
  ·
    refine ⟨58667904303448780973385335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156447744809196749262360893 58667904303448780973385335)
    ·
      refine ⟨88001856455173171460078003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58667904303448780973385335 88001856455173171460078003)
      ·
        refine ⟨132002784682759757190117005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88001856455173171460078003 132002784682759757190117005)
        ·
          refine ⟨49501044256034908946293877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132002784682759757190117005 49501044256034908946293877)
          ·
            refine ⟨4640722899003272713715051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49501044256034908946293877 4640722899003272713715051)
            ·
              refine ⟨6961084348504909070572577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640722899003272713715051 6961084348504909070572577)
              ·
                refine ⟨5220813261378681802929433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6961084348504909070572577 5220813261378681802929433)
                ·
                  refine ⟨3915609946034011352197075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5220813261378681802929433 3915609946034011352197075)
                  ·
                    refine ⟨5873414919051017028295613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915609946034011352197075 5873414919051017028295613)
                    ·
                      refine ⟨2202530594644131385610855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873414919051017028295613 2202530594644131385610855)
                      ·
                        rfl

theorem cell23_4289413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_4289413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289413 prefixEnd_4289413 := by exact prefixLift 4289413
  have htrace : WordTrace (prefixWord ++ tailWord_4289413) baseStart_4289413 baseEnd_4289413 := by
    simpa [prefixWord, tailWord_4289413, baseEnd_4289413] using wordTrace_append hprefix tailTrace_4289413
  have hstable : (prefixWord ++ tailWord_4289413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289413).length < 2 ^ (prefixWord ++ tailWord_4289413).sum := by decide
  have hdescent : baseEnd_4289413 < baseStart_4289413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289419 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 4, 2]
def baseStart_4289419 : Nat := 118140960795 + 4289419 * 2 ^ 59
def prefixEnd_4289419 : Nat := 4983230072969 + 3 ^ 40 * 4289419 * 2
def baseEnd_4289419 : Nat := 2202533675528058362135827

theorem tailTrace_4289419 : CollatzResearch.WordTrace tailWord_4289419 prefixEnd_4289419 2202533675528058362135827 := by
  unfold tailWord_4289419
  simp only [CollatzResearch.WordTrace]
  refine ⟨156447963647175012287079311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104298642431450008191386207 156447963647175012287079311)
  ·
    refine ⟨234671945470762518430618967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156447963647175012287079311 234671945470762518430618967)
    ·
      refine ⟨352007918206143777645928451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234671945470762518430618967 352007918206143777645928451)
      ·
        refine ⟨528011877309215666468892677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352007918206143777645928451 528011877309215666468892677)
        ·
          refine ⟨99002226995477937462917377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 528011877309215666468892677 99002226995477937462917377)
          ·
            refine ⟨74251670246608453097188033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99002226995477937462917377 74251670246608453097188033)
            ·
              refine ⟨55688752684956339822891025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74251670246608453097188033 55688752684956339822891025)
              ·
                refine ⟨41766564513717254867168269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55688752684956339822891025 41766564513717254867168269)
                ·
                  refine ⟨15662461692643970575188101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41766564513717254867168269 15662461692643970575188101)
                  ·
                    refine ⟨2936711567370744482847769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15662461692643970575188101 2936711567370744482847769)
                    ·
                      refine ⟨2202533675528058362135827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936711567370744482847769 2202533675528058362135827)
                      ·
                        rfl

theorem cell23_4289419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4, 2].length) (baseStart_4289419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289419 prefixEnd_4289419 := by exact prefixLift 4289419
  have htrace : WordTrace (prefixWord ++ tailWord_4289419) baseStart_4289419 baseEnd_4289419 := by
    simpa [prefixWord, tailWord_4289419, baseEnd_4289419] using wordTrace_append hprefix tailTrace_4289419
  have hstable : (prefixWord ++ tailWord_4289419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289419).length < 2 ^ (prefixWord ++ tailWord_4289419).sum := by decide
  have hdescent : baseEnd_4289419 < baseStart_4289419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289430 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4289430 : Nat := 118140960795 + 4289430 * 2 ^ 59
def prefixEnd_4289430 : Nat := 4983230072969 + 3 ^ 40 * 4289430 * 2
def baseEnd_4289430 : Nat := 2202539323815257819098277

theorem tailTrace_4289430 : CollatzResearch.WordTrace tailWord_4289430 prefixEnd_4289430 2202539323815257819098277 := by
  unfold tailWord_4289430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778022803133447572858109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104298909900090107443819829 9778022803133447572858109)
  ·
    refine ⟨3666758551175042839821791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9778022803133447572858109 3666758551175042839821791)
    ·
      refine ⟨5500137826762564259732687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666758551175042839821791 5500137826762564259732687)
      ·
        refine ⟨8250206740143846389599031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500137826762564259732687 8250206740143846389599031)
        ·
          refine ⟨12375310110215769584398547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250206740143846389599031 12375310110215769584398547)
          ·
            refine ⟨18562965165323654376597821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375310110215769584398547 18562965165323654376597821)
            ·
              refine ⟨6961111936996370391224183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18562965165323654376597821 6961111936996370391224183)
              ·
                refine ⟨10441667905494555586836275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961111936996370391224183 10441667905494555586836275)
                ·
                  refine ⟨15662501858241833380254413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10441667905494555586836275 15662501858241833380254413)
                  ·
                    refine ⟨5873438196840687517595405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15662501858241833380254413 5873438196840687517595405)
                    ·
                      refine ⟨2202539323815257819098277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873438196840687517595405 2202539323815257819098277)
                      ·
                        rfl

theorem cell23_4289430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4289430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289430 prefixEnd_4289430 := by exact prefixLift 4289430
  have htrace : WordTrace (prefixWord ++ tailWord_4289430) baseStart_4289430 baseEnd_4289430 := by
    simpa [prefixWord, tailWord_4289430, baseEnd_4289430] using wordTrace_append hprefix tailTrace_4289430
  have hstable : (prefixWord ++ tailWord_4289430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289430).length < 2 ^ (prefixWord ++ tailWord_4289430).sum := by decide
  have hdescent : baseEnd_4289430 < baseStart_4289430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289459 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 5]
def baseStart_4289459 : Nat := 118140960795 + 4289459 * 2 ^ 59
def prefixEnd_4289459 : Nat := 4983230072969 + 3 ^ 40 * 4289459 * 2
def baseEnd_4289459 : Nat := 244728246083804245070627

theorem tailTrace_4289459 : CollatzResearch.WordTrace tailWord_4289459 prefixEnd_4289459 244728246083804245070627 := by
  unfold tailWord_4289459
  simp only [CollatzResearch.WordTrace]
  refine ⟨156449422567030099118535431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104299615044686732745690287 156449422567030099118535431)
  ·
    refine ⟨234674133850545148677803147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156449422567030099118535431 234674133850545148677803147)
    ·
      refine ⟨352011200775817723016704721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234674133850545148677803147 352011200775817723016704721)
      ·
        refine ⟨264008400581863292262528541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352011200775817723016704721 264008400581863292262528541)
        ·
          refine ⟨99003150218198734598448203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264008400581863292262528541 99003150218198734598448203)
          ·
            refine ⟨148504725327298101897672305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99003150218198734598448203 148504725327298101897672305)
            ·
              refine ⟨111378543995473576423254229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148504725327298101897672305 111378543995473576423254229)
              ·
                refine ⟨2610434624893911947420021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111378543995473576423254229 2610434624893911947420021)
                ·
                  refine ⟨244728246083804245070627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610434624893911947420021 244728246083804245070627)
                  ·
                    rfl

theorem cell23_4289459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 5].length) (baseStart_4289459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289459 prefixEnd_4289459 := by exact prefixLift 4289459
  have htrace : WordTrace (prefixWord ++ tailWord_4289459) baseStart_4289459 baseEnd_4289459 := by
    simpa [prefixWord, tailWord_4289459, baseEnd_4289459] using wordTrace_append hprefix tailTrace_4289459
  have hstable : (prefixWord ++ tailWord_4289459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289459).length < 2 ^ (prefixWord ++ tailWord_4289459).sum := by decide
  have hdescent : baseEnd_4289459 < baseStart_4289459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289570 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_4289570 : Nat := 118140960795 + 4289570 * 2 ^ 59
def prefixEnd_4289570 : Nat := 4983230072969 + 3 ^ 40 * 4289570 * 2
def baseEnd_4289570 : Nat := 734203737035629090449211

theorem tailTrace_4289570 : CollatzResearch.WordTrace tailWord_4289570 prefixEnd_4289570 734203737035629090449211 := by
  unfold tailWord_4289570
  simp only [CollatzResearch.WordTrace]
  refine ⟨39113367767406991268956541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104302314046418643383884109 39113367767406991268956541)
  ·
    refine ⟨14667512912777621725858703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39113367767406991268956541 14667512912777621725858703)
    ·
      refine ⟨22001269369166432588788055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14667512912777621725858703 22001269369166432588788055)
      ·
        refine ⟨33001904053749648883182083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22001269369166432588788055 33001904053749648883182083)
        ·
          refine ⟨49502856080624473324773125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33001904053749648883182083 49502856080624473324773125)
          ·
            refine ⟨9281785515117088748394961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49502856080624473324773125 9281785515117088748394961)
            ·
              refine ⟨6961339136337816561296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281785515117088748394961 6961339136337816561296221)
              ·
                refine ⟨2610502176126681210486083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6961339136337816561296221 2610502176126681210486083)
                ·
                  refine ⟨3915753264190021815729125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610502176126681210486083 3915753264190021815729125)
                  ·
                    refine ⟨734203737035629090449211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3915753264190021815729125 734203737035629090449211)
                    ·
                      rfl

theorem cell23_4289570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_4289570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289570 prefixEnd_4289570 := by exact prefixLift 4289570
  have htrace : WordTrace (prefixWord ++ tailWord_4289570) baseStart_4289570 baseEnd_4289570 := by
    simpa [prefixWord, tailWord_4289570, baseEnd_4289570] using wordTrace_append hprefix tailTrace_4289570
  have hstable : (prefixWord ++ tailWord_4289570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289570).length < 2 ^ (prefixWord ++ tailWord_4289570).sum := by decide
  have hdescent : baseEnd_4289570 < baseStart_4289570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289593 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4289593 : Nat := 118140960795 + 4289593 * 2 ^ 59
def prefixEnd_4289593 : Nat := 4983230072969 + 3 ^ 40 * 4289593 * 2
def baseEnd_4289593 : Nat := 2202623021161940681360027

theorem tailTrace_4289593 : CollatzResearch.WordTrace tailWord_4289593 prefixEnd_4289593 2202623021161940681360027 := by
  unfold tailWord_4289593
  simp only [CollatzResearch.WordTrace]
  refine ⟨156454309948544640003913433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104302873299029760002608955 156454309948544640003913433)
  ·
    refine ⟨117340732461408480002935075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156454309948544640003913433 117340732461408480002935075)
    ·
      refine ⟨176011098692112720004402613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117340732461408480002935075 176011098692112720004402613)
      ·
        refine ⟨16501040502385567500412745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176011098692112720004402613 16501040502385567500412745)
        ·
          refine ⟨12375780376789175625309559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16501040502385567500412745 12375780376789175625309559)
          ·
            refine ⟨18563670565183763437964339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375780376789175625309559 18563670565183763437964339)
            ·
              refine ⟨27845505847775645156946509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18563670565183763437964339 27845505847775645156946509)
              ·
                refine ⟨10442064692915866933854941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27845505847775645156946509 10442064692915866933854941)
                ·
                  refine ⟨3915774259843450100195603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10442064692915866933854941 3915774259843450100195603)
                  ·
                    refine ⟨5873661389765175150293405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915774259843450100195603 5873661389765175150293405)
                    ·
                      refine ⟨2202623021161940681360027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873661389765175150293405 2202623021161940681360027)
                      ·
                        rfl

theorem cell23_4289593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4289593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289593 prefixEnd_4289593 := by exact prefixLift 4289593
  have htrace : WordTrace (prefixWord ++ tailWord_4289593) baseStart_4289593 baseEnd_4289593 := by
    simpa [prefixWord, tailWord_4289593, baseEnd_4289593] using wordTrace_append hprefix tailTrace_4289593
  have hstable : (prefixWord ++ tailWord_4289593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289593).length < 2 ^ (prefixWord ++ tailWord_4289593).sum := by decide
  have hdescent : baseEnd_4289593 < baseStart_4289593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289609 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_4289609 : Nat := 118140960795 + 4289609 * 2 ^ 59
def prefixEnd_4289609 : Nat := 4983230072969 + 3 ^ 40 * 4289609 * 2
def baseEnd_4289609 : Nat := 734210412284137539586651

theorem tailTrace_4289609 : CollatzResearch.WordTrace tailWord_4289609 prefixEnd_4289609 734210412284137539586651 := by
  unfold tailWord_4289609
  simp only [CollatzResearch.WordTrace]
  refine ⟨156454893516486674736495881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104303262344324449824330587 156454893516486674736495881)
  ·
    refine ⟨117341170137365006052371911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156454893516486674736495881 117341170137365006052371911)
    ·
      refine ⟨176011755206047509078557867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117341170137365006052371911 176011755206047509078557867)
      ·
        refine ⟨264017632809071263617836801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176011755206047509078557867 264017632809071263617836801)
        ·
          refine ⟨198013224606803447713377601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264017632809071263617836801 198013224606803447713377601)
          ·
            refine ⟨148509918455102585785033201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198013224606803447713377601 148509918455102585785033201)
            ·
              refine ⟨111382438841326939338774901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148509918455102585785033201 111382438841326939338774901)
              ·
                refine ⟨10442103641374400563010147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111382438841326939338774901 10442103641374400563010147)
                ·
                  refine ⟨15663155462061600844515221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10442103641374400563010147 15663155462061600844515221)
                  ·
                    refine ⟨734210412284137539586651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15663155462061600844515221 734210412284137539586651)
                    ·
                      rfl

theorem cell23_4289609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_4289609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289609 prefixEnd_4289609 := by exact prefixLift 4289609
  have htrace : WordTrace (prefixWord ++ tailWord_4289609) baseStart_4289609 baseEnd_4289609 := by
    simpa [prefixWord, tailWord_4289609, baseEnd_4289609] using wordTrace_append hprefix tailTrace_4289609
  have hstable : (prefixWord ++ tailWord_4289609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289609).length < 2 ^ (prefixWord ++ tailWord_4289609).sum := by decide
  have hdescent : baseEnd_4289609 < baseStart_4289609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289613 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4289613 : Nat := 118140960795 + 4289613 * 2 ^ 59
def prefixEnd_4289613 : Nat := 4983230072969 + 3 ^ 40 * 4289613 * 2
def baseEnd_4289613 : Nat := 734211096925010201036645

theorem tailTrace_4289613 : CollatzResearch.WordTrace tailWord_4289613 prefixEnd_4289613 734211096925010201036645 := by
  unfold tailWord_4289613
  simp only [CollatzResearch.WordTrace]
  refine ⟨156455039408472183419641493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104303359605648122279760995 156455039408472183419641493)
  ·
    refine ⟨7333829972272133597795695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156455039408472183419641493 7333829972272133597795695)
    ·
      refine ⟨11000744958408200396693543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7333829972272133597795695 11000744958408200396693543)
      ·
        refine ⟨16501117437612300595040315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11000744958408200396693543 16501117437612300595040315)
        ·
          refine ⟨24751676156418450892560473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16501117437612300595040315 24751676156418450892560473)
          ·
            refine ⟨18563757117313838169420355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24751676156418450892560473 18563757117313838169420355)
            ·
              refine ⟨27845635675970757254130533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18563757117313838169420355 27845635675970757254130533)
              ·
                refine ⟨5221056689244516985149475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27845635675970757254130533 5221056689244516985149475)
                ·
                  refine ⟨7831585033866775477724213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5221056689244516985149475 7831585033866775477724213)
                  ·
                    refine ⟨734211096925010201036645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7831585033866775477724213 734211096925010201036645)
                    ·
                      rfl

theorem cell23_4289613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4289613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289613 prefixEnd_4289613 := by exact prefixLift 4289613
  have htrace : WordTrace (prefixWord ++ tailWord_4289613) baseStart_4289613 baseEnd_4289613 := by
    simpa [prefixWord, tailWord_4289613, baseEnd_4289613] using wordTrace_append hprefix tailTrace_4289613
  have hstable : (prefixWord ++ tailWord_4289613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289613).length < 2 ^ (prefixWord ++ tailWord_4289613).sum := by decide
  have hdescent : baseEnd_4289613 < baseStart_4289613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289633 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_4289633 : Nat := 118140960795 + 4289633 * 2 ^ 59
def prefixEnd_4289633 : Nat := 4983230072969 + 3 ^ 40 * 4289633 * 2
def baseEnd_4289633 : Nat := 2202643560388120524859843

theorem tailTrace_4289633 : CollatzResearch.WordTrace tailWord_4289633 prefixEnd_4289633 2202643560388120524859843 := by
  unfold tailWord_4289633
  simp only [CollatzResearch.WordTrace]
  refine ⟨156455768868399726835369553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104303845912266484556913035 156455768868399726835369553)
  ·
    refine ⟨117341826651299795126527165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156455768868399726835369553 117341826651299795126527165)
    ·
      refine ⟨44003184994237423172447687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117341826651299795126527165 44003184994237423172447687)
      ·
        refine ⟨66004777491356134758671531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44003184994237423172447687 66004777491356134758671531)
        ·
          refine ⟨99007166237034202138007297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66004777491356134758671531 99007166237034202138007297)
          ·
            refine ⟨74255374677775651603505473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99007166237034202138007297 74255374677775651603505473)
            ·
              refine ⟨55691531008331738702629105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74255374677775651603505473 55691531008331738702629105)
              ·
                refine ⟨41768648256248804026971829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55691531008331738702629105 41768648256248804026971829)
                ·
                  refine ⟨3915810774023325377528609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41768648256248804026971829 3915810774023325377528609)
                  ·
                    refine ⟨2936858080517494033146457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3915810774023325377528609 2936858080517494033146457)
                    ·
                      refine ⟨2202643560388120524859843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2936858080517494033146457 2202643560388120524859843)
                      ·
                        rfl

theorem cell23_4289633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_4289633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289633 prefixEnd_4289633 := by exact prefixLift 4289633
  have htrace : WordTrace (prefixWord ++ tailWord_4289633) baseStart_4289633 baseEnd_4289633 := by
    simpa [prefixWord, tailWord_4289633, baseEnd_4289633] using wordTrace_append hprefix tailTrace_4289633
  have hstable : (prefixWord ++ tailWord_4289633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289633).length < 2 ^ (prefixWord ++ tailWord_4289633).sum := by decide
  have hdescent : baseEnd_4289633 < baseStart_4289633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289636 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_4289636 : Nat := 118140960795 + 4289636 * 2 ^ 59
def prefixEnd_4289636 : Nat := 4983230072969 + 3 ^ 40 * 4289636 * 2
def baseEnd_4289636 : Nat := 2202645100830084013122329

theorem tailTrace_4289636 : CollatzResearch.WordTrace tailWord_4289636 prefixEnd_4289636 2202645100830084013122329 := by
  unfold tailWord_4289636
  simp only [CollatzResearch.WordTrace]
  refine ⟨78227939143694429173864381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104303918858259238898485841 78227939143694429173864381)
  ·
    refine ⟨29335477178885410940199143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78227939143694429173864381 29335477178885410940199143)
    ·
      refine ⟨44003215768328116410298715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29335477178885410940199143 44003215768328116410298715)
      ·
        refine ⟨66004823652492174615448073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44003215768328116410298715 66004823652492174615448073)
        ·
          refine ⟨49503617739369130961586055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66004823652492174615448073 49503617739369130961586055)
          ·
            refine ⟨74255426609053696442379083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49503617739369130961586055 74255426609053696442379083)
            ·
              refine ⟨111383139913580544663568625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74255426609053696442379083 111383139913580544663568625)
              ·
                refine ⟨83537354935185408497676469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111383139913580544663568625 83537354935185408497676469)
                ·
                  refine ⟨7831627025173632046657169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83537354935185408497676469 7831627025173632046657169)
                  ·
                    refine ⟨5873720268880224034992877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7831627025173632046657169 5873720268880224034992877)
                    ·
                      refine ⟨2202645100830084013122329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873720268880224034992877 2202645100830084013122329)
                      ·
                        rfl

theorem cell23_4289636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_4289636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289636 prefixEnd_4289636 := by exact prefixLift 4289636
  have htrace : WordTrace (prefixWord ++ tailWord_4289636) baseStart_4289636 baseEnd_4289636 := by
    simpa [prefixWord, tailWord_4289636, baseEnd_4289636] using wordTrace_append hprefix tailTrace_4289636
  have hstable : (prefixWord ++ tailWord_4289636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289636).length < 2 ^ (prefixWord ++ tailWord_4289636).sum := by decide
  have hdescent : baseEnd_4289636 < baseStart_4289636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289639 : List Nat := [1, 1, 5, 1, 1, 3, 11]
def baseStart_4289639 : Nat := 118140960795 + 4289639 * 2 ^ 59
def prefixEnd_4289639 : Nat := 4983230072969 + 3 ^ 40 * 4289639 * 2
def baseEnd_4289639 : Nat := 27193168410766018535615

theorem tailTrace_4289639 : CollatzResearch.WordTrace tailWord_4289639 prefixEnd_4289639 27193168410766018535615 := by
  unfold tailWord_4289639
  simp only [CollatzResearch.WordTrace]
  refine ⟨156455987706377989860087971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104303991804251993240058647 156455987706377989860087971)
  ·
    refine ⟨234683981559566984790131957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156455987706377989860087971 234683981559566984790131957)
    ·
      refine ⟨22001623271209404824074871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234683981559566984790131957 22001623271209404824074871)
      ·
        refine ⟨33002434906814107236112307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22001623271209404824074871 33002434906814107236112307)
        ·
          refine ⟨49503652360221160854168461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33002434906814107236112307 49503652360221160854168461)
          ·
            refine ⟨18563869635082935320313173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49503652360221160854168461 18563869635082935320313173)
            ·
              refine ⟨27193168410766018535615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18563869635082935320313173 27193168410766018535615)
              ·
                rfl

theorem cell23_4289639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 11].length) (baseStart_4289639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289639 prefixEnd_4289639 := by exact prefixLift 4289639
  have htrace : WordTrace (prefixWord ++ tailWord_4289639) baseStart_4289639 baseEnd_4289639 := by
    simpa [prefixWord, tailWord_4289639, baseEnd_4289639] using wordTrace_append hprefix tailTrace_4289639
  have hstable : (prefixWord ++ tailWord_4289639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289639).length < 2 ^ (prefixWord ++ tailWord_4289639).sum := by decide
  have hdescent : baseEnd_4289639 < baseStart_4289639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289646 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4289646 : Nat := 118140960795 + 4289646 * 2 ^ 59
def prefixEnd_4289646 : Nat := 4983230072969 + 3 ^ 40 * 4289646 * 2
def baseEnd_4289646 : Nat := 2202650235636628973997283

theorem tailTrace_4289646 : CollatzResearch.WordTrace tailWord_4289646 prefixEnd_4289646 2202650235636628973997283 := by
  unfold tailWord_4289646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557030377169078756949099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104304162011568420037061861 19557030377169078756949099)
  ·
    refine ⟨29335545565753618135423649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19557030377169078756949099 29335545565753618135423649)
    ·
      refine ⟨22001659174315213601567737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29335545565753618135423649 22001659174315213601567737)
      ·
        refine ⟨16501244380736410201175803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22001659174315213601567737 16501244380736410201175803)
        ·
          refine ⟨24751866571104615301763705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16501244380736410201175803 24751866571104615301763705)
          ·
            refine ⟨18563899928328461476322779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24751866571104615301763705 18563899928328461476322779)
            ·
              refine ⟨27845849892492692214484169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18563899928328461476322779 27845849892492692214484169)
              ·
                refine ⟨20884387419369519160863127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27845849892492692214484169 20884387419369519160863127)
                ·
                  refine ⟨31326581129054278741294691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20884387419369519160863127 31326581129054278741294691)
                  ·
                    refine ⟨46989871693581418111942037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31326581129054278741294691 46989871693581418111942037)
                    ·
                      refine ⟨2202650235636628973997283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46989871693581418111942037 2202650235636628973997283)
                      ·
                        rfl

theorem cell23_4289646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4289646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289646 prefixEnd_4289646 := by exact prefixLift 4289646
  have htrace : WordTrace (prefixWord ++ tailWord_4289646) baseStart_4289646 baseEnd_4289646 := by
    simpa [prefixWord, tailWord_4289646, baseEnd_4289646] using wordTrace_append hprefix tailTrace_4289646
  have hstable : (prefixWord ++ tailWord_4289646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289646).length < 2 ^ (prefixWord ++ tailWord_4289646).sum := by decide
  have hdescent : baseEnd_4289646 < baseStart_4289646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289679 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_4289679 : Nat := 118140960795 + 4289679 * 2 ^ 59
def prefixEnd_4289679 : Nat := 4983230072969 + 3 ^ 40 * 4289679 * 2
def baseEnd_4289679 : Nat := 2202667180498227344884631

theorem tailTrace_4289679 : CollatzResearch.WordTrace tailWord_4289679 prefixEnd_4289679 2202667180498227344884631 := by
  unfold tailWord_4289679
  simp only [CollatzResearch.WordTrace]
  refine ⟨156457446626233076691544091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104304964417488717794362727 156457446626233076691544091)
  ·
    refine ⟨234686169939349615037316137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156457446626233076691544091 234686169939349615037316137)
    ·
      refine ⟨176014627454512211277987103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234686169939349615037316137 176014627454512211277987103)
      ·
        refine ⟨264021941181768316916980655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176014627454512211277987103 264021941181768316916980655)
        ·
          refine ⟨396032911772652475375470983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264021941181768316916980655 396032911772652475375470983)
          ·
            refine ⟨594049367658978713063206475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396032911772652475375470983 594049367658978713063206475)
            ·
              refine ⟨891074051488468069594809713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594049367658978713063206475 891074051488468069594809713)
              ·
                refine ⟨668305538616351052196107285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891074051488468069594809713 668305538616351052196107285)
                ·
                  refine ⟨31326822122641455571692529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 668305538616351052196107285 31326822122641455571692529)
                  ·
                    refine ⟨23495116591981091678769397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31326822122641455571692529 23495116591981091678769397)
                    ·
                      refine ⟨2202667180498227344884631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23495116591981091678769397 2202667180498227344884631)
                      ·
                        rfl

theorem cell23_4289679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_4289679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289679 prefixEnd_4289679 := by exact prefixLift 4289679
  have htrace : WordTrace (prefixWord ++ tailWord_4289679) baseStart_4289679 baseEnd_4289679 := by
    simpa [prefixWord, tailWord_4289679, baseEnd_4289679] using wordTrace_append hprefix tailTrace_4289679
  have hstable : (prefixWord ++ tailWord_4289679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289679).length < 2 ^ (prefixWord ++ tailWord_4289679).sum := by decide
  have hdescent : baseEnd_4289679 < baseStart_4289679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289699 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 8]
def baseStart_4289699 : Nat := 118140960795 + 4289699 * 2 ^ 59
def prefixEnd_4289699 : Nat := 4983230072969 + 3 ^ 40 * 4289699 * 2
def baseEnd_4289699 : Nat := 734225816703772422211513

theorem tailTrace_4289699 : CollatzResearch.WordTrace tailWord_4289699 prefixEnd_4289699 734225816703772422211513 := by
  unfold tailWord_4289699
  simp only [CollatzResearch.WordTrace]
  refine ⟨156458176086160620107272151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104305450724107080071514767 156458176086160620107272151)
  ·
    refine ⟨234687264129240930160908227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156458176086160620107272151 234687264129240930160908227)
    ·
      refine ⟨352030896193861395241362341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234687264129240930160908227 352030896193861395241362341)
      ·
        refine ⟨66005793036349011607755439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 352030896193861395241362341 66005793036349011607755439)
        ·
          refine ⟨99008689554523517411633159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66005793036349011607755439 99008689554523517411633159)
          ·
            refine ⟨148513034331785276117449739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99008689554523517411633159 148513034331785276117449739)
            ·
              refine ⟨222769551497677914176174609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148513034331785276117449739 222769551497677914176174609)
              ·
                refine ⟨167077163623258435632130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222769551497677914176174609 167077163623258435632130957)
                ·
                  refine ⟨62653936358721913362049109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167077163623258435632130957 62653936358721913362049109)
                  ·
                    refine ⟨734225816703772422211513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62653936358721913362049109 734225816703772422211513)
                    ·
                      rfl

theorem cell23_4289699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_4289699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289699 prefixEnd_4289699 := by exact prefixLift 4289699
  have htrace : WordTrace (prefixWord ++ tailWord_4289699) baseStart_4289699 baseEnd_4289699 := by
    simpa [prefixWord, tailWord_4289699, baseEnd_4289699] using wordTrace_append hprefix tailTrace_4289699
  have hstable : (prefixWord ++ tailWord_4289699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289699).length < 2 ^ (prefixWord ++ tailWord_4289699).sum := by decide
  have hdescent : baseEnd_4289699 < baseStart_4289699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289700 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_4289700 : Nat := 118140960795 + 4289700 * 2 ^ 59
def prefixEnd_4289700 : Nat := 4983230072969 + 3 ^ 40 * 4289700 * 2
def baseEnd_4289700 : Nat := 2202677963591971762722035

theorem tailTrace_4289700 : CollatzResearch.WordTrace tailWord_4289700 prefixEnd_4289700 2202677963591971762722035 := by
  unfold tailWord_4289700
  simp only [CollatzResearch.WordTrace]
  refine ⟨78229106279578498639029277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104305475039437998185372369 78229106279578498639029277)
  ·
    refine ⟨29335914854841936989635979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78229106279578498639029277 29335914854841936989635979)
    ·
      refine ⟨44003872282262905484453969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29335914854841936989635979 44003872282262905484453969)
      ·
        refine ⟨33002904211697179113340477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44003872282262905484453969 33002904211697179113340477)
        ·
          refine ⟨12376089079386442167502679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33002904211697179113340477 12376089079386442167502679)
          ·
            refine ⟨18564133619079663251254019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12376089079386442167502679 18564133619079663251254019)
            ·
              refine ⟨27846200428619494876881029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18564133619079663251254019 27846200428619494876881029)
              ·
                refine ⟨5221162580366155289415193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27846200428619494876881029 5221162580366155289415193)
                ·
                  refine ⟨3915871935274616467061395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221162580366155289415193 3915871935274616467061395)
                  ·
                    refine ⟨5873807902911924700592093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915871935274616467061395 5873807902911924700592093)
                    ·
                      refine ⟨2202677963591971762722035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5873807902911924700592093 2202677963591971762722035)
                      ·
                        rfl

theorem cell23_4289700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_4289700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289700 prefixEnd_4289700 := by exact prefixLift 4289700
  have htrace : WordTrace (prefixWord ++ tailWord_4289700) baseStart_4289700 baseEnd_4289700 := by
    simpa [prefixWord, tailWord_4289700, baseEnd_4289700] using wordTrace_append hprefix tailTrace_4289700
  have hstable : (prefixWord ++ tailWord_4289700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289700).length < 2 ^ (prefixWord ++ tailWord_4289700).sum := by decide
  have hdescent : baseEnd_4289700 < baseStart_4289700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289746 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_4289746 : Nat := 118140960795 + 4289746 * 2 ^ 59
def prefixEnd_4289746 : Nat := 4983230072969 + 3 ^ 40 * 4289746 * 2
def baseEnd_4289746 : Nat := 244744620411342064749647

theorem tailTrace_4289746 : CollatzResearch.WordTrace tailWord_4289746 prefixEnd_4289746 244744620411342064749647 := by
  unfold tailWord_4289746
  simp only [CollatzResearch.WordTrace]
  refine ⟨39114972579247586783558273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104306593544660231422822061 39114972579247586783558273)
  ·
    refine ⟨29336229434435690087668705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39114972579247586783558273 29336229434435690087668705)
    ·
      refine ⟨22002172075826767565751529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29336229434435690087668705 22002172075826767565751529)
      ·
        refine ⟨16501629056870075674313647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22002172075826767565751529 16501629056870075674313647)
        ·
          refine ⟨24752443585305113511470471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16501629056870075674313647 24752443585305113511470471)
          ·
            refine ⟨37128665377957670267205707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24752443585305113511470471 37128665377957670267205707)
            ·
              refine ⟨55692998066936505400808561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37128665377957670267205707 55692998066936505400808561)
              ·
                refine ⟨41769748550202379050606421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55692998066936505400808561 41769748550202379050606421)
                ·
                  refine ⟨244744620411342064749647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41769748550202379050606421 244744620411342064749647)
                  ·
                    rfl

theorem cell23_4289746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_4289746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289746 prefixEnd_4289746 := by exact prefixLift 4289746
  have htrace : WordTrace (prefixWord ++ tailWord_4289746) baseStart_4289746 baseEnd_4289746 := by
    simpa [prefixWord, tailWord_4289746, baseEnd_4289746] using wordTrace_append hprefix tailTrace_4289746
  have hstable : (prefixWord ++ tailWord_4289746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289746).length < 2 ^ (prefixWord ++ tailWord_4289746).sum := by decide
  have hdescent : baseEnd_4289746 < baseStart_4289746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289850 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_4289850 : Nat := 118140960795 + 4289850 * 2 ^ 59
def prefixEnd_4289850 : Nat := 4983230072969 + 3 ^ 40 * 4289850 * 2
def baseEnd_4289850 : Nat := 2202754985690146175846345

theorem tailTrace_4289850 : CollatzResearch.WordTrace tailWord_4289850 prefixEnd_4289850 2202754985690146175846345 := by
  unfold tailWord_4289850
  simp only [CollatzResearch.WordTrace]
  refine ⟨39115920877153393224004751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104309122339075715264012669 39115920877153393224004751)
  ·
    refine ⟨58673881315730089836007127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39115920877153393224004751 58673881315730089836007127)
    ·
      refine ⟨88010821973595134754010691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58673881315730089836007127 88010821973595134754010691)
      ·
        refine ⟨132016232960392702131016037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88010821973595134754010691 132016232960392702131016037)
        ·
          refine ⟨24753043680073631649565507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132016232960392702131016037 24753043680073631649565507)
          ·
            refine ⟨37129565520110447474348261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24753043680073631649565507 37129565520110447474348261)
            ·
              refine ⟨6961793535020708901440299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37129565520110447474348261 6961793535020708901440299)
              ·
                refine ⟨10442690302531063352160449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961793535020708901440299 10442690302531063352160449)
                ·
                  refine ⟨7832017726898297514120337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10442690302531063352160449 7832017726898297514120337)
                  ·
                    refine ⟨5874013295173723135590253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7832017726898297514120337 5874013295173723135590253)
                    ·
                      refine ⟨2202754985690146175846345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874013295173723135590253 2202754985690146175846345)
                      ·
                        rfl

theorem cell23_4289850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_4289850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289850 prefixEnd_4289850 := by exact prefixLift 4289850
  have htrace : WordTrace (prefixWord ++ tailWord_4289850) baseStart_4289850 baseEnd_4289850 := by
    simpa [prefixWord, tailWord_4289850, baseEnd_4289850] using wordTrace_append hprefix tailTrace_4289850
  have hstable : (prefixWord ++ tailWord_4289850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289850).length < 2 ^ (prefixWord ++ tailWord_4289850).sum := by decide
  have hdescent : baseEnd_4289850 < baseStart_4289850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289880 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4289880 : Nat := 118140960795 + 4289880 * 2 ^ 59
def prefixEnd_4289880 : Nat := 4983230072969 + 3 ^ 40 * 4289880 * 2
def baseEnd_4289880 : Nat := 2202770390109781058471207

theorem tailTrace_4289880 : CollatzResearch.WordTrace tailWord_4289880 prefixEnd_4289880 2202770390109781058471207 := by
  unfold tailWord_4289880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232388849252444009805547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104309851799003258679740729 78232388849252444009805547)
  ·
    refine ⟨117348583273878666014708321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78232388849252444009805547 117348583273878666014708321)
    ·
      refine ⟨88011437455408999511031241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117348583273878666014708321 88011437455408999511031241)
      ·
        refine ⟨66008578091556749633273431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88011437455408999511031241 66008578091556749633273431)
        ·
          refine ⟨99012867137335124449910147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66008578091556749633273431 99012867137335124449910147)
          ·
            refine ⟨148519300706002686674865221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99012867137335124449910147 148519300706002686674865221)
            ·
              refine ⟨27847368882375503751537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148519300706002686674865221 27847368882375503751537229)
              ·
                refine ⟨10442763330890813906826461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27847368882375503751537229 10442763330890813906826461)
                ·
                  refine ⟨3916036249084055215059923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10442763330890813906826461 3916036249084055215059923)
                  ·
                    refine ⟨5874054373626082822589885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3916036249084055215059923 5874054373626082822589885)
                    ·
                      refine ⟨2202770390109781058471207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874054373626082822589885 2202770390109781058471207)
                      ·
                        rfl

theorem cell23_4289880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4289880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289880 prefixEnd_4289880 := by exact prefixLift 4289880
  have htrace : WordTrace (prefixWord ++ tailWord_4289880) baseStart_4289880 baseEnd_4289880 := by
    simpa [prefixWord, tailWord_4289880, baseEnd_4289880] using wordTrace_append hprefix tailTrace_4289880
  have hstable : (prefixWord ++ tailWord_4289880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289880).length < 2 ^ (prefixWord ++ tailWord_4289880).sum := by decide
  have hdescent : baseEnd_4289880 < baseStart_4289880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289903 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_4289903 : Nat := 118140960795 + 4289903 * 2 ^ 59
def prefixEnd_4289903 : Nat := 4983230072969 + 3 ^ 40 * 4289903 * 2
def baseEnd_4289903 : Nat := 2202782200164834468483601

theorem tailTrace_4289903 : CollatzResearch.WordTrace tailWord_4289903 prefixEnd_4289903 2202782200164834468483601 := by
  unfold tailWord_4289903
  simp only [CollatzResearch.WordTrace]
  refine ⟨156465616577421562947698363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104310411051614375298465575 156465616577421562947698363)
  ·
    refine ⟨234698424866132344421547545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156465616577421562947698363 234698424866132344421547545)
    ·
      refine ⟨176023818649599258316160659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234698424866132344421547545 176023818649599258316160659)
      ·
        refine ⟨264035727974398887474240989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176023818649599258316160659 264035727974398887474240989)
        ·
          refine ⟨99013397990399582802840371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264035727974398887474240989 99013397990399582802840371)
          ·
            refine ⟨148520096985599374204260557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99013397990399582802840371 148520096985599374204260557)
            ·
              refine ⟨55695036369599765326597709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148520096985599374204260557 55695036369599765326597709)
              ·
                refine ⟨20885638638599911997474141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55695036369599765326597709 20885638638599911997474141)
                ·
                  refine ⟨7832114489474966999052803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20885638638599911997474141 7832114489474966999052803)
                  ·
                    refine ⟨11748171734212450498579205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7832114489474966999052803 11748171734212450498579205)
                    ·
                      refine ⟨2202782200164834468483601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11748171734212450498579205 2202782200164834468483601)
                      ·
                        rfl

theorem cell23_4289903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_4289903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289903 prefixEnd_4289903 := by exact prefixLift 4289903
  have htrace : WordTrace (prefixWord ++ tailWord_4289903) baseStart_4289903 baseEnd_4289903 := by
    simpa [prefixWord, tailWord_4289903, baseEnd_4289903] using wordTrace_append hprefix tailTrace_4289903
  have hstable : (prefixWord ++ tailWord_4289903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289903).length < 2 ^ (prefixWord ++ tailWord_4289903).sum := by decide
  have hdescent : baseEnd_4289903 < baseStart_4289903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289913 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_4289913 : Nat := 118140960795 + 4289913 * 2 ^ 59
def prefixEnd_4289913 : Nat := 4983230072969 + 3 ^ 40 * 4289913 * 2
def baseEnd_4289913 : Nat := 734262444990459809786185

theorem tailTrace_4289913 : CollatzResearch.WordTrace tailWord_4289913 prefixEnd_4289913 734262444990459809786185 := by
  unfold tailWord_4289913
  simp only [CollatzResearch.WordTrace]
  refine ⟨156465981307385334655562393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104310654204923556437041595 156465981307385334655562393)
  ·
    refine ⟨117349485980539000991671795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156465981307385334655562393 117349485980539000991671795)
    ·
      refine ⟨176024228970808501487507693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117349485980539000991671795 176024228970808501487507693)
      ·
        refine ⟨66009085864053188057815385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176024228970808501487507693 66009085864053188057815385)
        ·
          refine ⟨49506814398039891043361539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66009085864053188057815385 49506814398039891043361539)
          ·
            refine ⟨74260221597059836565042309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49506814398039891043361539 74260221597059836565042309)
            ·
              refine ⟨13923791549448719355945433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74260221597059836565042309 13923791549448719355945433)
              ·
                refine ⟨10442843662086539516959075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13923791549448719355945433 10442843662086539516959075)
                ·
                  refine ⟨15664265493129809275438613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10442843662086539516959075 15664265493129809275438613)
                  ·
                    refine ⟨734262444990459809786185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15664265493129809275438613 734262444990459809786185)
                    ·
                      rfl

theorem cell23_4289913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_4289913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289913 prefixEnd_4289913 := by exact prefixLift 4289913
  have htrace : WordTrace (prefixWord ++ tailWord_4289913) baseStart_4289913 baseEnd_4289913 := by
    simpa [prefixWord, tailWord_4289913, baseEnd_4289913] using wordTrace_append hprefix tailTrace_4289913
  have hstable : (prefixWord ++ tailWord_4289913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289913).length < 2 ^ (prefixWord ++ tailWord_4289913).sum := by decide
  have hdescent : baseEnd_4289913 < baseStart_4289913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289940 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4289940 : Nat := 118140960795 + 4289940 * 2 ^ 59
def prefixEnd_4289940 : Nat := 4983230072969 + 3 ^ 40 * 4289940 * 2
def baseEnd_4289940 : Nat := 2202801198949050823720931

theorem tailTrace_4289940 : CollatzResearch.WordTrace tailWord_4289940 prefixEnd_4289940 2202801198949050823720931 := by
  unfold tailWord_4289940
  simp only [CollatzResearch.WordTrace]
  refine ⟨78233483039143759133397637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104311310718858345511196849 78233483039143759133397637)
  ·
    refine ⟨14668778069839454837512057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78233483039143759133397637 14668778069839454837512057)
    ·
      refine ⟨11001583552379591128134043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14668778069839454837512057 11001583552379591128134043)
      ·
        refine ⟨16502375328569386692201065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11001583552379591128134043 16502375328569386692201065)
        ·
          refine ⟨12376781496427040019150799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16502375328569386692201065 12376781496427040019150799)
          ·
            refine ⟨18565172244640560028726199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12376781496427040019150799 18565172244640560028726199)
            ·
              refine ⟨27847758366960840043089299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18565172244640560028726199 27847758366960840043089299)
              ·
                refine ⟨41771637550441260064633949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27847758366960840043089299 41771637550441260064633949)
                ·
                  refine ⟨15664364081415472524237731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41771637550441260064633949 15664364081415472524237731)
                  ·
                    refine ⟨23496546122123208786356597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15664364081415472524237731 23496546122123208786356597)
                    ·
                      refine ⟨2202801198949050823720931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23496546122123208786356597 2202801198949050823720931)
                      ·
                        rfl

theorem cell23_4289940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4289940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289940 prefixEnd_4289940 := by exact prefixLift 4289940
  have htrace : WordTrace (prefixWord ++ tailWord_4289940) baseStart_4289940 baseEnd_4289940 := by
    simpa [prefixWord, tailWord_4289940, baseEnd_4289940] using wordTrace_append hprefix tailTrace_4289940
  have hstable : (prefixWord ++ tailWord_4289940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289940).length < 2 ^ (prefixWord ++ tailWord_4289940).sum := by decide
  have hdescent : baseEnd_4289940 < baseStart_4289940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289954 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4289954 : Nat := 118140960795 + 4289954 * 2 ^ 59
def prefixEnd_4289954 : Nat := 4983230072969 + 3 ^ 40 * 4289954 * 2
def baseEnd_4289954 : Nat := 2202808387678213768945867

theorem tailTrace_4289954 : CollatzResearch.WordTrace tailWord_4289954 prefixEnd_4289954 2202808387678213768945867 := by
  unfold tailWord_4289954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116869175059199664451229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104311651133491199105203277 39116869175059199664451229)
  ·
    refine ⟨14668825940647199874169211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39116869175059199664451229 14668825940647199874169211)
    ·
      refine ⟨22003238910970799811253817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14668825940647199874169211 22003238910970799811253817)
      ·
        refine ⟨16502429183228099858440363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22003238910970799811253817 16502429183228099858440363)
        ·
          refine ⟨24753643774842149787660545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16502429183228099858440363 24753643774842149787660545)
          ·
            refine ⟨18565232831131612340745409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24753643774842149787660545 18565232831131612340745409)
            ·
              refine ⟨13923924623348709255559057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18565232831131612340745409 13923924623348709255559057)
              ·
                refine ⟨10442943467511531941669293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13923924623348709255559057 10442943467511531941669293)
                ·
                  refine ⟨3916103800316824478125985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10442943467511531941669293 3916103800316824478125985)
                  ·
                    refine ⟨2937077850237618358594489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916103800316824478125985 2937077850237618358594489)
                    ·
                      refine ⟨2202808387678213768945867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937077850237618358594489 2202808387678213768945867)
                      ·
                        rfl

theorem cell23_4289954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4289954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289954 prefixEnd_4289954 := by exact prefixLift 4289954
  have htrace : WordTrace (prefixWord ++ tailWord_4289954) baseStart_4289954 baseEnd_4289954 := by
    simpa [prefixWord, tailWord_4289954, baseEnd_4289954] using wordTrace_append hprefix tailTrace_4289954
  have hstable : (prefixWord ++ tailWord_4289954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289954).length < 2 ^ (prefixWord ++ tailWord_4289954).sum := by decide
  have hdescent : baseEnd_4289954 < baseStart_4289954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4289993 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_4289993 : Nat := 118140960795 + 4289993 * 2 ^ 59
def prefixEnd_4289993 : Nat := 4983230072969 + 3 ^ 40 * 4289993 * 2
def baseEnd_4289993 : Nat := 2202828413423739116358187

theorem tailTrace_4289993 : CollatzResearch.WordTrace tailWord_4289993 prefixEnd_4289993 2202828413423739116358187 := by
  unfold tailWord_4289993
  simp only [CollatzResearch.WordTrace]
  refine ⟨156468899147095508318474633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104312599431397005545649755 156468899147095508318474633)
  ·
    refine ⟨117351674360321631238855975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156468899147095508318474633 117351674360321631238855975)
    ·
      refine ⟨176027511540482446858283963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117351674360321631238855975 176027511540482446858283963)
      ·
        refine ⟨264041267310723670287425945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176027511540482446858283963 264041267310723670287425945)
        ·
          refine ⟨198030950483042752715569459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264041267310723670287425945 198030950483042752715569459)
          ·
            refine ⟨297046425724564129073354189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198030950483042752715569459 297046425724564129073354189)
            ·
              refine ⟨111392409646711548402507821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297046425724564129073354189 111392409646711548402507821)
              ·
                refine ⟨41772153617516830650940433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111392409646711548402507821 41772153617516830650940433)
                ·
                  refine ⟨31329115213137622988205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41772153617516830650940433 31329115213137622988205325)
                  ·
                    refine ⟨11748418204926608620576997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31329115213137622988205325 11748418204926608620576997)
                    ·
                      refine ⟨2202828413423739116358187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11748418204926608620576997 2202828413423739116358187)
                      ·
                        rfl

theorem cell23_4289993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_4289993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4289993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4289993 prefixEnd_4289993 := by exact prefixLift 4289993
  have htrace : WordTrace (prefixWord ++ tailWord_4289993) baseStart_4289993 baseEnd_4289993 := by
    simpa [prefixWord, tailWord_4289993, baseEnd_4289993] using wordTrace_append hprefix tailTrace_4289993
  have hstable : (prefixWord ++ tailWord_4289993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4289993).length < 2 ^ (prefixWord ++ tailWord_4289993).sum := by decide
  have hdescent : baseEnd_4289993 < baseStart_4289993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4289993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290027 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 4, 2, 2]
def baseStart_4290027 : Nat := 118140960795 + 4290027 * 2 ^ 59
def prefixEnd_4290027 : Nat := 4983230072969 + 3 ^ 40 * 4290027 * 2
def baseEnd_4290027 : Nat := 2202845871765991983333031

theorem tailTrace_4290027 : CollatzResearch.WordTrace tailWord_4290027 prefixEnd_4290027 2202845871765991983333031 := by
  unfold tailWord_4290027
  simp only [CollatzResearch.WordTrace]
  refine ⟨156470139228972332125212335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104313426152648221416808223 156470139228972332125212335)
  ·
    refine ⟨234705208843458498187818503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156470139228972332125212335 234705208843458498187818503)
    ·
      refine ⟨352057813265187747281727755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234705208843458498187818503 352057813265187747281727755)
      ·
        refine ⟨528086719897781620922591633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352057813265187747281727755 528086719897781620922591633)
        ·
          refine ⟨396065039923336215691943725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528086719897781620922591633 396065039923336215691943725)
          ·
            refine ⟨148524389971251080884478897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396065039923336215691943725 148524389971251080884478897)
            ·
              refine ⟨111393292478438310663359173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148524389971251080884478897 111393292478438310663359173)
              ·
                refine ⟨20886242339707183249379845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111393292478438310663359173 20886242339707183249379845)
                ·
                  refine ⟨3916170438695096859258721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20886242339707183249379845 3916170438695096859258721)
                  ·
                    refine ⟨2937127829021322644444041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916170438695096859258721 2937127829021322644444041)
                    ·
                      refine ⟨2202845871765991983333031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937127829021322644444041 2202845871765991983333031)
                      ·
                        rfl

theorem cell23_4290027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2, 2].length) (baseStart_4290027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290027 prefixEnd_4290027 := by exact prefixLift 4290027
  have htrace : WordTrace (prefixWord ++ tailWord_4290027) baseStart_4290027 baseEnd_4290027 := by
    simpa [prefixWord, tailWord_4290027, baseEnd_4290027] using wordTrace_append hprefix tailTrace_4290027
  have hstable : (prefixWord ++ tailWord_4290027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290027).length < 2 ^ (prefixWord ++ tailWord_4290027).sum := by decide
  have hdescent : baseEnd_4290027 < baseStart_4290027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290030 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4290030 : Nat := 118140960795 + 4290030 * 2 ^ 59
def prefixEnd_4290030 : Nat := 4983230072969 + 3 ^ 40 * 4290030 * 2
def baseEnd_4290030 : Nat := 2202847412207955471595517

theorem tailTrace_4290030 : CollatzResearch.WordTrace tailWord_4290030 prefixEnd_4290030 2202847412207955471595517 := by
  unfold tailWord_4290030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19558781080995182954696443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104313499098640975758381029 19558781080995182954696443)
  ·
    refine ⟨29338171621492774432044665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19558781080995182954696443 29338171621492774432044665)
    ·
      refine ⟨22003628716119580824033499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29338171621492774432044665 22003628716119580824033499)
      ·
        refine ⟨33005443074179371236050249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22003628716119580824033499 33005443074179371236050249)
        ·
          refine ⟨24754082305634528427037687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33005443074179371236050249 24754082305634528427037687)
          ·
            refine ⟨37131123458451792640556531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24754082305634528427037687 37131123458451792640556531)
            ·
              refine ⟨55696685187677688960834797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37131123458451792640556531 55696685187677688960834797)
              ·
                refine ⟨20886256945379133360313049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55696685187677688960834797 20886256945379133360313049)
                ·
                  refine ⟨15664692709034350020234787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20886256945379133360313049 15664692709034350020234787)
                  ·
                    refine ⟨23497039063551525030352181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15664692709034350020234787 23497039063551525030352181)
                    ·
                      refine ⟨2202847412207955471595517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23497039063551525030352181 2202847412207955471595517)
                      ·
                        rfl

theorem cell23_4290030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4290030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290030 prefixEnd_4290030 := by exact prefixLift 4290030
  have htrace : WordTrace (prefixWord ++ tailWord_4290030) baseStart_4290030 baseEnd_4290030 := by
    simpa [prefixWord, tailWord_4290030, baseEnd_4290030] using wordTrace_append hprefix tailTrace_4290030
  have hstable : (prefixWord ++ tailWord_4290030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290030).length < 2 ^ (prefixWord ++ tailWord_4290030).sum := by decide
  have hdescent : baseEnd_4290030 < baseStart_4290030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290044 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_4290044 : Nat := 118140960795 + 4290044 * 2 ^ 59
def prefixEnd_4290044 : Nat := 4983230072969 + 3 ^ 40 * 4290044 * 2
def baseEnd_4290044 : Nat := 2202854600937118416820453

theorem tailTrace_4290044 : CollatzResearch.WordTrace tailWord_4290044 prefixEnd_4290044 2202854600937118416820453 := by
  unfold tailWord_4290044
  simp only [CollatzResearch.WordTrace]
  refine ⟨78235379634955372014290593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104313839513273829352387457 78235379634955372014290593)
  ·
    refine ⟨58676534726216529010717945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78235379634955372014290593 58676534726216529010717945)
    ·
      refine ⟨44007401044662396758038459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58676534726216529010717945 44007401044662396758038459)
      ·
        refine ⟨66011101566993595137057689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44007401044662396758038459 66011101566993595137057689)
        ·
          refine ⟨49508326175245196352793267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66011101566993595137057689 49508326175245196352793267)
          ·
            refine ⟨74262489262867794529189901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49508326175245196352793267 74262489262867794529189901)
            ·
              refine ⟨27848433473575422948446213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74262489262867794529189901 27848433473575422948446213)
              ·
                refine ⟨5221581276295391802833665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27848433473575422948446213 5221581276295391802833665)
                ·
                  refine ⟨3916185957221543852125249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221581276295391802833665 3916185957221543852125249)
                  ·
                    refine ⟨2937139467916157889093937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916185957221543852125249 2937139467916157889093937)
                    ·
                      refine ⟨2202854600937118416820453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937139467916157889093937 2202854600937118416820453)
                      ·
                        rfl

theorem cell23_4290044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_4290044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290044 prefixEnd_4290044 := by exact prefixLift 4290044
  have htrace : WordTrace (prefixWord ++ tailWord_4290044) baseStart_4290044 baseEnd_4290044 := by
    simpa [prefixWord, tailWord_4290044, baseEnd_4290044] using wordTrace_append hprefix tailTrace_4290044
  have hstable : (prefixWord ++ tailWord_4290044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290044).length < 2 ^ (prefixWord ++ tailWord_4290044).sum := by decide
  have hdescent : baseEnd_4290044 < baseStart_4290044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290053 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4290053 : Nat := 118140960795 + 4290053 * 2 ^ 59
def prefixEnd_4290053 : Nat := 4983230072969 + 3 ^ 40 * 4290053 * 2
def baseEnd_4290053 : Nat := 2202859222263008881607911

theorem tailTrace_4290053 : CollatzResearch.WordTrace tailWord_4290053 prefixEnd_4290053 2202859222263008881607911 := by
  unfold tailWord_4290053
  simp only [CollatzResearch.WordTrace]
  refine ⟨156471087526878138565658813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104314058351252092377105875 156471087526878138565658813)
  ·
    refine ⟨58676657822579301962122055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156471087526878138565658813 58676657822579301962122055)
    ·
      refine ⟨88014986733868952943183083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58676657822579301962122055 88014986733868952943183083)
      ·
        refine ⟨132022480100803429414774625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88014986733868952943183083 132022480100803429414774625)
        ·
          refine ⟨99016860075602572061080969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132022480100803429414774625 99016860075602572061080969)
          ·
            refine ⟨74262645056701929045810727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99016860075602572061080969 74262645056701929045810727)
            ·
              refine ⟨111393967585052893568716091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74262645056701929045810727 111393967585052893568716091)
              ·
                refine ⟨167090951377579340353074137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111393967585052893568716091 167090951377579340353074137)
                ·
                  refine ⟨125318213533184505264805603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167090951377579340353074137 125318213533184505264805603)
                  ·
                    refine ⟨187977320299776757897208405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125318213533184505264805603 187977320299776757897208405)
                    ·
                      refine ⟨2202859222263008881607911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187977320299776757897208405 2202859222263008881607911)
                      ·
                        rfl

theorem cell23_4290053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4290053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290053 prefixEnd_4290053 := by exact prefixLift 4290053
  have htrace : WordTrace (prefixWord ++ tailWord_4290053) baseStart_4290053 baseEnd_4290053 := by
    simpa [prefixWord, tailWord_4290053, baseEnd_4290053] using wordTrace_append hprefix tailTrace_4290053
  have hstable : (prefixWord ++ tailWord_4290053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290053).length < 2 ^ (prefixWord ++ tailWord_4290053).sum := by decide
  have hdescent : baseEnd_4290053 < baseStart_4290053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290117 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_4290117 : Nat := 118140960795 + 4290117 * 2 ^ 59
def prefixEnd_4290117 : Nat := 4983230072969 + 3 ^ 40 * 4290117 * 2
def baseEnd_4290117 : Nat := 2202892085024896631207617

theorem tailTrace_4290117 : CollatzResearch.WordTrace tailWord_4290117 prefixEnd_4290117 2202892085024896631207617 := by
  unfold tailWord_4290117
  simp only [CollatzResearch.WordTrace]
  refine ⟨156473421798646277495988605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104315614532430851663992403 156473421798646277495988605)
  ·
    refine ⟨58677533174492354060995727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156473421798646277495988605 58677533174492354060995727)
    ·
      refine ⟨88016299761738531091493591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58677533174492354060995727 88016299761738531091493591)
      ·
        refine ⟨132024449642607796637240387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88016299761738531091493591 132024449642607796637240387)
        ·
          refine ⟨198036674463911694955860581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132024449642607796637240387 198036674463911694955860581)
          ·
            refine ⟨37131876461983442804223859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198036674463911694955860581 37131876461983442804223859)
            ·
              refine ⟨55697814692975164206335789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37131876461983442804223859 55697814692975164206335789)
              ·
                refine ⟨20886680509865686577375921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55697814692975164206335789 20886680509865686577375921)
                ·
                  refine ⟨15665010382399264933031941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20886680509865686577375921 15665010382399264933031941)
                  ·
                    refine ⟨2937189446699862174943489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15665010382399264933031941 2937189446699862174943489)
                    ·
                      refine ⟨2202892085024896631207617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937189446699862174943489 2202892085024896631207617)
                      ·
                        rfl

theorem cell23_4290117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_4290117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290117 prefixEnd_4290117 := by exact prefixLift 4290117
  have htrace : WordTrace (prefixWord ++ tailWord_4290117) baseStart_4290117 baseEnd_4290117 := by
    simpa [prefixWord, tailWord_4290117, baseEnd_4290117] using wordTrace_append hprefix tailTrace_4290117
  have hstable : (prefixWord ++ tailWord_4290117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290117).length < 2 ^ (prefixWord ++ tailWord_4290117).sum := by decide
  have hdescent : baseEnd_4290117 < baseStart_4290117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290154 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4290154 : Nat := 118140960795 + 4290154 * 2 ^ 59
def prefixEnd_4290154 : Nat := 4983230072969 + 3 ^ 40 * 4290154 * 2
def baseEnd_4290154 : Nat := 2202911083809112986444947

theorem tailTrace_4290154 : CollatzResearch.WordTrace tailWord_4290154 prefixEnd_4290154 2202911083809112986444947 := by
  unfold tailWord_4290154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39118692824878058203771379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104316514199674821876723677 39118692824878058203771379)
  ·
    refine ⟨58678039237317087305657069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39118692824878058203771379 58678039237317087305657069)
    ·
      refine ⟨22004264713993907739621401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58678039237317087305657069 22004264713993907739621401)
      ·
        refine ⟨16503198535495430804716051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22004264713993907739621401 16503198535495430804716051)
        ·
          refine ⟨24754797803243146207074077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16503198535495430804716051 24754797803243146207074077)
          ·
            refine ⟨9283049176216179827652779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24754797803243146207074077 9283049176216179827652779)
            ·
              refine ⟨13924573764324269741479169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9283049176216179827652779 13924573764324269741479169)
              ·
                refine ⟨10443430323243202306109377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13924573764324269741479169 10443430323243202306109377)
                ·
                  refine ⟨7832572742432401729582033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10443430323243202306109377 7832572742432401729582033)
                  ·
                    refine ⟨5874429556824301297186525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7832572742432401729582033 5874429556824301297186525)
                    ·
                      refine ⟨2202911083809112986444947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874429556824301297186525 2202911083809112986444947)
                      ·
                        rfl

theorem cell23_4290154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4290154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290154 prefixEnd_4290154 := by exact prefixLift 4290154
  have htrace : WordTrace (prefixWord ++ tailWord_4290154) baseStart_4290154 baseEnd_4290154 := by
    simpa [prefixWord, tailWord_4290154, baseEnd_4290154] using wordTrace_append hprefix tailTrace_4290154
  have hstable : (prefixWord ++ tailWord_4290154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290154).length < 2 ^ (prefixWord ++ tailWord_4290154).sum := by decide
  have hdescent : baseEnd_4290154 < baseStart_4290154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290227 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3]
def baseStart_4290227 : Nat := 118140960795 + 4290227 * 2 ^ 59
def prefixEnd_4290227 : Nat := 4983230072969 + 3 ^ 40 * 4290227 * 2
def baseEnd_4290227 : Nat := 2202948567896891200832111

theorem tailTrace_4290227 : CollatzResearch.WordTrace tailWord_4290227 prefixEnd_4290227 2202948567896891200832111 := by
  unfold tailWord_4290227
  simp only [CollatzResearch.WordTrace]
  refine ⟨156477433828247766282492935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104318289218831844188328623 156477433828247766282492935)
  ·
    refine ⟨234716150742371649423739403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156477433828247766282492935 234716150742371649423739403)
    ·
      refine ⟨352074226113557474135609105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234716150742371649423739403 352074226113557474135609105)
      ·
        refine ⟨264055669585168105601706829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352074226113557474135609105 264055669585168105601706829)
        ·
          refine ⟨99020876094438039600640061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264055669585168105601706829 99020876094438039600640061)
          ·
            refine ⟨37132828535414264850240023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99020876094438039600640061 37132828535414264850240023)
            ·
              refine ⟨55699242803121397275360035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37132828535414264850240023 55699242803121397275360035)
              ·
                refine ⟨83548864204682095913040053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55699242803121397275360035 83548864204682095913040053)
                ·
                  refine ⟨7832706019188946491847505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83548864204682095913040053 7832706019188946491847505)
                  ·
                    refine ⟨5874529514391709868885629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7832706019188946491847505 5874529514391709868885629)
                    ·
                      refine ⟨2202948567896891200832111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874529514391709868885629 2202948567896891200832111)
                      ·
                        rfl

theorem cell23_4290227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_4290227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290227 prefixEnd_4290227 := by exact prefixLift 4290227
  have htrace : WordTrace (prefixWord ++ tailWord_4290227) baseStart_4290227 baseEnd_4290227 := by
    simpa [prefixWord, tailWord_4290227, baseEnd_4290227] using wordTrace_append hprefix tailTrace_4290227
  have hstable : (prefixWord ++ tailWord_4290227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290227).length < 2 ^ (prefixWord ++ tailWord_4290227).sum := by decide
  have hdescent : baseEnd_4290227 < baseStart_4290227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290234 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_4290234 : Nat := 118140960795 + 4290234 * 2 ^ 59
def prefixEnd_4290234 : Nat := 4983230072969 + 3 ^ 40 * 4290234 * 2
def baseEnd_4290234 : Nat := 734317387420490891148193

theorem tailTrace_4290234 : CollatzResearch.WordTrace tailWord_4290234 prefixEnd_4290234 734317387420490891148193 := by
  unfold tailWord_4290234
  simp only [CollatzResearch.WordTrace]
  refine ⟨39119422284805601619499439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104318459426148270985331837 39119422284805601619499439)
  ·
    refine ⟨58679133427208402429249159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39119422284805601619499439 58679133427208402429249159)
    ·
      refine ⟨88018700140812603643873739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58679133427208402429249159 88018700140812603643873739)
      ·
        refine ⟨132028050211218905465810609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88018700140812603643873739 132028050211218905465810609)
        ·
          refine ⟨99021037658414179099357957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132028050211218905465810609 99021037658414179099357957)
          ·
            refine ⟨18566444560952658581129617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99021037658414179099357957 18566444560952658581129617)
            ·
              refine ⟨13924833420714493935847213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18566444560952658581129617 13924833420714493935847213)
              ·
                refine ⟨5221812532767935225942705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13924833420714493935847213 5221812532767935225942705)
                ·
                  refine ⟨3916359399575951419457029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221812532767935225942705 3916359399575951419457029)
                  ·
                    refine ⟨734317387420490891148193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3916359399575951419457029 734317387420490891148193)
                    ·
                      rfl

theorem cell23_4290234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_4290234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290234 prefixEnd_4290234 := by exact prefixLift 4290234
  have htrace : WordTrace (prefixWord ++ tailWord_4290234) baseStart_4290234 baseEnd_4290234 := by
    simpa [prefixWord, tailWord_4290234, baseEnd_4290234] using wordTrace_append hprefix tailTrace_4290234
  have hstable : (prefixWord ++ tailWord_4290234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290234).length < 2 ^ (prefixWord ++ tailWord_4290234).sum := by decide
  have hdescent : baseEnd_4290234 < baseStart_4290234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290244 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4290244 : Nat := 118140960795 + 4290244 * 2 ^ 59
def prefixEnd_4290244 : Nat := 4983230072969 + 3 ^ 40 * 4290244 * 2
def baseEnd_4290244 : Nat := 2202957297068017634319533

theorem tailTrace_4290244 : CollatzResearch.WordTrace tailWord_4290244 prefixEnd_4290244 2202957297068017634319533 := by
  unfold tailWord_4290244
  simp only [CollatzResearch.WordTrace]
  refine ⟨78239026934593089092930893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104318702579457452123907857 78239026934593089092930893)
  ·
    refine ⟨29339635100472408409849085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78239026934593089092930893 29339635100472408409849085)
    ·
      refine ⟨11002363162677153153693407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29339635100472408409849085 11002363162677153153693407)
      ·
        refine ⟨16503544744015729730540111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002363162677153153693407 16503544744015729730540111)
        ·
          refine ⟨24755317116023594595810167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16503544744015729730540111 24755317116023594595810167)
          ·
            refine ⟨37132975674035391893715251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24755317116023594595810167 37132975674035391893715251)
            ·
              refine ⟨55699463511053087840572877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37132975674035391893715251 55699463511053087840572877)
              ·
                refine ⟨20887298816644907940214829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55699463511053087840572877 20887298816644907940214829)
                ·
                  refine ⟨7832737056241840477580561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20887298816644907940214829 7832737056241840477580561)
                  ·
                    refine ⟨5874552792181380358185421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7832737056241840477580561 5874552792181380358185421)
                    ·
                      refine ⟨2202957297068017634319533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874552792181380358185421 2202957297068017634319533)
                      ·
                        rfl

theorem cell23_4290244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4290244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290244 prefixEnd_4290244 := by exact prefixLift 4290244
  have htrace : WordTrace (prefixWord ++ tailWord_4290244) baseStart_4290244 baseEnd_4290244 := by
    simpa [prefixWord, tailWord_4290244, baseEnd_4290244] using wordTrace_append hprefix tailTrace_4290244
  have hstable : (prefixWord ++ tailWord_4290244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290244).length < 2 ^ (prefixWord ++ tailWord_4290244).sum := by decide
  have hdescent : baseEnd_4290244 < baseStart_4290244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290247 : List Nat := [1, 1, 4, 1, 1, 1, 7, 7]
def baseStart_4290247 : Nat := 118140960795 + 4290247 * 2 ^ 59
def prefixEnd_4290247 : Nat := 4983230072969 + 3 ^ 40 * 4290247 * 2
def baseEnd_4290247 : Nat := 81591068055925226762297

theorem tailTrace_4290247 : CollatzResearch.WordTrace tailWord_4290247 prefixEnd_4290247 81591068055925226762297 := by
  unfold tailWord_4290247
  simp only [CollatzResearch.WordTrace]
  refine ⟨156478163288175309698220995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104318775525450206465480663 156478163288175309698220995)
  ·
    refine ⟨234717244932262964547331493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156478163288175309698220995 234717244932262964547331493)
    ·
      refine ⟨44009483424799305852624655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234717244932262964547331493 44009483424799305852624655)
      ·
        refine ⟨66014225137198958778936983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44009483424799305852624655 66014225137198958778936983)
        ·
          refine ⟨99021337705798438168405475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66014225137198958778936983 99021337705798438168405475)
          ·
            refine ⟨148532006558697657252608213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99021337705798438168405475 148532006558697657252608213)
            ·
              refine ⟨3481218903719476341858005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148532006558697657252608213 3481218903719476341858005)
              ·
                refine ⟨81591068055925226762297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3481218903719476341858005 81591068055925226762297)
                ·
                  rfl

theorem cell23_4290247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 7].length) (baseStart_4290247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290247 prefixEnd_4290247 := by exact prefixLift 4290247
  have htrace : WordTrace (prefixWord ++ tailWord_4290247) baseStart_4290247 baseEnd_4290247 := by
    simpa [prefixWord, tailWord_4290247, baseEnd_4290247] using wordTrace_append hprefix tailTrace_4290247
  have hstable : (prefixWord ++ tailWord_4290247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290247).length < 2 ^ (prefixWord ++ tailWord_4290247).sum := by decide
  have hdescent : baseEnd_4290247 < baseStart_4290247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290258 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4290258 : Nat := 118140960795 + 4290258 * 2 ^ 59
def prefixEnd_4290258 : Nat := 4983230072969 + 3 ^ 40 * 4290258 * 2
def baseEnd_4290258 : Nat := 2202964485797180579544469

theorem tailTrace_4290258 : CollatzResearch.WordTrace tailWord_4290258 prefixEnd_4290258 2202964485797180579544469 := by
  unfold tailWord_4290258
  simp only [CollatzResearch.WordTrace]
  refine ⟨39119641122783864644217857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104319042994090305717914285 39119641122783864644217857)
  ·
    refine ⟨29339730842087898483163393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39119641122783864644217857 29339730842087898483163393)
    ·
      refine ⟨22004798131565923862372545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29339730842087898483163393 22004798131565923862372545)
      ·
        refine ⟨16503598598674442896779409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22004798131565923862372545 16503598598674442896779409)
        ·
          refine ⟨12377698949005832172584557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16503598598674442896779409 12377698949005832172584557)
          ·
            refine ⟨4641637105877187064719209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12377698949005832172584557 4641637105877187064719209)
            ·
              refine ⟨3481227829407890298539407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641637105877187064719209 3481227829407890298539407)
              ·
                refine ⟨5221841744111835447809111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481227829407890298539407 5221841744111835447809111)
                ·
                  refine ⟨7832762616167753171713667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5221841744111835447809111 7832762616167753171713667)
                  ·
                    refine ⟨11749143924251629757570501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7832762616167753171713667 11749143924251629757570501)
                    ·
                      refine ⟨2202964485797180579544469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11749143924251629757570501 2202964485797180579544469)
                      ·
                        rfl

theorem cell23_4290258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4290258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290258 prefixEnd_4290258 := by exact prefixLift 4290258
  have htrace : WordTrace (prefixWord ++ tailWord_4290258) baseStart_4290258 baseEnd_4290258 := by
    simpa [prefixWord, tailWord_4290258, baseEnd_4290258] using wordTrace_append hprefix tailTrace_4290258
  have hstable : (prefixWord ++ tailWord_4290258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290258).length < 2 ^ (prefixWord ++ tailWord_4290258).sum := by decide
  have hdescent : baseEnd_4290258 < baseStart_4290258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290284 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_4290284 : Nat := 118140960795 + 4290284 * 2 ^ 59
def prefixEnd_4290284 : Nat := 4983230072969 + 3 ^ 40 * 4290284 * 2
def baseEnd_4290284 : Nat := 2202977836294197477819349

theorem tailTrace_4290284 : CollatzResearch.WordTrace tailWord_4290284 prefixEnd_4290284 2202977836294197477819349 := by
  unfold tailWord_4290284
  simp only [CollatzResearch.WordTrace]
  refine ⟨78239756394520632508658953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104319675192694176678211937 78239756394520632508658953)
  ·
    refine ⟨58679817295890474381494215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78239756394520632508658953 58679817295890474381494215)
    ·
      refine ⟨88019725943835711572241323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58679817295890474381494215 88019725943835711572241323)
      ·
        refine ⟨132029588915753567358361985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88019725943835711572241323 132029588915753567358361985)
        ·
          refine ⟨99022191686815175518771489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132029588915753567358361985 99022191686815175518771489)
          ·
            refine ⟨74266643765111381639078617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99022191686815175518771489 74266643765111381639078617)
            ·
              refine ⟨55699982823833536229308963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74266643765111381639078617 55699982823833536229308963)
              ·
                refine ⟨83549974235750304343963445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55699982823833536229308963 83549974235750304343963445)
                ·
                  refine ⟨7832810084601591032246573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83549974235750304343963445 7832810084601591032246573)
                  ·
                    refine ⟨2937303781725596637092465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7832810084601591032246573 2937303781725596637092465)
                    ·
                      refine ⟨2202977836294197477819349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937303781725596637092465 2202977836294197477819349)
                      ·
                        rfl

theorem cell23_4290284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_4290284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290284 prefixEnd_4290284 := by exact prefixLift 4290284
  have htrace : WordTrace (prefixWord ++ tailWord_4290284) baseStart_4290284 baseEnd_4290284 := by
    simpa [prefixWord, tailWord_4290284, baseEnd_4290284] using wordTrace_append hprefix tailTrace_4290284
  have hstable : (prefixWord ++ tailWord_4290284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290284).length < 2 ^ (prefixWord ++ tailWord_4290284).sum := by decide
  have hdescent : baseEnd_4290284 < baseStart_4290284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290348 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_4290348 : Nat := 118140960795 + 4290348 * 2 ^ 59
def prefixEnd_4290348 : Nat := 4983230072969 + 3 ^ 40 * 4290348 * 2
def baseEnd_4290348 : Nat := 2203010699056085227419055

theorem tailTrace_4290348 : CollatzResearch.WordTrace tailWord_4290348 prefixEnd_4290348 2203010699056085227419055 := by
  unfold tailWord_4290348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78240923530404701973823849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104321231373872935965098465 78240923530404701973823849)
  ·
    refine ⟨58680692647803526480367887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78240923530404701973823849 58680692647803526480367887)
    ·
      refine ⟨88021038971705289720551831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58680692647803526480367887 88021038971705289720551831)
      ·
        refine ⟨132031558457557934580827747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88021038971705289720551831 132031558457557934580827747)
        ·
          refine ⟨198047337686336901871241621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132031558457557934580827747 198047337686336901871241621)
          ·
            refine ⟨9283468954047042275214451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 198047337686336901871241621 9283468954047042275214451)
            ·
              refine ⟨13925203431070563412821677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9283468954047042275214451 13925203431070563412821677)
              ·
                refine ⟨5221951286651461279808129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13925203431070563412821677 5221951286651461279808129)
                ·
                  refine ⟨3916463464988595959856097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221951286651461279808129 3916463464988595959856097)
                  ·
                    refine ⟨2937347598741446969892073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916463464988595959856097 2937347598741446969892073)
                    ·
                      refine ⟨2203010699056085227419055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937347598741446969892073 2203010699056085227419055)
                      ·
                        rfl

theorem cell23_4290348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_4290348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290348 prefixEnd_4290348 := by exact prefixLift 4290348
  have htrace : WordTrace (prefixWord ++ tailWord_4290348) baseStart_4290348 baseEnd_4290348 := by
    simpa [prefixWord, tailWord_4290348, baseEnd_4290348] using wordTrace_append hprefix tailTrace_4290348
  have hstable : (prefixWord ++ tailWord_4290348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290348).length < 2 ^ (prefixWord ++ tailWord_4290348).sum := by decide
  have hdescent : baseEnd_4290348 < baseStart_4290348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290377 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_4290377 : Nat := 118140960795 + 4290377 * 2 ^ 59
def prefixEnd_4290377 : Nat := 4983230072969 + 3 ^ 40 * 4290377 * 2
def baseEnd_4290377 : Nat := 2203025589995065613956421

theorem tailTrace_4290377 : CollatzResearch.WordTrace tailWord_4290377 prefixEnd_4290377 2203025589995065613956421 := by
  unfold tailWord_4290377
  simp only [CollatzResearch.WordTrace]
  refine ⟨156482904777704341900453385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104321936518469561266968923 156482904777704341900453385)
  ·
    refine ⟨117362178583278256425340039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156482904777704341900453385 117362178583278256425340039)
    ·
      refine ⟨176043267874917384638010059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117362178583278256425340039 176043267874917384638010059)
      ·
        refine ⟨264064901812376076957015089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176043267874917384638010059 264064901812376076957015089)
        ·
          refine ⟨198048676359282057717761317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264064901812376076957015089 198048676359282057717761317)
          ·
            refine ⟨37134126817365385822080247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198048676359282057717761317 37134126817365385822080247)
            ·
              refine ⟨55701190226048078733120371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37134126817365385822080247 55701190226048078733120371)
              ·
                refine ⟨83551785339072118099680557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55701190226048078733120371 83551785339072118099680557)
                ·
                  refine ⟨31331919502152044287380209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83551785339072118099680557 31331919502152044287380209)
                  ·
                    refine ⟨23498939626614033215535157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31331919502152044287380209 23498939626614033215535157)
                    ·
                      refine ⟨2203025589995065613956421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23498939626614033215535157 2203025589995065613956421)
                      ·
                        rfl

theorem cell23_4290377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_4290377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290377 prefixEnd_4290377 := by exact prefixLift 4290377
  have htrace : WordTrace (prefixWord ++ tailWord_4290377) baseStart_4290377 baseEnd_4290377 := by
    simpa [prefixWord, tailWord_4290377, baseEnd_4290377] using wordTrace_append hprefix tailTrace_4290377
  have hstable : (prefixWord ++ tailWord_4290377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290377).length < 2 ^ (prefixWord ++ tailWord_4290377).sum := by decide
  have hdescent : baseEnd_4290377 < baseStart_4290377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290387 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_4290387 : Nat := 118140960795 + 4290387 * 2 ^ 59
def prefixEnd_4290387 : Nat := 4983230072969 + 3 ^ 40 * 4290387 * 2
def baseEnd_4290387 : Nat := 2203030724801610574831375

theorem tailTrace_4290387 : CollatzResearch.WordTrace tailWord_4290387 prefixEnd_4290387 2203030724801610574831375 := by
  unfold tailWord_4290387
  simp only [CollatzResearch.WordTrace]
  refine ⟨156483269507668113608317415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104322179671778742405544943 156483269507668113608317415)
  ·
    refine ⟨234724904261502170412476123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156483269507668113608317415 234724904261502170412476123)
    ·
      refine ⟨352087356392253255618714185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234724904261502170412476123 352087356392253255618714185)
      ·
        refine ⟨264065517294189941714035639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352087356392253255618714185 264065517294189941714035639)
        ·
          refine ⟨396098275941284912571053459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264065517294189941714035639 396098275941284912571053459)
          ·
            refine ⟨594147413911927368856580189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396098275941284912571053459 594147413911927368856580189)
            ·
              refine ⟨222805280216972763321217571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594147413911927368856580189 222805280216972763321217571)
              ·
                refine ⟨334207920325459144981826357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222805280216972763321217571 334207920325459144981826357)
                ·
                  refine ⟨31331992530511794842046221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334207920325459144981826357 31331992530511794842046221)
                  ·
                    refine ⟨11749497198941923065767333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31331992530511794842046221 11749497198941923065767333)
                    ·
                      refine ⟨2203030724801610574831375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11749497198941923065767333 2203030724801610574831375)
                      ·
                        rfl

theorem cell23_4290387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_4290387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290387 prefixEnd_4290387 := by exact prefixLift 4290387
  have htrace : WordTrace (prefixWord ++ tailWord_4290387) baseStart_4290387 baseEnd_4290387 := by
    simpa [prefixWord, tailWord_4290387, baseEnd_4290387] using wordTrace_append hprefix tailTrace_4290387
  have hstable : (prefixWord ++ tailWord_4290387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290387).length < 2 ^ (prefixWord ++ tailWord_4290387).sum := by decide
  have hdescent : baseEnd_4290387 < baseStart_4290387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290388 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 5]
def baseStart_4290388 : Nat := 118140960795 + 4290388 * 2 ^ 59
def prefixEnd_4290388 : Nat := 4983230072969 + 3 ^ 40 * 4290388 * 2
def baseEnd_4290388 : Nat := 244781248698029452324319

theorem tailTrace_4290388 : CollatzResearch.WordTrace tailWord_4290388 prefixEnd_4290388 244781248698029452324319 := by
  unfold tailWord_4290388
  simp only [CollatzResearch.WordTrace]
  refine ⟨78241652990332245389551909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104322203987109660519402545 78241652990332245389551909)
  ·
    refine ⟨14670309935687296010540983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78241652990332245389551909 14670309935687296010540983)
    ·
      refine ⟨22005464903530944015811475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14670309935687296010540983 22005464903530944015811475)
      ·
        refine ⟨33008197355296416023717213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22005464903530944015811475 33008197355296416023717213)
        ·
          refine ⟨12378074008236156008893955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33008197355296416023717213 12378074008236156008893955)
          ·
            refine ⟨18567111012354234013340933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12378074008236156008893955 18567111012354234013340933)
            ·
              refine ⟨3481333314816418877501425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18567111012354234013340933 3481333314816418877501425)
              ·
                refine ⟨2610999986112314158126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481333314816418877501425 2610999986112314158126069)
                ·
                  refine ⟨244781248698029452324319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610999986112314158126069 244781248698029452324319)
                  ·
                    rfl

theorem cell23_4290388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_4290388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290388 prefixEnd_4290388 := by exact prefixLift 4290388
  have htrace : WordTrace (prefixWord ++ tailWord_4290388) baseStart_4290388 baseEnd_4290388 := by
    simpa [prefixWord, tailWord_4290388, baseEnd_4290388] using wordTrace_append hprefix tailTrace_4290388
  have hstable : (prefixWord ++ tailWord_4290388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290388).length < 2 ^ (prefixWord ++ tailWord_4290388).sum := by decide
  have hdescent : baseEnd_4290388 < baseStart_4290388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290421 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4290421 : Nat := 118140960795 + 4290421 * 2 ^ 59
def prefixEnd_4290421 : Nat := 4983230072969 + 3 ^ 40 * 4290421 * 2
def baseEnd_4290421 : Nat := 2203048183143863441806219

theorem tailTrace_4290421 : CollatzResearch.WordTrace tailWord_4290421 prefixEnd_4290421 2203048183143863441806219 := by
  unfold tailWord_4290421
  simp only [CollatzResearch.WordTrace]
  refine ⟨156484509589544937415055117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104323006393029958276703411 156484509589544937415055117)
  ·
    refine ⟨58681691096079351530645669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156484509589544937415055117 58681691096079351530645669)
    ·
      refine ⟨11002817080514878411996063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58681691096079351530645669 11002817080514878411996063)
      ·
        refine ⟨16504225620772317617994095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002817080514878411996063 16504225620772317617994095)
        ·
          refine ⟨24756338431158476426991143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16504225620772317617994095 24756338431158476426991143)
          ·
            refine ⟨37134507646737714640486715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24756338431158476426991143 37134507646737714640486715)
            ·
              refine ⟨55701761470106571960730073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37134507646737714640486715 55701761470106571960730073)
              ·
                refine ⟨41776321102579928970547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55701761470106571960730073 41776321102579928970547555)
                ·
                  refine ⟨62664481653869893455821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41776321102579928970547555 62664481653869893455821333)
                  ·
                    refine ⟨2937397577525151255741625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62664481653869893455821333 2937397577525151255741625)
                    ·
                      refine ⟨2203048183143863441806219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937397577525151255741625 2203048183143863441806219)
                      ·
                        rfl

theorem cell23_4290421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4290421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290421 prefixEnd_4290421 := by exact prefixLift 4290421
  have htrace : WordTrace (prefixWord ++ tailWord_4290421) baseStart_4290421 baseEnd_4290421 := by
    simpa [prefixWord, tailWord_4290421, baseEnd_4290421] using wordTrace_append hprefix tailTrace_4290421
  have hstable : (prefixWord ++ tailWord_4290421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290421).length < 2 ^ (prefixWord ++ tailWord_4290421).sum := by decide
  have hdescent : baseEnd_4290421 < baseStart_4290421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290427 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 8]
def baseStart_4290427 : Nat := 118140960795 + 4290427 * 2 ^ 59
def prefixEnd_4290427 : Nat := 4983230072969 + 3 ^ 40 * 4290427 * 2
def baseEnd_4290427 : Nat := 244783473780865602036799

theorem tailTrace_4290427 : CollatzResearch.WordTrace tailWord_4290427 prefixEnd_4290427 244783473780865602036799 := by
  unfold tailWord_4290427
  simp only [CollatzResearch.WordTrace]
  refine ⟨156484728427523200439773535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104323152285015466959849023 156484728427523200439773535)
  ·
    refine ⟨234727092641284800659660303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156484728427523200439773535 234727092641284800659660303)
    ·
      refine ⟨352090638961927200989490455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234727092641284800659660303 352090638961927200989490455)
      ·
        refine ⟨528135958442890801484235683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352090638961927200989490455 528135958442890801484235683)
        ·
          refine ⟨792203937664336202226353525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528135958442890801484235683 792203937664336202226353525)
          ·
            refine ⟨74269119156031518958720643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 792203937664336202226353525 74269119156031518958720643)
            ·
              refine ⟨111403678734047278438080965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74269119156031518958720643 111403678734047278438080965)
              ·
                refine ⟨20888189762633864707140181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111403678734047278438080965 20888189762633864707140181)
                ·
                  refine ⟨244783473780865602036799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20888189762633864707140181 244783473780865602036799)
                  ·
                    rfl

theorem cell23_4290427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_4290427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290427 prefixEnd_4290427 := by exact prefixLift 4290427
  have htrace : WordTrace (prefixWord ++ tailWord_4290427) baseStart_4290427 baseEnd_4290427 := by
    simpa [prefixWord, tailWord_4290427, baseEnd_4290427] using wordTrace_append hprefix tailTrace_4290427
  have hstable : (prefixWord ++ tailWord_4290427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290427).length < 2 ^ (prefixWord ++ tailWord_4290427).sum := by decide
  have hdescent : baseEnd_4290427 < baseStart_4290427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290525 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4290525 : Nat := 118140960795 + 4290525 * 2 ^ 59
def prefixEnd_4290525 : Nat := 4983230072969 + 3 ^ 40 * 4290525 * 2
def baseEnd_4290525 : Nat := 734367195043977011635247

theorem tailTrace_4290525 : CollatzResearch.WordTrace tailWord_4290525 prefixEnd_4290525 734367195043977011635247 := by
  unfold tailWord_4290525
  simp only [CollatzResearch.WordTrace]
  refine ⟨156488302781168163176841029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104325535187445442117894019 156488302781168163176841029)
  ·
    refine ⟨29341556771469030595657693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156488302781168163176841029 29341556771469030595657693)
    ·
      refine ⟨11003083789300886473371635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29341556771469030595657693 11003083789300886473371635)
      ·
        refine ⟨16504625683951329710057453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11003083789300886473371635 16504625683951329710057453)
        ·
          refine ⟨6189234631481748641271545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16504625683951329710057453 6189234631481748641271545)
          ·
            refine ⟨4641925973611311480953659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189234631481748641271545 4641925973611311480953659)
            ·
              refine ⟨6962888960416967221430489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641925973611311480953659 6962888960416967221430489)
              ·
                refine ⟨5222166720312725416072867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6962888960416967221430489 5222166720312725416072867)
                ·
                  refine ⟨7833250080469088124109301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222166720312725416072867 7833250080469088124109301)
                  ·
                    refine ⟨734367195043977011635247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7833250080469088124109301 734367195043977011635247)
                    ·
                      rfl

theorem cell23_4290525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4290525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290525 prefixEnd_4290525 := by exact prefixLift 4290525
  have htrace : WordTrace (prefixWord ++ tailWord_4290525) baseStart_4290525 baseEnd_4290525 := by
    simpa [prefixWord, tailWord_4290525, baseEnd_4290525] using wordTrace_append hprefix tailTrace_4290525
  have hstable : (prefixWord ++ tailWord_4290525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290525).length < 2 ^ (prefixWord ++ tailWord_4290525).sum := by decide
  have hdescent : baseEnd_4290525 < baseStart_4290525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290528 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2]
def baseStart_4290528 : Nat := 118140960795 + 4290528 * 2 ^ 59
def prefixEnd_4290528 : Nat := 4983230072969 + 3 ^ 40 * 4290528 * 2
def baseEnd_4290528 : Nat := 2203103125573894523168227

theorem tailTrace_4290528 : CollatzResearch.WordTrace tailWord_4290528 prefixEnd_4290528 2203103125573894523168227 := by
  unfold tailWord_4290528
  simp only [CollatzResearch.WordTrace]
  refine ⟨78244206100078647344600119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104325608133438196459466825 78244206100078647344600119)
  ·
    refine ⟨117366309150117971016900179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78244206100078647344600119 117366309150117971016900179)
    ·
      refine ⟨176049463725176956525350269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117366309150117971016900179 176049463725176956525350269)
      ·
        refine ⟨66018548896941358697006351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176049463725176956525350269 66018548896941358697006351)
        ·
          refine ⟨99027823345412038045509527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66018548896941358697006351 99027823345412038045509527)
          ·
            refine ⟨148541735018118057068264291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99027823345412038045509527 148541735018118057068264291)
            ·
              refine ⟨222812602527177085602396437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148541735018118057068264291 222812602527177085602396437)
              ·
                refine ⟨10444340743461425887612333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 222812602527177085602396437 10444340743461425887612333)
                ·
                  refine ⟨3916627778798034707854625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10444340743461425887612333 3916627778798034707854625)
                  ·
                    refine ⟨2937470834098526030890969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916627778798034707854625 2937470834098526030890969)
                    ·
                      refine ⟨2203103125573894523168227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937470834098526030890969 2203103125573894523168227)
                      ·
                        rfl

theorem cell23_4290528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_4290528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290528 prefixEnd_4290528 := by exact prefixLift 4290528
  have htrace : WordTrace (prefixWord ++ tailWord_4290528) baseStart_4290528 baseEnd_4290528 := by
    simpa [prefixWord, tailWord_4290528, baseEnd_4290528] using wordTrace_append hprefix tailTrace_4290528
  have hstable : (prefixWord ++ tailWord_4290528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290528).length < 2 ^ (prefixWord ++ tailWord_4290528).sum := by decide
  have hdescent : baseEnd_4290528 < baseStart_4290528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290545 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_4290545 : Nat := 118140960795 + 4290545 * 2 ^ 59
def prefixEnd_4290545 : Nat := 4983230072969 + 3 ^ 40 * 4290545 * 2
def baseEnd_4290545 : Nat := 2203111854745020956655649

theorem tailTrace_4290545 : CollatzResearch.WordTrace tailWord_4290545 prefixEnd_4290545 2203111854745020956655649 := by
  unfold tailWord_4290545
  simp only [CollatzResearch.WordTrace]
  refine ⟨156489032241095706592569089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104326021494063804395046059 156489032241095706592569089)
  ·
    refine ⟨117366774180821779944426817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156489032241095706592569089 117366774180821779944426817)
    ·
      refine ⟨88025080635616334958320113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117366774180821779944426817 88025080635616334958320113)
      ·
        refine ⟨66018810476712251218740085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88025080635616334958320113 66018810476712251218740085)
        ·
          refine ⟨6189263482191773551756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66018810476712251218740085 6189263482191773551756883)
          ·
            refine ⟨9283895223287660327635325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189263482191773551756883 9283895223287660327635325)
            ·
              refine ⟨3481460708732872622863247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9283895223287660327635325 3481460708732872622863247)
              ·
                refine ⟨5222191063099308934294871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481460708732872622863247 5222191063099308934294871)
                ·
                  refine ⟨7833286594648963401442307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222191063099308934294871 7833286594648963401442307)
                  ·
                    refine ⟨11749929891973445102163461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7833286594648963401442307 11749929891973445102163461)
                    ·
                      refine ⟨2203111854745020956655649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11749929891973445102163461 2203111854745020956655649)
                      ·
                        rfl

theorem cell23_4290545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_4290545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290545 prefixEnd_4290545 := by exact prefixLift 4290545
  have htrace : WordTrace (prefixWord ++ tailWord_4290545) baseStart_4290545 baseEnd_4290545 := by
    simpa [prefixWord, tailWord_4290545, baseEnd_4290545] using wordTrace_append hprefix tailTrace_4290545
  have hstable : (prefixWord ++ tailWord_4290545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290545).length < 2 ^ (prefixWord ++ tailWord_4290545).sum := by decide
  have hdescent : baseEnd_4290545 < baseStart_4290545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290561 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_4290561 : Nat := 118140960795 + 4290561 * 2 ^ 59
def prefixEnd_4290561 : Nat := 4983230072969 + 3 ^ 40 * 4290561 * 2
def baseEnd_4290561 : Nat := 2203120070435492894055575

theorem tailTrace_4290561 : CollatzResearch.WordTrace tailWord_4290561 prefixEnd_4290561 2203120070435492894055575 := by
  unfold tailWord_4290561
  simp only [CollatzResearch.WordTrace]
  refine ⟨156489615809037741325151537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104326410539358494216767691 156489615809037741325151537)
  ·
    refine ⟨117367211856778305993863653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156489615809037741325151537 117367211856778305993863653)
    ·
      refine ⟨22006352223145932373849435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117367211856778305993863653 22006352223145932373849435)
      ·
        refine ⟨33009528334718898560774153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22006352223145932373849435 33009528334718898560774153)
        ·
          refine ⟨24757146251039173920580615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33009528334718898560774153 24757146251039173920580615)
          ·
            refine ⟨37135719376558760880870923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24757146251039173920580615 37135719376558760880870923)
            ·
              refine ⟨55703579064838141321306385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37135719376558760880870923 55703579064838141321306385)
              ·
                refine ⟨41777684298628605990979789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55703579064838141321306385 41777684298628605990979789)
                ·
                  refine ⟨15666631611985727246617421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41777684298628605990979789 15666631611985727246617421)
                  ·
                    refine ⟨5874986854494647717481533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15666631611985727246617421 5874986854494647717481533)
                    ·
                      refine ⟨2203120070435492894055575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5874986854494647717481533 2203120070435492894055575)
                      ·
                        rfl

theorem cell23_4290561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_4290561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290561 prefixEnd_4290561 := by exact prefixLift 4290561
  have htrace : WordTrace (prefixWord ++ tailWord_4290561) baseStart_4290561 baseEnd_4290561 := by
    simpa [prefixWord, tailWord_4290561, baseEnd_4290561] using wordTrace_append hprefix tailTrace_4290561
  have hstable : (prefixWord ++ tailWord_4290561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290561).length < 2 ^ (prefixWord ++ tailWord_4290561).sum := by decide
  have hdescent : baseEnd_4290561 < baseStart_4290561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290599 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4290599 : Nat := 118140960795 + 4290599 * 2 ^ 59
def prefixEnd_4290599 : Nat := 4983230072969 + 3 ^ 40 * 4290599 * 2
def baseEnd_4290599 : Nat := 2203139582700363745380401

theorem tailTrace_4290599 : CollatzResearch.WordTrace tailWord_4290599 prefixEnd_4290599 2203139582700363745380401 := by
  unfold tailWord_4290599
  simp only [CollatzResearch.WordTrace]
  refine ⟨156491001782900073815034851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104327334521933382543356567 156491001782900073815034851)
  ·
    refine ⟨234736502674350110722552277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156491001782900073815034851 234736502674350110722552277)
    ·
      refine ⟨5501636781430080720059819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 234736502674350110722552277 5501636781430080720059819)
      ·
        refine ⟨8252455172145121080089729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5501636781430080720059819 8252455172145121080089729)
        ·
          refine ⟨6189341379108840810067297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8252455172145121080089729 6189341379108840810067297)
          ·
            refine ⟨4642006034331630607550473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189341379108840810067297 4642006034331630607550473)
            ·
              refine ⟨3481504525748722955662855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642006034331630607550473 3481504525748722955662855)
              ·
                refine ⟨5222256788623084433494283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481504525748722955662855 5222256788623084433494283)
                ·
                  refine ⟨7833385182934626650241425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222256788623084433494283 7833385182934626650241425)
                  ·
                    refine ⟨5875038887200969987681069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7833385182934626650241425 5875038887200969987681069)
                    ·
                      refine ⟨2203139582700363745380401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875038887200969987681069 2203139582700363745380401)
                      ·
                        rfl

theorem cell23_4290599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4290599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290599 prefixEnd_4290599 := by exact prefixLift 4290599
  have htrace : WordTrace (prefixWord ++ tailWord_4290599) baseStart_4290599 baseEnd_4290599 := by
    simpa [prefixWord, tailWord_4290599, baseEnd_4290599] using wordTrace_append hprefix tailTrace_4290599
  have hstable : (prefixWord ++ tailWord_4290599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290599).length < 2 ^ (prefixWord ++ tailWord_4290599).sum := by decide
  have hdescent : baseEnd_4290599 < baseStart_4290599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 8, 2]
def baseStart_4290601 : Nat := 118140960795 + 4290601 * 2 ^ 59
def prefixEnd_4290601 : Nat := 4983230072969 + 3 ^ 40 * 4290601 * 2
def baseEnd_4290601 : Nat := 2203140609661672737555391

theorem tailTrace_4290601 : CollatzResearch.WordTrace tailWord_4290601 prefixEnd_4290601 2203140609661672737555391 := by
  unfold tailWord_4290601
  simp only [CollatzResearch.WordTrace]
  refine ⟨156491074728892828156607657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104327383152595218771071771 156491074728892828156607657)
  ·
    refine ⟨117368306046669621117455743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156491074728892828156607657 117368306046669621117455743)
    ·
      refine ⟨176052459070004431676183615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117368306046669621117455743 176052459070004431676183615)
      ·
        refine ⟨264078688605006647514275423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176052459070004431676183615 264078688605006647514275423)
        ·
          refine ⟨396118032907509971271413135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264078688605006647514275423 396118032907509971271413135)
          ·
            refine ⟨594177049361264956907119703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396118032907509971271413135 594177049361264956907119703)
            ·
              refine ⟨891265574041897435360679555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594177049361264956907119703 891265574041897435360679555)
              ·
                refine ⟨1336898361062846153041019333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891265574041897435360679555 1336898361062846153041019333)
                ·
                  refine ⟨250668442699283653695191125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336898361062846153041019333 250668442699283653695191125)
                  ·
                    refine ⟨2937520812882230316740521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 250668442699283653695191125 2937520812882230316740521)
                    ·
                      refine ⟨2203140609661672737555391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937520812882230316740521 2203140609661672737555391)
                      ·
                        rfl

theorem cell23_4290601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8, 2].length) (baseStart_4290601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290601 prefixEnd_4290601 := by exact prefixLift 4290601
  have htrace : WordTrace (prefixWord ++ tailWord_4290601) baseStart_4290601 baseEnd_4290601 := by
    simpa [prefixWord, tailWord_4290601, baseEnd_4290601] using wordTrace_append hprefix tailTrace_4290601
  have hstable : (prefixWord ++ tailWord_4290601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290601).length < 2 ^ (prefixWord ++ tailWord_4290601).sum := by decide
  have hdescent : baseEnd_4290601 < baseStart_4290601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290612 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4290612 : Nat := 118140960795 + 4290612 * 2 ^ 59
def prefixEnd_4290612 : Nat := 4983230072969 + 3 ^ 40 * 4290612 * 2
def baseEnd_4290612 : Nat := 2203146257948872194517841

theorem tailTrace_4290612 : CollatzResearch.WordTrace tailWord_4290612 prefixEnd_4290612 2203146257948872194517841 := by
  unfold tailWord_4290612
  simp only [CollatzResearch.WordTrace]
  refine ⟨78245737965926488517629045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104327650621235318023505393 78245737965926488517629045)
  ·
    refine ⟨7335537934305608298527723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78245737965926488517629045 7335537934305608298527723)
    ·
      refine ⟨11003306901458412447791585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335537934305608298527723 11003306901458412447791585)
      ·
        refine ⟨8252480176093809335843689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11003306901458412447791585 8252480176093809335843689)
        ·
          refine ⟨6189360132070357001882767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8252480176093809335843689 6189360132070357001882767)
          ·
            refine ⟨9284040198105535502824151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189360132070357001882767 9284040198105535502824151)
            ·
              refine ⟨13926060297158303254236227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9284040198105535502824151 13926060297158303254236227)
              ·
                refine ⟨20889090445737454881354341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13926060297158303254236227 20889090445737454881354341)
                ·
                  refine ⟨3916704458575772790253939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20889090445737454881354341 3916704458575772790253939)
                  ·
                    refine ⟨5875056687863659185380909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3916704458575772790253939 5875056687863659185380909)
                    ·
                      refine ⟨2203146257948872194517841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875056687863659185380909 2203146257948872194517841)
                      ·
                        rfl

theorem cell23_4290612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4290612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290612 prefixEnd_4290612 := by exact prefixLift 4290612
  have htrace : WordTrace (prefixWord ++ tailWord_4290612) baseStart_4290612 baseEnd_4290612 := by
    simpa [prefixWord, tailWord_4290612, baseEnd_4290612] using wordTrace_append hprefix tailTrace_4290612
  have hstable : (prefixWord ++ tailWord_4290612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290612).length < 2 ^ (prefixWord ++ tailWord_4290612).sum := by decide
  have hdescent : baseEnd_4290612 < baseStart_4290612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290631 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_4290631 : Nat := 118140960795 + 4290631 * 2 ^ 59
def prefixEnd_4290631 : Nat := 4983230072969 + 3 ^ 40 * 4290631 * 2
def baseEnd_4290631 : Nat := 2203156014081307620180253

theorem tailTrace_4290631 : CollatzResearch.WordTrace tailWord_4290631 prefixEnd_4290631 2203156014081307620180253 := by
  unfold tailWord_4290631
  simp only [CollatzResearch.WordTrace]
  refine ⟨156492168918784143280199747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104328112612522762186799831 156492168918784143280199747)
  ·
    refine ⟨234738253378176214920299621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156492168918784143280199747 234738253378176214920299621)
    ·
      refine ⟨44013422508408040297556179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234738253378176214920299621 44013422508408040297556179)
      ·
        refine ⟨66020133762612060446334269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44013422508408040297556179 66020133762612060446334269)
        ·
          refine ⟨24757550160979522667375351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66020133762612060446334269 24757550160979522667375351)
          ·
            refine ⟨37136325241469284001063027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24757550160979522667375351 37136325241469284001063027)
            ·
              refine ⟨55704487862203926001594541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37136325241469284001063027 55704487862203926001594541)
              ·
                refine ⟨20889182948326472250597953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55704487862203926001594541 20889182948326472250597953)
                ·
                  refine ⟨15666887211244854187948465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20889182948326472250597953 15666887211244854187948465)
                  ·
                    refine ⟨11750165408433640640961349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15666887211244854187948465 11750165408433640640961349)
                    ·
                      refine ⟨2203156014081307620180253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11750165408433640640961349 2203156014081307620180253)
                      ·
                        rfl

theorem cell23_4290631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_4290631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290631 prefixEnd_4290631 := by exact prefixLift 4290631
  have htrace : WordTrace (prefixWord ++ tailWord_4290631) baseStart_4290631 baseEnd_4290631 := by
    simpa [prefixWord, tailWord_4290631, baseEnd_4290631] using wordTrace_append hprefix tailTrace_4290631
  have hstable : (prefixWord ++ tailWord_4290631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290631).length < 2 ^ (prefixWord ++ tailWord_4290631).sum := by decide
  have hdescent : baseEnd_4290631 < baseStart_4290631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290671 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 4, 5]
def baseStart_4290671 : Nat := 118140960795 + 4290671 * 2 ^ 59
def prefixEnd_4290671 : Nat := 4983230072969 + 3 ^ 40 * 4290671 * 2
def baseEnd_4290671 : Nat := 734392184435829154560023

theorem tailTrace_4290671 : CollatzResearch.WordTrace tailWord_4290671 prefixEnd_4290671 734392184435829154560023 := by
  unfold tailWord_4290671
  simp only [CollatzResearch.WordTrace]
  refine ⟨156493627838639230111655867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104329085225759486741103911 156493627838639230111655867)
  ·
    refine ⟨234740441757958845167483801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156493627838639230111655867 234740441757958845167483801)
    ·
      refine ⟨176055331318469133875612851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234740441757958845167483801 176055331318469133875612851)
      ·
        refine ⟨264082996977703700813419277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176055331318469133875612851 264082996977703700813419277)
        ·
          refine ⟨99031123866638887805032229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264082996977703700813419277 99031123866638887805032229)
          ·
            refine ⟨18568335724994791463443543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99031123866638887805032229 18568335724994791463443543)
            ·
              refine ⟨27852503587492187195165315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18568335724994791463443543 27852503587492187195165315)
              ·
                refine ⟨41778755381238280792747973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27852503587492187195165315 41778755381238280792747973)
                ·
                  refine ⟨7833516633982177648640245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41778755381238280792747973 7833516633982177648640245)
                  ·
                    refine ⟨734392184435829154560023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7833516633982177648640245 734392184435829154560023)
                    ·
                      rfl

theorem cell23_4290671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_4290671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290671 prefixEnd_4290671 := by exact prefixLift 4290671
  have htrace : WordTrace (prefixWord ++ tailWord_4290671) baseStart_4290671 baseEnd_4290671 := by
    simpa [prefixWord, tailWord_4290671, baseEnd_4290671] using wordTrace_append hprefix tailTrace_4290671
  have hstable : (prefixWord ++ tailWord_4290671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290671).length < 2 ^ (prefixWord ++ tailWord_4290671).sum := by decide
  have hdescent : baseEnd_4290671 < baseStart_4290671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290681 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_4290681 : Nat := 118140960795 + 4290681 * 2 ^ 59
def prefixEnd_4290681 : Nat := 4983230072969 + 3 ^ 40 * 4290681 * 2
def baseEnd_4290681 : Nat := 2203181688114032424555023

theorem tailTrace_4290681 : CollatzResearch.WordTrace tailWord_4290681 prefixEnd_4290681 2203181688114032424555023 := by
  unfold tailWord_4290681
  simp only [CollatzResearch.WordTrace]
  refine ⟨156493992568603001819519897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104329328379068667879679931 156493992568603001819519897)
  ·
    refine ⟨117370494426452251364639923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156493992568603001819519897 117370494426452251364639923)
    ·
      refine ⟨176055741639678377046959885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117370494426452251364639923 176055741639678377046959885)
      ·
        refine ⟨66020903114879391392609957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176055741639678377046959885 66020903114879391392609957)
        ·
          refine ⟨12378919334039885886114367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66020903114879391392609957 12378919334039885886114367)
          ·
            refine ⟨18568379001059828829171551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12378919334039885886114367 18568379001059828829171551)
            ·
              refine ⟨27852568501589743243757327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18568379001059828829171551 27852568501589743243757327)
              ·
                refine ⟨41778852752384614865635991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27852568501589743243757327 41778852752384614865635991)
                ·
                  refine ⟨62668279128576922298453987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41778852752384614865635991 62668279128576922298453987)
                  ·
                    refine ⟨94002418692865383447680981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62668279128576922298453987 94002418692865383447680981)
                    ·
                      refine ⟨2203181688114032424555023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94002418692865383447680981 2203181688114032424555023)
                      ·
                        rfl

theorem cell23_4290681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_4290681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290681 prefixEnd_4290681 := by exact prefixLift 4290681
  have htrace : WordTrace (prefixWord ++ tailWord_4290681) baseStart_4290681 baseEnd_4290681 := by
    simpa [prefixWord, tailWord_4290681, baseEnd_4290681] using wordTrace_append hprefix tailTrace_4290681
  have hstable : (prefixWord ++ tailWord_4290681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290681).length < 2 ^ (prefixWord ++ tailWord_4290681).sum := by decide
  have hdescent : baseEnd_4290681 < baseStart_4290681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290785 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_4290785 : Nat := 118140960795 + 4290785 * 2 ^ 59
def prefixEnd_4290785 : Nat := 4983230072969 + 3 ^ 40 * 4290785 * 2
def baseEnd_4290785 : Nat := 2203235090102100017654545

theorem tailTrace_4290785 : CollatzResearch.WordTrace tailWord_4290785 prefixEnd_4290785 2203235090102100017654545 := by
  unfold tailWord_4290785
  simp only [CollatzResearch.WordTrace]
  refine ⟨156497785760226227581305809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104331857173484151720870539 156497785760226227581305809)
  ·
    refine ⟨117373339320169670685979357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156497785760226227581305809 117373339320169670685979357)
    ·
      refine ⟨44015002245063626507242259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117373339320169670685979357 44015002245063626507242259)
      ·
        refine ⟨66022503367595439760863389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44015002245063626507242259 66022503367595439760863389)
        ·
          refine ⟨24758438762848289910323771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66022503367595439760863389 24758438762848289910323771)
          ·
            refine ⟨37137658144272434865485657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24758438762848289910323771 37137658144272434865485657)
            ·
              refine ⟨27853243608204326149114243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37137658144272434865485657 27853243608204326149114243)
              ·
                refine ⟨41779865412306489223671365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27853243608204326149114243 41779865412306489223671365)
                ·
                  refine ⟨7833724764807466729438381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41779865412306489223671365 7833724764807466729438381)
                  ·
                    refine ⟨2937646786802800023539393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7833724764807466729438381 2937646786802800023539393)
                    ·
                      refine ⟨2203235090102100017654545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937646786802800023539393 2203235090102100017654545)
                      ·
                        rfl

theorem cell23_4290785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_4290785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290785 prefixEnd_4290785 := by exact prefixLift 4290785
  have htrace : WordTrace (prefixWord ++ tailWord_4290785) baseStart_4290785 baseEnd_4290785 := by
    simpa [prefixWord, tailWord_4290785, baseEnd_4290785] using wordTrace_append hprefix tailTrace_4290785
  have hstable : (prefixWord ++ tailWord_4290785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290785).length < 2 ^ (prefixWord ++ tailWord_4290785).sum := by decide
  have hdescent : baseEnd_4290785 < baseStart_4290785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290786 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4290786 : Nat := 118140960795 + 4290786 * 2 ^ 59
def prefixEnd_4290786 : Nat := 4983230072969 + 3 ^ 40 * 4290786 * 2
def baseEnd_4290786 : Nat := 734411867860918171247347

theorem tailTrace_4290786 : CollatzResearch.WordTrace tailWord_4290786 prefixEnd_4290786 734411867860918171247347 := by
  unfold tailWord_4290786
  simp only [CollatzResearch.WordTrace]
  refine ⟨39124455558305651188023053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104331881488815069834728141 39124455558305651188023053)
  ·
    refine ⟨14671670834364619195508645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39124455558305651188023053 14671670834364619195508645)
    ·
      refine ⟨2750938281443366099157871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14671670834364619195508645 2750938281443366099157871)
      ·
        refine ⟨4126407422165049148736807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750938281443366099157871 4126407422165049148736807)
        ·
          refine ⟨6189611133247573723105211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126407422165049148736807 6189611133247573723105211)
          ·
            refine ⟨9284416699871360584657817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189611133247573723105211 9284416699871360584657817)
            ·
              refine ⟨6963312524903520438493363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9284416699871360584657817 6963312524903520438493363)
              ·
                refine ⟨10444968787355280657740045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6963312524903520438493363 10444968787355280657740045)
                ·
                  refine ⟨3916863295258230246652517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10444968787355280657740045 3916863295258230246652517)
                  ·
                    refine ⟨734411867860918171247347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3916863295258230246652517 734411867860918171247347)
                    ·
                      rfl

theorem cell23_4290786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4290786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290786 prefixEnd_4290786 := by exact prefixLift 4290786
  have htrace : WordTrace (prefixWord ++ tailWord_4290786) baseStart_4290786 baseEnd_4290786 := by
    simpa [prefixWord, tailWord_4290786, baseEnd_4290786] using wordTrace_append hprefix tailTrace_4290786
  have hstable : (prefixWord ++ tailWord_4290786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290786).length < 2 ^ (prefixWord ++ tailWord_4290786).sum := by decide
  have hdescent : baseEnd_4290786 < baseStart_4290786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290792 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4290792 : Nat := 118140960795 + 4290792 * 2 ^ 59
def prefixEnd_4290792 : Nat := 4983230072969 + 3 ^ 40 * 4290792 * 2
def baseEnd_4290792 : Nat := 2203238684466681490267013

theorem tailTrace_4290792 : CollatzResearch.WordTrace tailWord_4290792 prefixEnd_4290792 2203238684466681490267013 := by
  unfold tailWord_4290792
  simp only [CollatzResearch.WordTrace]
  refine ⟨78249020535600433888405315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104332027380800578517873753 78249020535600433888405315)
  ·
    refine ⟨117373530803400650832607973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78249020535600433888405315 117373530803400650832607973)
    ·
      refine ⟨22007537025637622031113995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117373530803400650832607973 22007537025637622031113995)
      ·
        refine ⟨33011305538456433046670993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22007537025637622031113995 33011305538456433046670993)
        ·
          refine ⟨24758479153842324785003245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33011305538456433046670993 24758479153842324785003245)
          ·
            refine ⟨9284429682690871794376217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24758479153842324785003245 9284429682690871794376217)
            ·
              refine ⟨6963322262018153845782163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9284429682690871794376217 6963322262018153845782163)
              ·
                refine ⟨10444983393027230768673245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6963322262018153845782163 10444983393027230768673245)
                ·
                  refine ⟨3916868772385211538252467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10444983393027230768673245 3916868772385211538252467)
                  ·
                    refine ⟨5875303158577817307378701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3916868772385211538252467 5875303158577817307378701)
                    ·
                      refine ⟨2203238684466681490267013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875303158577817307378701 2203238684466681490267013)
                      ·
                        rfl

theorem cell23_4290792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4290792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290792 prefixEnd_4290792 := by exact prefixLift 4290792
  have htrace : WordTrace (prefixWord ++ tailWord_4290792) baseStart_4290792 baseEnd_4290792 := by
    simpa [prefixWord, tailWord_4290792, baseEnd_4290792] using wordTrace_append hprefix tailTrace_4290792
  have hstable : (prefixWord ++ tailWord_4290792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290792).length < 2 ^ (prefixWord ++ tailWord_4290792).sum := by decide
  have hdescent : baseEnd_4290792 < baseStart_4290792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290815 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_4290815 : Nat := 118140960795 + 4290815 * 2 ^ 59
def prefixEnd_4290815 : Nat := 4983230072969 + 3 ^ 40 * 4290815 * 2
def baseEnd_4290815 : Nat := 2203250494521734900279407

theorem tailTrace_4290815 : CollatzResearch.WordTrace tailWord_4290815 prefixEnd_4290815 2203250494521734900279407 := by
  unfold tailWord_4290815
  simp only [CollatzResearch.WordTrace]
  refine ⟨156498879950117542704897899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104332586633411695136598599 156498879950117542704897899)
  ·
    refine ⟨234748319925176314057346849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156498879950117542704897899 234748319925176314057346849)
    ·
      refine ⟨176061239943882235543010137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234748319925176314057346849 176061239943882235543010137)
      ·
        refine ⟨132045929957911676657257603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176061239943882235543010137 132045929957911676657257603)
        ·
          refine ⟨198068894936867514985886405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132045929957911676657257603 198068894936867514985886405)
          ·
            refine ⟨37137917800662659059853701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198068894936867514985886405 37137917800662659059853701)
            ·
              refine ⟨6963359587624248573722569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37137917800662659059853701 6963359587624248573722569)
              ·
                refine ⟨5222519690718186430291927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6963359587624248573722569 5222519690718186430291927)
                ·
                  refine ⟨7833779536077279645437891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222519690718186430291927 7833779536077279645437891)
                  ·
                    refine ⟨11750669304115919468156837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7833779536077279645437891 11750669304115919468156837)
                    ·
                      refine ⟨2203250494521734900279407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11750669304115919468156837 2203250494521734900279407)
                      ·
                        rfl

theorem cell23_4290815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_4290815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290815 prefixEnd_4290815 := by exact prefixLift 4290815
  have htrace : WordTrace (prefixWord ++ tailWord_4290815) baseStart_4290815 baseEnd_4290815 := by
    simpa [prefixWord, tailWord_4290815, baseEnd_4290815] using wordTrace_append hprefix tailTrace_4290815
  have hstable : (prefixWord ++ tailWord_4290815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290815).length < 2 ^ (prefixWord ++ tailWord_4290815).sum := by decide
  have hdescent : baseEnd_4290815 < baseStart_4290815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290828 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4290828 : Nat := 118140960795 + 4290828 * 2 ^ 59
def prefixEnd_4290828 : Nat := 4983230072969 + 3 ^ 40 * 4290828 * 2
def baseEnd_4290828 : Nat := 2203257169770243349416847

theorem tailTrace_4290828 : CollatzResearch.WordTrace tailWord_4290828 prefixEnd_4290828 2203257169770243349416847 := by
  unfold tailWord_4290828
  simp only [CollatzResearch.WordTrace]
  refine ⟨78249677049535222962560569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104332902732713630616747425 78249677049535222962560569)
  ·
    refine ⟨58687257787151417221920427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78249677049535222962560569 58687257787151417221920427)
    ·
      refine ⟨88030886680727125832880641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58687257787151417221920427 88030886680727125832880641)
      ·
        refine ⟨66023165010545344374660481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88030886680727125832880641 66023165010545344374660481)
        ·
          refine ⟨49517373757909008280995361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66023165010545344374660481 49517373757909008280995361)
          ·
            refine ⟨37138030318431756210746521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49517373757909008280995361 37138030318431756210746521)
            ·
              refine ⟨27853522738823817158059891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37138030318431756210746521 27853522738823817158059891)
              ·
                refine ⟨41780284108235725737089837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27853522738823817158059891 41780284108235725737089837)
                ·
                  refine ⟨15667606540588397151408689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41780284108235725737089837 15667606540588397151408689)
                  ·
                    refine ⟨11750704905441297863556517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15667606540588397151408689 11750704905441297863556517)
                    ·
                      refine ⟨2203257169770243349416847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11750704905441297863556517 2203257169770243349416847)
                      ·
                        rfl

theorem cell23_4290828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4290828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290828 prefixEnd_4290828 := by exact prefixLift 4290828
  have htrace : WordTrace (prefixWord ++ tailWord_4290828) baseStart_4290828 baseEnd_4290828 := by
    simpa [prefixWord, tailWord_4290828, baseEnd_4290828] using wordTrace_append hprefix tailTrace_4290828
  have hstable : (prefixWord ++ tailWord_4290828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290828).length < 2 ^ (prefixWord ++ tailWord_4290828).sum := by decide
  have hdescent : baseEnd_4290828 < baseStart_4290828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290849 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4290849 : Nat := 118140960795 + 4290849 * 2 ^ 59
def prefixEnd_4290849 : Nat := 4983230072969 + 3 ^ 40 * 4290849 * 2
def baseEnd_4290849 : Nat := 2203267952863987767254251

theorem tailTrace_4290849 : CollatzResearch.WordTrace tailWord_4290849 prefixEnd_4290849 2203267952863987767254251 := by
  unfold tailWord_4290849
  simp only [CollatzResearch.WordTrace]
  refine ⟨156500120031994366511635601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104333413354662911007757067 156500120031994366511635601)
  ·
    refine ⟨117375090023995774883726701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156500120031994366511635601 117375090023995774883726701)
    ·
      refine ⟨44015658758998415581397513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117375090023995774883726701 44015658758998415581397513)
      ·
        refine ⟨33011744069248811686048135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44015658758998415581397513 33011744069248811686048135)
        ·
          refine ⟨49517616103873217529072203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33011744069248811686048135 49517616103873217529072203)
          ·
            refine ⟨74276424155809826293608305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49517616103873217529072203 74276424155809826293608305)
            ·
              refine ⟨55707318116857369720206229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74276424155809826293608305 55707318116857369720206229)
              ·
                refine ⟨2611280536727689205634667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55707318116857369720206229 2611280536727689205634667)
                ·
                  refine ⟨3916920805091533808452001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611280536727689205634667 3916920805091533808452001)
                  ·
                    refine ⟨2937690603818650356339001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916920805091533808452001 2937690603818650356339001)
                    ·
                      refine ⟨2203267952863987767254251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937690603818650356339001 2203267952863987767254251)
                      ·
                        rfl

theorem cell23_4290849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4290849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290849 prefixEnd_4290849 := by exact prefixLift 4290849
  have htrace : WordTrace (prefixWord ++ tailWord_4290849) baseStart_4290849 baseEnd_4290849 := by
    simpa [prefixWord, tailWord_4290849, baseEnd_4290849] using wordTrace_append hprefix tailTrace_4290849
  have hstable : (prefixWord ++ tailWord_4290849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290849).length < 2 ^ (prefixWord ++ tailWord_4290849).sum := by decide
  have hdescent : baseEnd_4290849 < baseStart_4290849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 4, 2]
def baseStart_4290905 : Nat := 118140960795 + 4290905 * 2 ^ 59
def prefixEnd_4290905 : Nat := 4983230072969 + 3 ^ 40 * 4290905 * 2
def baseEnd_4290905 : Nat := 2203296707780639548153993

theorem tailTrace_4290905 : CollatzResearch.WordTrace tailWord_4290905 prefixEnd_4290905 2203296707780639548153993 := by
  unfold tailWord_4290905
  simp only [CollatzResearch.WordTrace]
  refine ⟨156502162519791488075674169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104334775013194325383782779 156502162519791488075674169)
  ·
    refine ⟨117376621889843616056755627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156502162519791488075674169 117376621889843616056755627)
    ·
      refine ⟨176064932834765424085133441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117376621889843616056755627 176064932834765424085133441)
      ·
        refine ⟨132048699626074068063850081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176064932834765424085133441 132048699626074068063850081)
        ·
          refine ⟨99036524719555551047887561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132048699626074068063850081 99036524719555551047887561)
          ·
            refine ⟨74277393539666663285915671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99036524719555551047887561 74277393539666663285915671)
            ·
              refine ⟨111416090309499994928873507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74277393539666663285915671 111416090309499994928873507)
              ·
                refine ⟨167124135464249992393310261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111416090309499994928873507 167124135464249992393310261)
                ·
                  refine ⟨15667887699773436786872837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167124135464249992393310261 15667887699773436786872837)
                  ·
                    refine ⟨2937728943707519397538657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15667887699773436786872837 2937728943707519397538657)
                    ·
                      refine ⟨2203296707780639548153993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937728943707519397538657 2203296707780639548153993)
                      ·
                        rfl

theorem cell23_4290905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_4290905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290905 prefixEnd_4290905 := by exact prefixLift 4290905
  have htrace : WordTrace (prefixWord ++ tailWord_4290905) baseStart_4290905 baseEnd_4290905 := by
    simpa [prefixWord, tailWord_4290905, baseEnd_4290905] using wordTrace_append hprefix tailTrace_4290905
  have hstable : (prefixWord ++ tailWord_4290905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290905).length < 2 ^ (prefixWord ++ tailWord_4290905).sum := by decide
  have hdescent : baseEnd_4290905 < baseStart_4290905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290925 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4290925 : Nat := 118140960795 + 4290925 * 2 ^ 59
def prefixEnd_4290925 : Nat := 4983230072969 + 3 ^ 40 * 4290925 * 2
def baseEnd_4290925 : Nat := 2203306977393729469903901

theorem tailTrace_4290925 : CollatzResearch.WordTrace tailWord_4290925 prefixEnd_4290925 2203306977393729469903901 := by
  unfold tailWord_4290925
  simp only [CollatzResearch.WordTrace]
  refine ⟨156502891979719031491402229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104335261319812687660934819 156502891979719031491402229)
  ·
    refine ⟨14672146123098659202318959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156502891979719031491402229 14672146123098659202318959)
    ·
      refine ⟨22008219184647988803478439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14672146123098659202318959 22008219184647988803478439)
      ·
        refine ⟨33012328776971983205217659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22008219184647988803478439 33012328776971983205217659)
        ·
          refine ⟨49518493165457974807826489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33012328776971983205217659 49518493165457974807826489)
          ·
            refine ⟨37138869874093481105869867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49518493165457974807826489 37138869874093481105869867)
            ·
              refine ⟨55708304811140221658804801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37138869874093481105869867 55708304811140221658804801)
              ·
                refine ⟨41781228608355166244103601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55708304811140221658804801 41781228608355166244103601)
                ·
                  refine ⟨31335921456266374683077701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41781228608355166244103601 31335921456266374683077701)
                  ·
                    refine ⟨5875485273049945253077069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31335921456266374683077701 5875485273049945253077069)
                    ·
                      refine ⟨2203306977393729469903901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875485273049945253077069 2203306977393729469903901)
                      ·
                        rfl

theorem cell23_4290925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4290925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290925 prefixEnd_4290925 := by exact prefixLift 4290925
  have htrace : WordTrace (prefixWord ++ tailWord_4290925) baseStart_4290925 baseEnd_4290925 := by
    simpa [prefixWord, tailWord_4290925, baseEnd_4290925] using wordTrace_append hprefix tailTrace_4290925
  have hstable : (prefixWord ++ tailWord_4290925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290925).length < 2 ^ (prefixWord ++ tailWord_4290925).sum := by decide
  have hdescent : baseEnd_4290925 < baseStart_4290925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290928 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 9]
def baseStart_4290928 : Nat := 118140960795 + 4290928 * 2 ^ 59
def prefixEnd_4290928 : Nat := 4983230072969 + 3 ^ 40 * 4290928 * 2
def baseEnd_4290928 : Nat := 244812057537299217574043

theorem tailTrace_4290928 : CollatzResearch.WordTrace tailWord_4290928 prefixEnd_4290928 244812057537299217574043 := by
  unfold tailWord_4290928
  simp only [CollatzResearch.WordTrace]
  refine ⟨78251500699354081501880719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104335334265805442002507625 78251500699354081501880719)
  ·
    refine ⟨117377251049031122252821079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78251500699354081501880719 117377251049031122252821079)
    ·
      refine ⟨176065876573546683379231619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117377251049031122252821079 176065876573546683379231619)
      ·
        refine ⟨264098814860320025068847429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176065876573546683379231619 264098814860320025068847429)
        ·
          refine ⟨49518527786310004700408893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264098814860320025068847429 49518527786310004700408893)
          ·
            refine ⟨18569447919866251762653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49518527786310004700408893 18569447919866251762653335)
            ·
              refine ⟨27854171879799377643980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18569447919866251762653335 27854171879799377643980003)
              ·
                refine ⟨41781257819699066465970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27854171879799377643980003 41781257819699066465970005)
                ·
                  refine ⟨244812057537299217574043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41781257819699066465970005 244812057537299217574043)
                  ·
                    rfl

theorem cell23_4290928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_4290928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290928 prefixEnd_4290928 := by exact prefixLift 4290928
  have htrace : WordTrace (prefixWord ++ tailWord_4290928) baseStart_4290928 baseEnd_4290928 := by
    simpa [prefixWord, tailWord_4290928, baseEnd_4290928] using wordTrace_append hprefix tailTrace_4290928
  have hstable : (prefixWord ++ tailWord_4290928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290928).length < 2 ^ (prefixWord ++ tailWord_4290928).sum := by decide
  have hdescent : baseEnd_4290928 < baseStart_4290928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290955 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3]
def baseStart_4290955 : Nat := 118140960795 + 4290955 * 2 ^ 59
def prefixEnd_4290955 : Nat := 4983230072969 + 3 ^ 40 * 4290955 * 2
def baseEnd_4290955 : Nat := 2203322381813364352528763

theorem tailTrace_4290955 : CollatzResearch.WordTrace tailWord_4290955 prefixEnd_4290955 2203322381813364352528763 := by
  unfold tailWord_4290955
  simp only [CollatzResearch.WordTrace]
  refine ⟨156503986169610346614994319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104335990779740231076662879 156503986169610346614994319)
  ·
    refine ⟨234755979254415519922491479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156503986169610346614994319 234755979254415519922491479)
    ·
      refine ⟨352133968881623279883737219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234755979254415519922491479 352133968881623279883737219)
      ·
        refine ⟨528200953322434919825605829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352133968881623279883737219 528200953322434919825605829)
        ·
          refine ⟨99037678747956547467301093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 528200953322434919825605829 99037678747956547467301093)
          ·
            refine ⟨18569564765241852650118955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99037678747956547467301093 18569564765241852650118955)
            ·
              refine ⟨27854347147862778975178433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18569564765241852650118955 27854347147862778975178433)
              ·
                refine ⟨20890760360897084231383825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27854347147862778975178433 20890760360897084231383825)
                ·
                  refine ⟨15668070270672813173537869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20890760360897084231383825 15668070270672813173537869)
                  ·
                    refine ⟨5875526351502304940076701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15668070270672813173537869 5875526351502304940076701)
                    ·
                      refine ⟨2203322381813364352528763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875526351502304940076701 2203322381813364352528763)
                      ·
                        rfl

theorem cell23_4290955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].length) (baseStart_4290955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290955 prefixEnd_4290955 := by exact prefixLift 4290955
  have htrace : WordTrace (prefixWord ++ tailWord_4290955) baseStart_4290955 baseEnd_4290955 := by
    simpa [prefixWord, tailWord_4290955, baseEnd_4290955] using wordTrace_append hprefix tailTrace_4290955
  have hstable : (prefixWord ++ tailWord_4290955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290955).length < 2 ^ (prefixWord ++ tailWord_4290955).sum := by decide
  have hdescent : baseEnd_4290955 < baseStart_4290955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290956 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_4290956 : Nat := 118140960795 + 4290956 * 2 ^ 59
def prefixEnd_4290956 : Nat := 4983230072969 + 3 ^ 40 * 4290956 * 2
def baseEnd_4290956 : Nat := 2203322895294018848616259

theorem tailTrace_4290956 : CollatzResearch.WordTrace tailWord_4290956 prefixEnd_4290956 2203322895294018848616259 := by
  unfold tailWord_4290956
  simp only [CollatzResearch.WordTrace]
  refine ⟨78252011321303361892890361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104336015095071149190520481 78252011321303361892890361)
  ·
    refine ⟨58689008490977521419667771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78252011321303361892890361 58689008490977521419667771)
    ·
      refine ⟨88033512736466282129501657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58689008490977521419667771 88033512736466282129501657)
      ·
        refine ⟨66025134552349711597126243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88033512736466282129501657 66025134552349711597126243)
        ·
          refine ⟨99037701828524567395689365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66025134552349711597126243 99037701828524567395689365)
          ·
            refine ⟨4642392273212089096672939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99037701828524567395689365 4642392273212089096672939)
            ·
              refine ⟨6963588409818133645009409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642392273212089096672939 6963588409818133645009409)
              ·
                refine ⟨5222691307363600233757057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6963588409818133645009409 5222691307363600233757057)
                ·
                  refine ⟨3917018480522700175317793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222691307363600233757057 3917018480522700175317793)
                  ·
                    refine ⟨2937763860392025131488345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917018480522700175317793 2937763860392025131488345)
                    ·
                      refine ⟨2203322895294018848616259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937763860392025131488345 2203322895294018848616259)
                      ·
                        rfl

theorem cell23_4290956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_4290956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290956 prefixEnd_4290956 := by exact prefixLift 4290956
  have htrace : WordTrace (prefixWord ++ tailWord_4290956) baseStart_4290956 baseEnd_4290956 := by
    simpa [prefixWord, tailWord_4290956, baseEnd_4290956] using wordTrace_append hprefix tailTrace_4290956
  have hstable : (prefixWord ++ tailWord_4290956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290956).length < 2 ^ (prefixWord ++ tailWord_4290956).sum := by decide
  have hdescent : baseEnd_4290956 < baseStart_4290956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290973 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_4290973 : Nat := 118140960795 + 4290973 * 2 ^ 59
def prefixEnd_4290973 : Nat := 4983230072969 + 3 ^ 40 * 4290973 * 2
def baseEnd_4290973 : Nat := 2203331624465145282103681

theorem tailTrace_4290973 : CollatzResearch.WordTrace tailWord_4290973 prefixEnd_4290973 2203331624465145282103681 := by
  unfold tailWord_4290973
  simp only [CollatzResearch.WordTrace]
  refine ⟨156504642683545135689149573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104336428455696757126099715 156504642683545135689149573)
  ·
    refine ⟨29344620503164712941715545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156504642683545135689149573 29344620503164712941715545)
    ·
      refine ⟨22008465377373534706286659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29344620503164712941715545 22008465377373534706286659)
      ·
        refine ⟨33012698066060302059429989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22008465377373534706286659 33012698066060302059429989)
        ·
          refine ⟨6189880887386306636143123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33012698066060302059429989 6189880887386306636143123)
          ·
            refine ⟨9284821331079459954214685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189880887386306636143123 9284821331079459954214685)
            ·
              refine ⟨3481807999154797482830507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9284821331079459954214685 3481807999154797482830507)
              ·
                refine ⟨5222711998732196224245761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481807999154797482830507 5222711998732196224245761)
                ·
                  refine ⟨3917033999049147168184321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222711998732196224245761 3917033999049147168184321)
                  ·
                    refine ⟨2937775499286860376138241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917033999049147168184321 2937775499286860376138241)
                    ·
                      refine ⟨2203331624465145282103681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937775499286860376138241 2203331624465145282103681)
                      ·
                        rfl

theorem cell23_4290973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_4290973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290973 prefixEnd_4290973 := by exact prefixLift 4290973
  have htrace : WordTrace (prefixWord ++ tailWord_4290973) baseStart_4290973 baseEnd_4290973 := by
    simpa [prefixWord, tailWord_4290973, baseEnd_4290973] using wordTrace_append hprefix tailTrace_4290973
  have hstable : (prefixWord ++ tailWord_4290973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290973).length < 2 ^ (prefixWord ++ tailWord_4290973).sum := by decide
  have hdescent : baseEnd_4290973 < baseStart_4290973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4290988 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_4290988 : Nat := 118140960795 + 4290988 * 2 ^ 59
def prefixEnd_4290988 : Nat := 4983230072969 + 3 ^ 40 * 4290988 * 2
def baseEnd_4290988 : Nat := 734446442224987574472037

theorem tailTrace_4290988 : CollatzResearch.WordTrace tailWord_4290988 prefixEnd_4290988 734446442224987574472037 := by
  unfold tailWord_4290988
  simp only [CollatzResearch.WordTrace]
  refine ⟨78252594889245396625472809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104336793185660528833963745 78252594889245396625472809)
  ·
    refine ⟨58689446166934047469104607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78252594889245396625472809 58689446166934047469104607)
    ·
      refine ⟨88034169250401071203656911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58689446166934047469104607 88034169250401071203656911)
      ·
        refine ⟨132051253875601606805485367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88034169250401071203656911 132051253875601606805485367)
        ·
          refine ⟨198076880813402410208228051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132051253875601606805485367 198076880813402410208228051)
          ·
            refine ⟨297115321220103615312342077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198076880813402410208228051 297115321220103615312342077)
            ·
              refine ⟨111418245457538855742128279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297115321220103615312342077 111418245457538855742128279)
              ·
                refine ⟨167127368186308283613192419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111418245457538855742128279 167127368186308283613192419)
                ·
                  refine ⟨250691052279462425419788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167127368186308283613192419 250691052279462425419788629)
                  ·
                    refine ⟨734446442224987574472037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 250691052279462425419788629 734446442224987574472037)
                    ·
                      rfl

theorem cell23_4290988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_4290988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4290988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4290988 prefixEnd_4290988 := by exact prefixLift 4290988
  have htrace : WordTrace (prefixWord ++ tailWord_4290988) baseStart_4290988 baseEnd_4290988 := by
    simpa [prefixWord, tailWord_4290988, baseEnd_4290988] using wordTrace_append hprefix tailTrace_4290988
  have hstable : (prefixWord ++ tailWord_4290988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4290988).length < 2 ^ (prefixWord ++ tailWord_4290988).sum := by decide
  have hdescent : baseEnd_4290988 < baseStart_4290988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4290988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291073 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4291073 : Nat := 118140960795 + 4291073 * 2 ^ 59
def prefixEnd_4291073 : Nat := 4983230072969 + 3 ^ 40 * 4291073 * 2
def baseEnd_4291073 : Nat := 734460990843531630284407

theorem tailTrace_4291073 : CollatzResearch.WordTrace tailWord_4291073 prefixEnd_4291073 734460990843531630284407 := by
  unfold tailWord_4291073
  simp only [CollatzResearch.WordTrace]
  refine ⟨156508289983182852767789873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104338859988788568511859915 156508289983182852767789873)
  ·
    refine ⟨117381217487387139575842405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156508289983182852767789873 117381217487387139575842405)
    ·
      refine ⟨22008978278885088670470451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117381217487387139575842405 22008978278885088670470451)
      ·
        refine ⟨33013467418327633005705677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22008978278885088670470451 33013467418327633005705677)
        ·
          refine ⟨12380050281872862377139629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33013467418327633005705677 12380050281872862377139629)
          ·
            refine ⟨4642518855702323391427361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12380050281872862377139629 4642518855702323391427361)
            ·
              refine ⟨3481889141776742543570521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642518855702323391427361 3481889141776742543570521)
              ·
                refine ⟨2611416856332556907677891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481889141776742543570521 2611416856332556907677891)
                ·
                  refine ⟨3917125284498835361516837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611416856332556907677891 3917125284498835361516837)
                  ·
                    refine ⟨734460990843531630284407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917125284498835361516837 734460990843531630284407)
                    ·
                      rfl

theorem cell23_4291073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4291073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291073 prefixEnd_4291073 := by exact prefixLift 4291073
  have htrace : WordTrace (prefixWord ++ tailWord_4291073) baseStart_4291073 baseEnd_4291073 := by
    simpa [prefixWord, tailWord_4291073, baseEnd_4291073] using wordTrace_append hprefix tailTrace_4291073
  have hstable : (prefixWord ++ tailWord_4291073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291073).length < 2 ^ (prefixWord ++ tailWord_4291073).sum := by decide
  have hdescent : baseEnd_4291073 < baseStart_4291073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291125 : List Nat := [1, 3, 3, 1, 1, 2, 12]
def baseStart_4291125 : Nat := 118140960795 + 4291125 * 2 ^ 59
def prefixEnd_4291125 : Nat := 4983230072969 + 3 ^ 40 * 4291125 * 2
def baseEnd_4291125 : Nat := 27202588562032452930901

theorem tailTrace_4291125 : CollatzResearch.WordTrace tailWord_4291125 prefixEnd_4291125 27202588562032452930901 := by
  unfold tailWord_4291125
  simp only [CollatzResearch.WordTrace]
  refine ⟨156510186578994465648682829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104340124385996310432455219 156510186578994465648682829)
  ·
    refine ⟨58691319967122924618256061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156510186578994465648682829 58691319967122924618256061)
    ·
      refine ⟨22009244987671096731846023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58691319967122924618256061 22009244987671096731846023)
      ·
        refine ⟨33013867481506645097769035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22009244987671096731846023 33013867481506645097769035)
        ·
          refine ⟨49520801222259967646653553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33013867481506645097769035 49520801222259967646653553)
          ·
            refine ⟨37140600916694975734990165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49520801222259967646653553 37140600916694975734990165)
            ·
              refine ⟨27202588562032452930901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37140600916694975734990165 27202588562032452930901)
              ·
                rfl

theorem cell23_4291125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 12].length) (baseStart_4291125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291125 prefixEnd_4291125 := by exact prefixLift 4291125
  have htrace : WordTrace (prefixWord ++ tailWord_4291125) baseStart_4291125 baseEnd_4291125 := by
    simpa [prefixWord, tailWord_4291125, baseEnd_4291125] using wordTrace_append hprefix tailTrace_4291125
  have hstable : (prefixWord ++ tailWord_4291125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291125).length < 2 ^ (prefixWord ++ tailWord_4291125).sum := by decide
  have hdescent : baseEnd_4291125 < baseStart_4291125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291146 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_4291146 : Nat := 118140960795 + 4291146 * 2 ^ 59
def prefixEnd_4291146 : Nat := 4983230072969 + 3 ^ 40 * 4291146 * 2
def baseEnd_4291146 : Nat := 734473485539457701746795

theorem tailTrace_4291146 : CollatzResearch.WordTrace tailWord_4291146 prefixEnd_4291146 734473485539457701746795 := by
  unfold tailWord_4291146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39127738127979596558799323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104340635007945590823464861 39127738127979596558799323)
  ·
    refine ⟨58691607191969394838198985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39127738127979596558799323 58691607191969394838198985)
    ·
      refine ⟨44018705393977046128649239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58691607191969394838198985 44018705393977046128649239)
      ·
        refine ⟨66028058090965569192973859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44018705393977046128649239 66028058090965569192973859)
        ·
          refine ⟨99042087136448353789460789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66028058090965569192973859 99042087136448353789460789)
          ·
            refine ⟨9285195669042033167761949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99042087136448353789460789 9285195669042033167761949)
            ·
              refine ⟨3481948375890762437910731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9285195669042033167761949 3481948375890762437910731)
              ·
                refine ⟨5222922563836143656866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481948375890762437910731 5222922563836143656866097)
                ·
                  refine ⟨3917191922877107742649573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222922563836143656866097 3917191922877107742649573)
                  ·
                    refine ⟨734473485539457701746795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917191922877107742649573 734473485539457701746795)
                    ·
                      rfl

theorem cell23_4291146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_4291146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291146 prefixEnd_4291146 := by exact prefixLift 4291146
  have htrace : WordTrace (prefixWord ++ tailWord_4291146) baseStart_4291146 baseEnd_4291146 := by
    simpa [prefixWord, tailWord_4291146, baseEnd_4291146] using wordTrace_append hprefix tailTrace_4291146
  have hstable : (prefixWord ++ tailWord_4291146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291146).length < 2 ^ (prefixWord ++ tailWord_4291146).sum := by decide
  have hdescent : baseEnd_4291146 < baseStart_4291146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291149 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4291149 : Nat := 118140960795 + 4291149 * 2 ^ 59
def prefixEnd_4291149 : Nat := 4983230072969 + 3 ^ 40 * 4291149 * 2
def baseEnd_4291149 : Nat := 2203421997060336593502871

theorem tailTrace_4291149 : CollatzResearch.WordTrace tailWord_4291149 prefixEnd_4291149 2203421997060336593502871 := by
  unfold tailWord_4291149
  simp only [CollatzResearch.WordTrace]
  refine ⟨156511061930907517747556501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104340707953938345165037667 156511061930907517747556501)
  ·
    refine ⟨7336456028011289894416711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156511061930907517747556501 7336456028011289894416711)
    ·
      refine ⟨11004684042016934841625067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336456028011289894416711 11004684042016934841625067)
      ·
        refine ⟨16507026063025402262437601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11004684042016934841625067 16507026063025402262437601)
        ·
          refine ⟨12380269547269051696828201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16507026063025402262437601 12380269547269051696828201)
          ·
            refine ⟨9285202160451788772621151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12380269547269051696828201 9285202160451788772621151)
            ·
              refine ⟨13927803240677683158931727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9285202160451788772621151 13927803240677683158931727)
              ·
                refine ⟨20891704861016524738397591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13927803240677683158931727 20891704861016524738397591)
                ·
                  refine ⟨31337557291524787107596387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20891704861016524738397591 31337557291524787107596387)
                  ·
                    refine ⟨47006335937287180661394581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31337557291524787107596387 47006335937287180661394581)
                    ·
                      refine ⟨2203421997060336593502871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47006335937287180661394581 2203421997060336593502871)
                      ·
                        rfl

theorem cell23_4291149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4291149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291149 prefixEnd_4291149 := by exact prefixLift 4291149
  have htrace : WordTrace (prefixWord ++ tailWord_4291149) baseStart_4291149 baseEnd_4291149 := by
    simpa [prefixWord, tailWord_4291149, baseEnd_4291149] using wordTrace_append hprefix tailTrace_4291149
  have hstable : (prefixWord ++ tailWord_4291149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291149).length < 2 ^ (prefixWord ++ tailWord_4291149).sum := by decide
  have hdescent : baseEnd_4291149 < baseStart_4291149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291152 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_4291152 : Nat := 118140960795 + 4291152 * 2 ^ 59
def prefixEnd_4291152 : Nat := 4983230072969 + 3 ^ 40 * 4291152 * 2
def baseEnd_4291152 : Nat := 2203423537502300081765357

theorem tailTrace_4291152 : CollatzResearch.WordTrace tailWord_4291152 prefixEnd_4291152 2203423537502300081765357 := by
  unfold tailWord_4291152
  simp only [CollatzResearch.WordTrace]
  refine ⟨78255585674948324629957855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104340780899931099506610473 78255585674948324629957855)
  ·
    refine ⟨117383378512422486944936783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78255585674948324629957855 117383378512422486944936783)
    ·
      refine ⟨176075067768633730417405175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117383378512422486944936783 176075067768633730417405175)
      ·
        refine ⟨264112601652950595626107763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176075067768633730417405175 264112601652950595626107763)
        ·
          refine ⟨396168902479425893439161645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264112601652950595626107763 396168902479425893439161645)
          ·
            refine ⟨148563338429784710039685617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396168902479425893439161645 148563338429784710039685617)
            ·
              refine ⟨111422503822338532529764213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148563338429784710039685617 111422503822338532529764213)
              ·
                refine ⟨10445859733344237424665395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111422503822338532529764213 10445859733344237424665395)
                ·
                  refine ⟨15668789600016356136998093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10445859733344237424665395 15668789600016356136998093)
                  ·
                    refine ⟨5875796100006133551374285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15668789600016356136998093 5875796100006133551374285)
                    ·
                      refine ⟨2203423537502300081765357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875796100006133551374285 2203423537502300081765357)
                      ·
                        rfl

theorem cell23_4291152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_4291152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291152 prefixEnd_4291152 := by exact prefixLift 4291152
  have htrace : WordTrace (prefixWord ++ tailWord_4291152) baseStart_4291152 baseEnd_4291152 := by
    simpa [prefixWord, tailWord_4291152, baseEnd_4291152] using wordTrace_append hprefix tailTrace_4291152
  have hstable : (prefixWord ++ tailWord_4291152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291152).length < 2 ^ (prefixWord ++ tailWord_4291152).sum := by decide
  have hdescent : baseEnd_4291152 < baseStart_4291152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291156 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_4291156 : Nat := 118140960795 + 4291156 * 2 ^ 59
def prefixEnd_4291156 : Nat := 4983230072969 + 3 ^ 40 * 4291156 * 2
def baseEnd_4291156 : Nat := 2203425591424918066115339

theorem tailTrace_4291156 : CollatzResearch.WordTrace tailWord_4291156 prefixEnd_4291156 2203425591424918066115339 := by
  unfold tailWord_4291156
  simp only [CollatzResearch.WordTrace]
  refine ⟨78255658620941078971530661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104340878161254771962040881 78255658620941078971530661)
  ·
    refine ⟨14672935991426452307161999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78255658620941078971530661 14672935991426452307161999)
    ·
      refine ⟨22009403987139678460742999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14672935991426452307161999 22009403987139678460742999)
      ·
        refine ⟨33014105980709517691114499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22009403987139678460742999 33014105980709517691114499)
        ·
          refine ⟨49521158971064276536671749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33014105980709517691114499 49521158971064276536671749)
          ·
            refine ⟨9285217307074551850625953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49521158971064276536671749 9285217307074551850625953)
            ·
              refine ⟨6963912980305913887969465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9285217307074551850625953 6963912980305913887969465)
              ·
                refine ⟨5222934735229435415977099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6963912980305913887969465 5222934735229435415977099)
                ·
                  refine ⟨7834402102844153123965649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222934735229435415977099 7834402102844153123965649)
                  ·
                    refine ⟨5875801577133114842974237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7834402102844153123965649 5875801577133114842974237)
                    ·
                      refine ⟨2203425591424918066115339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875801577133114842974237 2203425591424918066115339)
                      ·
                        rfl

theorem cell23_4291156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_4291156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291156 prefixEnd_4291156 := by exact prefixLift 4291156
  have htrace : WordTrace (prefixWord ++ tailWord_4291156) baseStart_4291156 baseEnd_4291156 := by
    simpa [prefixWord, tailWord_4291156, baseEnd_4291156] using wordTrace_append hprefix tailTrace_4291156
  have hstable : (prefixWord ++ tailWord_4291156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291156).length < 2 ^ (prefixWord ++ tailWord_4291156).sum := by decide
  have hdescent : baseEnd_4291156 < baseStart_4291156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291169 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_4291169 : Nat := 118140960795 + 4291169 * 2 ^ 59
def prefixEnd_4291169 : Nat := 4983230072969 + 3 ^ 40 * 4291169 * 2
def baseEnd_4291169 : Nat := 2203432266673426515252779

theorem tailTrace_4291169 : CollatzResearch.WordTrace tailWord_4291169 prefixEnd_4291169 2203432266673426515252779 := by
  unfold tailWord_4291169
  simp only [CollatzResearch.WordTrace]
  refine ⟨156511791390835061163284561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104341194260556707442189707 156511791390835061163284561)
  ·
    refine ⟨117383843543126295872463421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156511791390835061163284561 117383843543126295872463421)
    ·
      refine ⟨44018941328672360952173783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117383843543126295872463421 44018941328672360952173783)
      ·
        refine ⟨66028411993008541428260675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44018941328672360952173783 66028411993008541428260675)
        ·
          refine ⟨99042617989512812142391013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66028411993008541428260675 99042617989512812142391013)
          ·
            refine ⟨18570490873033652276698315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99042617989512812142391013 18570490873033652276698315)
            ·
              refine ⟨27855736309550478415047473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18570490873033652276698315 27855736309550478415047473)
              ·
                refine ⟨20891802232162858811285605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27855736309550478415047473 20891802232162858811285605)
                ·
                  refine ⟨3917212918530536027116051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20891802232162858811285605 3917212918530536027116051)
                  ·
                    refine ⟨5875819377795804040674077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917212918530536027116051 5875819377795804040674077)
                    ·
                      refine ⟨2203432266673426515252779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875819377795804040674077 2203432266673426515252779)
                      ·
                        rfl

theorem cell23_4291169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_4291169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291169 prefixEnd_4291169 := by exact prefixLift 4291169
  have htrace : WordTrace (prefixWord ++ tailWord_4291169) baseStart_4291169 baseEnd_4291169 := by
    simpa [prefixWord, tailWord_4291169, baseEnd_4291169] using wordTrace_append hprefix tailTrace_4291169
  have hstable : (prefixWord ++ tailWord_4291169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291169).length < 2 ^ (prefixWord ++ tailWord_4291169).sum := by decide
  have hdescent : baseEnd_4291169 < baseStart_4291169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291209 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 4, 2]
def baseStart_4291209 : Nat := 118140960795 + 4291209 * 2 ^ 59
def prefixEnd_4291209 : Nat := 4983230072969 + 3 ^ 40 * 4291209 * 2
def baseEnd_4291209 : Nat := 2203452805899606358752595

theorem tailTrace_4291209 : CollatzResearch.WordTrace tailWord_4291209 prefixEnd_4291209 2203452805899606358752595 := by
  unfold tailWord_4291209
  simp only [CollatzResearch.WordTrace]
  refine ⟨156513250310690147994740681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104342166873793431996493787 156513250310690147994740681)
  ·
    refine ⟨117384937733017610996055511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156513250310690147994740681 117384937733017610996055511)
    ·
      refine ⟨176077406599526416494083267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117384937733017610996055511 176077406599526416494083267)
      ·
        refine ⟨264116109899289624741124901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176077406599526416494083267 264116109899289624741124901)
        ·
          refine ⟨49521770606116804638960919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264116109899289624741124901 49521770606116804638960919)
          ·
            refine ⟨74282655909175206958441379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49521770606116804638960919 74282655909175206958441379)
            ·
              refine ⟨111423983863762810437662069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74282655909175206958441379 111423983863762810437662069)
              ·
                refine ⟨10445998487227763478530819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111423983863762810437662069 10445998487227763478530819)
                ·
                  refine ⟨15668997730841645217796229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10445998487227763478530819 15668997730841645217796229)
                  ·
                    refine ⟨2937937074532808478336793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15668997730841645217796229 2937937074532808478336793)
                    ·
                      refine ⟨2203452805899606358752595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937937074532808478336793 2203452805899606358752595)
                      ·
                        rfl

theorem cell23_4291209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4, 2].length) (baseStart_4291209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291209 prefixEnd_4291209 := by exact prefixLift 4291209
  have htrace : WordTrace (prefixWord ++ tailWord_4291209) baseStart_4291209 baseEnd_4291209 := by
    simpa [prefixWord, tailWord_4291209, baseEnd_4291209] using wordTrace_append hprefix tailTrace_4291209
  have hstable : (prefixWord ++ tailWord_4291209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291209).length < 2 ^ (prefixWord ++ tailWord_4291209).sum := by decide
  have hdescent : baseEnd_4291209 < baseStart_4291209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291212 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4291212 : Nat := 118140960795 + 4291212 * 2 ^ 59
def prefixEnd_4291212 : Nat := 4983230072969 + 3 ^ 40 * 4291212 * 2
def baseEnd_4291212 : Nat := 2203454346341569847015081

theorem tailTrace_4291212 : CollatzResearch.WordTrace tailWord_4291212 prefixEnd_4291212 2203454346341569847015081 := by
  unfold tailWord_4291212
  simp only [CollatzResearch.WordTrace]
  refine ⟨78256679864839639753549945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104342239819786186338066593 78256679864839639753549945)
  ·
    refine ⟨58692509898629729815162459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78256679864839639753549945 58692509898629729815162459)
    ·
      refine ⟨88038764847944594722743689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58692509898629729815162459 88038764847944594722743689)
      ·
        refine ⟨66029073635958446042057767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88038764847944594722743689 66029073635958446042057767)
        ·
          refine ⟨99043610453937669063086651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66029073635958446042057767 99043610453937669063086651)
          ·
            refine ⟨148565415680906503594629977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99043610453937669063086651 148565415680906503594629977)
            ·
              refine ⟨111424061760679877695972483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148565415680906503594629977 111424061760679877695972483)
              ·
                refine ⟨167136092641019816543958725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111424061760679877695972483 167136092641019816543958725)
                ·
                  refine ⟨31338017370191215601992261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167136092641019816543958725 31338017370191215601992261)
                  ·
                    refine ⟨5875878256910852925373549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31338017370191215601992261 5875878256910852925373549)
                    ·
                      refine ⟨2203454346341569847015081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875878256910852925373549 2203454346341569847015081)
                      ·
                        rfl

theorem cell23_4291212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4291212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291212 prefixEnd_4291212 := by exact prefixLift 4291212
  have htrace : WordTrace (prefixWord ++ tailWord_4291212) baseStart_4291212 baseEnd_4291212 := by
    simpa [prefixWord, tailWord_4291212, baseEnd_4291212] using wordTrace_append hprefix tailTrace_4291212
  have hstable : (prefixWord ++ tailWord_4291212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291212).length < 2 ^ (prefixWord ++ tailWord_4291212).sum := by decide
  have hdescent : baseEnd_4291212 < baseStart_4291212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291230 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4291230 : Nat := 118140960795 + 4291230 * 2 ^ 59
def prefixEnd_4291230 : Nat := 4983230072969 + 3 ^ 40 * 4291230 * 2
def baseEnd_4291230 : Nat := 2203463588993350776589999

theorem tailTrace_4291230 : CollatzResearch.WordTrace tailWord_4291230 prefixEnd_4291230 2203463588993350776589999 := by
  unfold tailWord_4291230
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564252030451758572656893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104342677495742712387503429 19564252030451758572656893)
  ·
    refine ⟨7336594511419409464746335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19564252030451758572656893 7336594511419409464746335)
    ·
      refine ⟨11004891767129114197119503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336594511419409464746335 11004891767129114197119503)
      ·
        refine ⟨16507337650693671295679255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11004891767129114197119503 16507337650693671295679255)
        ·
          refine ⟨24761006476040506943518883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16507337650693671295679255 24761006476040506943518883)
          ·
            refine ⟨37141509714060760415278325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24761006476040506943518883 37141509714060760415278325)
            ·
              refine ⟨3482016535693196288932343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37141509714060760415278325 3482016535693196288932343)
              ·
                refine ⟨5223024803539794433398515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482016535693196288932343 5223024803539794433398515)
                ·
                  refine ⟨7834537205309691650097773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223024803539794433398515 7834537205309691650097773)
                  ·
                    refine ⟨2937951451991134368786665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7834537205309691650097773 2937951451991134368786665)
                    ·
                      refine ⟨2203463588993350776589999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2937951451991134368786665 2203463588993350776589999)
                      ·
                        rfl

theorem cell23_4291230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4291230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291230 prefixEnd_4291230 := by exact prefixLift 4291230
  have htrace : WordTrace (prefixWord ++ tailWord_4291230) baseStart_4291230 baseEnd_4291230 := by
    simpa [prefixWord, tailWord_4291230, baseEnd_4291230] using wordTrace_append hprefix tailTrace_4291230
  have hstable : (prefixWord ++ tailWord_4291230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291230).length < 2 ^ (prefixWord ++ tailWord_4291230).sum := by decide
  have hdescent : baseEnd_4291230 < baseStart_4291230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291246 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4291246 : Nat := 118140960795 + 4291246 * 2 ^ 59
def prefixEnd_4291246 : Nat := 4983230072969 + 3 ^ 40 * 4291246 * 2
def baseEnd_4291246 : Nat := 2203471804683822713989925

theorem tailTrace_4291246 : CollatzResearch.WordTrace tailWord_4291246 prefixEnd_4291246 2203471804683822713989925 := by
  unfold tailWord_4291246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564324976444512914229699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104343066541037402209225061 19564324976444512914229699)
  ·
    refine ⟨29346487464666769371344549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19564324976444512914229699 29346487464666769371344549)
    ·
      refine ⟨5502466399625019257127103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29346487464666769371344549 5502466399625019257127103)
      ·
        refine ⟨8253699599437528885690655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502466399625019257127103 8253699599437528885690655)
        ·
          refine ⟨12380549399156293328535983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253699599437528885690655 12380549399156293328535983)
          ·
            refine ⟨18570824098734439992803975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12380549399156293328535983 18570824098734439992803975)
            ·
              refine ⟨27856236148101659989205963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18570824098734439992803975 27856236148101659989205963)
              ·
                refine ⟨41784354222152489983808945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27856236148101659989205963 41784354222152489983808945)
                ·
                  refine ⟨31338265666614367487856709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41784354222152489983808945 31338265666614367487856709)
                  ·
                    refine ⟨5875924812490193903973133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31338265666614367487856709 5875924812490193903973133)
                    ·
                      refine ⟨2203471804683822713989925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5875924812490193903973133 2203471804683822713989925)
                      ·
                        rfl

theorem cell23_4291246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4291246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291246 prefixEnd_4291246 := by exact prefixLift 4291246
  have htrace : WordTrace (prefixWord ++ tailWord_4291246) baseStart_4291246 baseEnd_4291246 := by
    simpa [prefixWord, tailWord_4291246, baseEnd_4291246] using wordTrace_append hprefix tailTrace_4291246
  have hstable : (prefixWord ++ tailWord_4291246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291246).length < 2 ^ (prefixWord ++ tailWord_4291246).sum := by decide
  have hdescent : baseEnd_4291246 < baseStart_4291246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291312 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_4291312 : Nat := 118140960795 + 4291312 * 2 ^ 59
def prefixEnd_4291312 : Nat := 4983230072969 + 3 ^ 40 * 4291312 * 2
def baseEnd_4291312 : Nat := 2203505694407019455764621

theorem tailTrace_4291312 : CollatzResearch.WordTrace tailWord_4291312 prefixEnd_4291312 2203505694407019455764621 := by
  unfold tailWord_4291312
  simp only [CollatzResearch.WordTrace]
  refine ⟨78258503514658498292870095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104344671352877997723826793 78258503514658498292870095)
  ·
    refine ⟨117387755271987747439305143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78258503514658498292870095 117387755271987747439305143)
    ·
      refine ⟨176081632907981621158957715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117387755271987747439305143 176081632907981621158957715)
      ·
        refine ⟨264122449361972431738436573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176081632907981621158957715 264122449361972431738436573)
        ·
          refine ⟨99045918510739661901913715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264122449361972431738436573 99045918510739661901913715)
          ·
            refine ⟨148568877766109492852870573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99045918510739661901913715 148568877766109492852870573)
            ·
              refine ⟨55713329162291059819826465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148568877766109492852870573 55713329162291059819826465)
              ·
                refine ⟨41784996871718294864869849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55713329162291059819826465 41784996871718294864869849)
                ·
                  refine ⟨31338747653788721148652387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41784996871718294864869849 31338747653788721148652387)
                  ·
                    refine ⟨47008121480683081722978581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31338747653788721148652387 47008121480683081722978581)
                    ·
                      refine ⟨2203505694407019455764621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47008121480683081722978581 2203505694407019455764621)
                      ·
                        rfl

theorem cell23_4291312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_4291312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291312 prefixEnd_4291312 := by exact prefixLift 4291312
  have htrace : WordTrace (prefixWord ++ tailWord_4291312) baseStart_4291312 baseEnd_4291312 := by
    simpa [prefixWord, tailWord_4291312, baseEnd_4291312] using wordTrace_append hprefix tailTrace_4291312
  have hstable : (prefixWord ++ tailWord_4291312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291312).length < 2 ^ (prefixWord ++ tailWord_4291312).sum := by decide
  have hdescent : baseEnd_4291312 < baseStart_4291312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291360 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 1, 4]
def baseStart_4291360 : Nat := 118140960795 + 4291360 * 2 ^ 59
def prefixEnd_4291360 : Nat := 4983230072969 + 3 ^ 40 * 4291360 * 2
def baseEnd_4291360 : Nat := 734510113826145089321467

theorem tailTrace_4291360 : CollatzResearch.WordTrace tailWord_4291360 prefixEnd_4291360 734510113826145089321467 := by
  unfold tailWord_4291360
  simp only [CollatzResearch.WordTrace]
  refine ⟨78259378866571550391743767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104345838488762067188991689 78259378866571550391743767)
  ·
    refine ⟨117389068299857325587615651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78259378866571550391743767 117389068299857325587615651)
    ·
      refine ⟨176083602449785988381423477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117389068299857325587615651 176083602449785988381423477)
      ·
        refine ⟨16507837729667436410758451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176083602449785988381423477 16507837729667436410758451)
        ·
          refine ⟨24761756594501154616137677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16507837729667436410758451 24761756594501154616137677)
          ·
            refine ⟨9285658722937932981051629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24761756594501154616137677 9285658722937932981051629)
            ·
              refine ⟨3482122021101724867894361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9285658722937932981051629 3482122021101724867894361)
              ·
                refine ⟨2611591515826293650920771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482122021101724867894361 2611591515826293650920771)
                ·
                  refine ⟨3917387273739440476381157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611591515826293650920771 3917387273739440476381157)
                  ·
                    refine ⟨734510113826145089321467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917387273739440476381157 734510113826145089321467)
                    ·
                      rfl

theorem cell23_4291360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_4291360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291360 prefixEnd_4291360 := by exact prefixLift 4291360
  have htrace : WordTrace (prefixWord ++ tailWord_4291360) baseStart_4291360 baseEnd_4291360 := by
    simpa [prefixWord, tailWord_4291360, baseEnd_4291360] using wordTrace_append hprefix tailTrace_4291360
  have hstable : (prefixWord ++ tailWord_4291360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291360).length < 2 ^ (prefixWord ++ tailWord_4291360).sum := by decide
  have hdescent : baseEnd_4291360 < baseStart_4291360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291386 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_4291386 : Nat := 118140960795 + 4291386 * 2 ^ 59
def prefixEnd_4291386 : Nat := 4983230072969 + 3 ^ 40 * 4291386 * 2
def baseEnd_4291386 : Nat := 734514563991817388746427

theorem tailTrace_4291386 : CollatzResearch.WordTrace tailWord_4291386 prefixEnd_4291386 734514563991817388746427 := by
  unfold tailWord_4291386
  simp only [CollatzResearch.WordTrace]
  refine ⟨39129926507762226805983503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104346470687365938149289341 39129926507762226805983503)
  ·
    refine ⟨58694889761643340208975255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39129926507762226805983503 58694889761643340208975255)
    ·
      refine ⟨88042334642465010313462883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58694889761643340208975255 88042334642465010313462883)
      ·
        refine ⟨132063501963697515470194325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88042334642465010313462883 132063501963697515470194325)
        ·
          refine ⟨6190476654548321037665359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132063501963697515470194325 6190476654548321037665359)
          ·
            refine ⟨9285714981822481556498039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190476654548321037665359 9285714981822481556498039)
            ·
              refine ⟨13928572472733722334747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9285714981822481556498039 13928572472733722334747059)
              ·
                refine ⟨20892858709100583502120589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13928572472733722334747059 20892858709100583502120589)
                ·
                  refine ⟨7834822015912718813295221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20892858709100583502120589 7834822015912718813295221)
                  ·
                    refine ⟨734514563991817388746427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7834822015912718813295221 734514563991817388746427)
                    ·
                      rfl

theorem cell23_4291386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_4291386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291386 prefixEnd_4291386 := by exact prefixLift 4291386
  have htrace : WordTrace (prefixWord ++ tailWord_4291386) baseStart_4291386 baseEnd_4291386 := by
    simpa [prefixWord, tailWord_4291386, baseEnd_4291386] using wordTrace_append hprefix tailTrace_4291386
  have hstable : (prefixWord ++ tailWord_4291386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291386).length < 2 ^ (prefixWord ++ tailWord_4291386).sum := by decide
  have hdescent : baseEnd_4291386 < baseStart_4291386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291406 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_4291406 : Nat := 118140960795 + 4291406 * 2 ^ 59
def prefixEnd_4291406 : Nat := 4983230072969 + 3 ^ 40 * 4291406 * 2
def baseEnd_4291406 : Nat := 2203553961588542087989189

theorem tailTrace_4291406 : CollatzResearch.WordTrace tailWord_4291406 prefixEnd_4291406 2203553961588542087989189 := by
  unfold tailWord_4291406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19565054436372056329957759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104346956993984300426441381 19565054436372056329957759)
  ·
    refine ⟨29347581654558084494936639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19565054436372056329957759 29347581654558084494936639)
    ·
      refine ⟨44021372481837126742404959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29347581654558084494936639 44021372481837126742404959)
      ·
        refine ⟨66032058722755690113607439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44021372481837126742404959 66032058722755690113607439)
        ·
          refine ⟨99048088084133535170411159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66032058722755690113607439 99048088084133535170411159)
          ·
            refine ⟨148572132126200302755616739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99048088084133535170411159 148572132126200302755616739)
            ·
              refine ⟨222858198189300454133425109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148572132126200302755616739 222858198189300454133425109)
              ·
                refine ⟨5223239020061729393752151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 222858198189300454133425109 5223239020061729393752151)
                ·
                  refine ⟨7834858530092594090628227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223239020061729393752151 7834858530092594090628227)
                  ·
                    refine ⟨11752287795138891135942341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7834858530092594090628227 11752287795138891135942341)
                    ·
                      refine ⟨2203553961588542087989189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11752287795138891135942341 2203553961588542087989189)
                      ·
                        rfl

theorem cell23_4291406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_4291406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291406 prefixEnd_4291406 := by exact prefixLift 4291406
  have htrace : WordTrace (prefixWord ++ tailWord_4291406) baseStart_4291406 baseEnd_4291406 := by
    simpa [prefixWord, tailWord_4291406, baseEnd_4291406] using wordTrace_append hprefix tailTrace_4291406
  have hstable : (prefixWord ++ tailWord_4291406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291406).length < 2 ^ (prefixWord ++ tailWord_4291406).sum := by decide
  have hdescent : baseEnd_4291406 < baseStart_4291406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291417 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 1, 1, 3]
def baseStart_4291417 : Nat := 118140960795 + 4291417 * 2 ^ 59
def prefixEnd_4291417 : Nat := 4983230072969 + 3 ^ 40 * 4291417 * 2
def baseEnd_4291417 : Nat := 2203559609875741544951639

theorem tailTrace_4291417 : CollatzResearch.WordTrace tailWord_4291417 prefixEnd_4291417 2203559609875741544951639 := by
  unfold tailWord_4291417
  simp only [CollatzResearch.WordTrace]
  refine ⟨156520836693936599518312505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104347224462624399678875003 156520836693936599518312505)
  ·
    refine ⟨117390627520452449638734379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156520836693936599518312505 117390627520452449638734379)
    ·
      refine ⟨176085941280678674458101569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117390627520452449638734379 176085941280678674458101569)
      ·
        refine ⟨132064455960509005843576177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176085941280678674458101569 132064455960509005843576177)
        ·
          refine ⟨99048341970381754382682133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132064455960509005843576177 99048341970381754382682133)
          ·
            refine ⟨4642891029861644736688225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99048341970381754382682133 4642891029861644736688225)
            ·
              refine ⟨3482168272396233552516169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642891029861644736688225 3482168272396233552516169)
              ·
                refine ⟨2611626204297175164387127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482168272396233552516169 2611626204297175164387127)
                ·
                  refine ⟨3917439306445762746580691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611626204297175164387127 3917439306445762746580691)
                  ·
                    refine ⟨5876158959668644119871037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917439306445762746580691 5876158959668644119871037)
                    ·
                      refine ⟨2203559609875741544951639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876158959668644119871037 2203559609875741544951639)
                      ·
                        rfl

theorem cell23_4291417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_4291417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291417 prefixEnd_4291417 := by exact prefixLift 4291417
  have htrace : WordTrace (prefixWord ++ tailWord_4291417) baseStart_4291417 baseEnd_4291417 := by
    simpa [prefixWord, tailWord_4291417, baseEnd_4291417] using wordTrace_append hprefix tailTrace_4291417
  have hstable : (prefixWord ++ tailWord_4291417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291417).length < 2 ^ (prefixWord ++ tailWord_4291417).sum := by decide
  have hdescent : baseEnd_4291417 < baseStart_4291417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291423 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 3, 2, 2]
def baseStart_4291423 : Nat := 118140960795 + 4291423 * 2 ^ 59
def prefixEnd_4291423 : Nat := 4983230072969 + 3 ^ 40 * 4291423 * 2
def baseEnd_4291423 : Nat := 2203562690759668521476611

theorem tailTrace_4291423 : CollatzResearch.WordTrace tailWord_4291423 prefixEnd_4291423 2203562690759668521476611 := by
  unfold tailWord_4291423
  simp only [CollatzResearch.WordTrace]
  refine ⟨156521055531914862543030923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104347370354609908362020615 156521055531914862543030923)
  ·
    refine ⟨234781583297872293814546385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156521055531914862543030923 234781583297872293814546385)
    ·
      refine ⟨176086187473404220360909789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234781583297872293814546385 176086187473404220360909789)
      ·
        refine ⟨66032320302526582635341171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176086187473404220360909789 66032320302526582635341171)
        ·
          refine ⟨99048480453789873953011757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66032320302526582635341171 99048480453789873953011757)
          ·
            refine ⟨37143180170171202732379409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99048480453789873953011757 37143180170171202732379409)
            ·
              refine ⟨27857385127628402049284557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37143180170171202732379409 27857385127628402049284557)
              ·
                refine ⟨10446519422860650768481709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27857385127628402049284557 10446519422860650768481709)
                ·
                  refine ⟨3917444783572744038180641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10446519422860650768481709 3917444783572744038180641)
                  ·
                    refine ⟨2938083587679558028635481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917444783572744038180641 2938083587679558028635481)
                    ·
                      refine ⟨2203562690759668521476611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938083587679558028635481 2203562690759668521476611)
                      ·
                        rfl

theorem cell23_4291423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_4291423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291423 prefixEnd_4291423 := by exact prefixLift 4291423
  have htrace : WordTrace (prefixWord ++ tailWord_4291423) baseStart_4291423 baseEnd_4291423 := by
    simpa [prefixWord, tailWord_4291423, baseEnd_4291423] using wordTrace_append hprefix tailTrace_4291423
  have hstable : (prefixWord ++ tailWord_4291423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291423).length < 2 ^ (prefixWord ++ tailWord_4291423).sum := by decide
  have hdescent : baseEnd_4291423 < baseStart_4291423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291429 : List Nat := [1, 3, 1, 3, 1, 1, 5, 8]
def baseStart_4291429 : Nat := 118140960795 + 4291429 * 2 ^ 59
def prefixEnd_4291429 : Nat := 4983230072969 + 3 ^ 40 * 4291429 * 2
def baseEnd_4291429 : Nat := 81613547097910944370429

theorem tailTrace_4291429 : CollatzResearch.WordTrace tailWord_4291429 prefixEnd_4291429 81613547097910944370429 := by
  unfold tailWord_4291429
  simp only [CollatzResearch.WordTrace]
  refine ⟨156521274369893125567749341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104347516246595417045166227 156521274369893125567749341)
  ·
    refine ⟨58695477888709922087906003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156521274369893125567749341 58695477888709922087906003)
    ·
      refine ⟨88043216833064883131859005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58695477888709922087906003 88043216833064883131859005)
      ·
        refine ⟨33016206312399331174447127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88043216833064883131859005 33016206312399331174447127)
        ·
          refine ⟨49524309468598996761670691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33016206312399331174447127 49524309468598996761670691)
          ·
            refine ⟨74286464202898495142506037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49524309468598996761670691 74286464202898495142506037)
            ·
              refine ⟨6964356019021733919609941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74286464202898495142506037 6964356019021733919609941)
              ·
                refine ⟨81613547097910944370429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6964356019021733919609941 81613547097910944370429)
                ·
                  rfl

theorem cell23_4291429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 8].length) (baseStart_4291429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291429 prefixEnd_4291429 := by exact prefixLift 4291429
  have htrace : WordTrace (prefixWord ++ tailWord_4291429) baseStart_4291429 baseEnd_4291429 := by
    simpa [prefixWord, tailWord_4291429, baseEnd_4291429] using wordTrace_append hprefix tailTrace_4291429
  have hstable : (prefixWord ++ tailWord_4291429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291429).length < 2 ^ (prefixWord ++ tailWord_4291429).sum := by decide
  have hdescent : baseEnd_4291429 < baseStart_4291429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291436 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_4291436 : Nat := 118140960795 + 4291436 * 2 ^ 59
def prefixEnd_4291436 : Nat := 4983230072969 + 3 ^ 40 * 4291436 * 2
def baseEnd_4291436 : Nat := 2203569366008176970614051

theorem tailTrace_4291436 : CollatzResearch.WordTrace tailWord_4291436 prefixEnd_4291436 2203569366008176970614051 := by
  unfold tailWord_4291436
  simp only [CollatzResearch.WordTrace]
  refine ⟨78260764840433882881627081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104347686453911843842169441 78260764840433882881627081)
  ·
    refine ⟨58695573630325412161220311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78260764840433882881627081 58695573630325412161220311)
    ·
      refine ⟨88043360445488118241830467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58695573630325412161220311 88043360445488118241830467)
      ·
        refine ⟨132065040668232177362745701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88043360445488118241830467 132065040668232177362745701)
        ·
          refine ⟨24762195125293533255514819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132065040668232177362745701 24762195125293533255514819)
          ·
            refine ⟨37143292687940299883272229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24762195125293533255514819 37143292687940299883272229)
            ·
              refine ⟨6964367378988806228113543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37143292687940299883272229 6964367378988806228113543)
              ·
                refine ⟨10446551068483209342170315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6964367378988806228113543 10446551068483209342170315)
                ·
                  refine ⟨15669826602724814013255473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10446551068483209342170315 15669826602724814013255473)
                  ·
                    refine ⟨11752369952043610509941605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15669826602724814013255473 11752369952043610509941605)
                    ·
                      refine ⟨2203569366008176970614051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11752369952043610509941605 2203569366008176970614051)
                      ·
                        rfl

theorem cell23_4291436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_4291436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291436 prefixEnd_4291436 := by exact prefixLift 4291436
  have htrace : WordTrace (prefixWord ++ tailWord_4291436) baseStart_4291436 baseEnd_4291436 := by
    simpa [prefixWord, tailWord_4291436, baseEnd_4291436] using wordTrace_append hprefix tailTrace_4291436
  have hstable : (prefixWord ++ tailWord_4291436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291436).length < 2 ^ (prefixWord ++ tailWord_4291436).sum := by decide
  have hdescent : baseEnd_4291436 < baseStart_4291436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291454 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4291454 : Nat := 118140960795 + 4291454 * 2 ^ 59
def prefixEnd_4291454 : Nat := 4983230072969 + 3 ^ 40 * 4291454 * 2
def baseEnd_4291454 : Nat := 734526202886652633396323

theorem tailTrace_4291454 : CollatzResearch.WordTrace tailWord_4291454 prefixEnd_4291454 734526202886652633396323 := by
  unfold tailWord_4291454
  simp only [CollatzResearch.WordTrace]
  refine ⟨19565273274350319354676177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104348124129868369891606277 19565273274350319354676177)
  ·
    refine ⟨14673954955762739516007133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19565273274350319354676177 14673954955762739516007133)
    ·
      refine ⟨5502733108411027318502675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14673954955762739516007133 5502733108411027318502675)
      ·
        refine ⟨8254099662616540977754013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502733108411027318502675 8254099662616540977754013)
        ·
          refine ⟨3095287373481202866657755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8254099662616540977754013 3095287373481202866657755)
          ·
            refine ⟨4642931060221804299986633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095287373481202866657755 4642931060221804299986633)
            ·
              refine ⟨3482198295166353224989975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642931060221804299986633 3482198295166353224989975)
              ·
                refine ⟨5223297442749529837484963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482198295166353224989975 5223297442749529837484963)
                ·
                  refine ⟨7834946164124294756227445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223297442749529837484963 7834946164124294756227445)
                  ·
                    refine ⟨734526202886652633396323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7834946164124294756227445 734526202886652633396323)
                    ·
                      rfl

theorem cell23_4291454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4291454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291454 prefixEnd_4291454 := by exact prefixLift 4291454
  have htrace : WordTrace (prefixWord ++ tailWord_4291454) baseStart_4291454 baseEnd_4291454 := by
    simpa [prefixWord, tailWord_4291454, baseEnd_4291454] using wordTrace_append hprefix tailTrace_4291454
  have hstable : (prefixWord ++ tailWord_4291454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291454).length < 2 ^ (prefixWord ++ tailWord_4291454).sum := by decide
  have hdescent : baseEnd_4291454 < baseStart_4291454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291490 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4291490 : Nat := 118140960795 + 4291490 * 2 ^ 59
def prefixEnd_4291490 : Nat := 4983230072969 + 3 ^ 40 * 4291490 * 2
def baseEnd_4291490 : Nat := 2203597093963519759338803

theorem tailTrace_4291490 : CollatzResearch.WordTrace tailWord_4291490 prefixEnd_4291490 2203597093963519759338803 := by
  unfold tailWord_4291490
  simp only [CollatzResearch.WordTrace]
  refine ⟨39130874805668033246429981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104348999481781421990479949 39130874805668033246429981)
  ·
    refine ⟨14674078052125512467411243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39130874805668033246429981 14674078052125512467411243)
    ·
      refine ⟨22011117078188268701116865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14674078052125512467411243 22011117078188268701116865)
      ·
        refine ⟨16508337808641201525837649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22011117078188268701116865 16508337808641201525837649)
        ·
          refine ⟨12381253356480901144378237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16508337808641201525837649 12381253356480901144378237)
          ·
            refine ⟨4642970008680337929141839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12381253356480901144378237 4642970008680337929141839)
            ·
              refine ⟨6964455013020506893712759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642970008680337929141839 6964455013020506893712759)
              ·
                refine ⟨10446682519530760340569139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6964455013020506893712759 10446682519530760340569139)
                ·
                  refine ⟨15670023779296140510853709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10446682519530760340569139 15670023779296140510853709)
                  ·
                    refine ⟨5876258917236052691570141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15670023779296140510853709 5876258917236052691570141)
                    ·
                      refine ⟨2203597093963519759338803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876258917236052691570141 2203597093963519759338803)
                      ·
                        rfl

theorem cell23_4291490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4291490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291490 prefixEnd_4291490 := by exact prefixLift 4291490
  have htrace : WordTrace (prefixWord ++ tailWord_4291490) baseStart_4291490 baseEnd_4291490 := by
    simpa [prefixWord, tailWord_4291490, baseEnd_4291490] using wordTrace_append hprefix tailTrace_4291490
  have hstable : (prefixWord ++ tailWord_4291490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291490).length < 2 ^ (prefixWord ++ tailWord_4291490).sum := by decide
  have hdescent : baseEnd_4291490 < baseStart_4291490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_4291499 : Nat := 118140960795 + 4291499 * 2 ^ 59
def prefixEnd_4291499 : Nat := 4983230072969 + 3 ^ 40 * 4291499 * 2
def baseEnd_4291499 : Nat := 2203601715289410224126261

theorem tailTrace_4291499 : CollatzResearch.WordTrace tailWord_4291499 prefixEnd_4291499 2203601715289410224126261 := by
  unfold tailWord_4291499
  simp only [CollatzResearch.WordTrace]
  refine ⟨156523827479639527522797551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104349218319759685015198367 156523827479639527522797551)
  ·
    refine ⟨234785741219459291284196327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156523827479639527522797551 234785741219459291284196327)
    ·
      refine ⟨352178611829188936926294491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234785741219459291284196327 352178611829188936926294491)
      ·
        refine ⟨528267917743783405389441737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352178611829188936926294491 528267917743783405389441737)
        ·
          refine ⟨396200938307837554042081303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528267917743783405389441737 396200938307837554042081303)
          ·
            refine ⟨594301407461756331063121955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396200938307837554042081303 594301407461756331063121955)
            ·
              refine ⟨891452111192634496594682933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594301407461756331063121955 891452111192634496594682933)
              ·
                refine ⟨83573635424309484055751525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891452111192634496594682933 83573635424309484055751525)
                ·
                  refine ⟨15670056642058028260453411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83573635424309484055751525 15670056642058028260453411)
                  ·
                    refine ⟨23505084963087042390680117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15670056642058028260453411 23505084963087042390680117)
                    ·
                      refine ⟨2203601715289410224126261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23505084963087042390680117 2203601715289410224126261)
                      ·
                        rfl

theorem cell23_4291499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_4291499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291499 prefixEnd_4291499 := by exact prefixLift 4291499
  have htrace : WordTrace (prefixWord ++ tailWord_4291499) baseStart_4291499 baseEnd_4291499 := by
    simpa [prefixWord, tailWord_4291499, baseEnd_4291499] using wordTrace_append hprefix tailTrace_4291499
  have hstable : (prefixWord ++ tailWord_4291499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291499).length < 2 ^ (prefixWord ++ tailWord_4291499).sum := by decide
  have hdescent : baseEnd_4291499 < baseStart_4291499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291530 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_4291530 : Nat := 118140960795 + 4291530 * 2 ^ 59
def prefixEnd_4291530 : Nat := 4983230072969 + 3 ^ 40 * 4291530 * 2
def baseEnd_4291530 : Nat := 2203617633189699602838619

theorem tailTrace_4291530 : CollatzResearch.WordTrace tailWord_4291530 prefixEnd_4291530 2203617633189699602838619 := by
  unfold tailWord_4291530
  simp only [CollatzResearch.WordTrace]
  refine ⟨39131239535631804954294011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104349972095018146544784029 39131239535631804954294011)
  ·
    refine ⟨58696859303447707431441017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39131239535631804954294011 58696859303447707431441017)
    ·
      refine ⟨44022644477585780573580763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58696859303447707431441017 44022644477585780573580763)
      ·
        refine ⟨66033966716378670860371145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44022644477585780573580763 66033966716378670860371145)
        ·
          refine ⟨49525475037284003145278359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66033966716378670860371145 49525475037284003145278359)
          ·
            refine ⟨74288212555926004717917539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49525475037284003145278359 74288212555926004717917539)
            ·
              refine ⟨111432318833889007076876309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74288212555926004717917539 111432318833889007076876309)
              ·
                refine ⟨5223389945338547206728577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111432318833889007076876309 5223389945338547206728577)
                ·
                  refine ⟨3917542459003910405046433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223389945338547206728577 3917542459003910405046433)
                  ·
                    refine ⟨2938156844252932803784825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917542459003910405046433 2938156844252932803784825)
                    ·
                      refine ⟨2203617633189699602838619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938156844252932803784825 2203617633189699602838619)
                      ·
                        rfl

theorem cell23_4291530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_4291530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291530 prefixEnd_4291530 := by exact prefixLift 4291530
  have htrace : WordTrace (prefixWord ++ tailWord_4291530) baseStart_4291530 baseEnd_4291530 := by
    simpa [prefixWord, tailWord_4291530, baseEnd_4291530] using wordTrace_append hprefix tailTrace_4291530
  have hstable : (prefixWord ++ tailWord_4291530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291530).length < 2 ^ (prefixWord ++ tailWord_4291530).sum := by decide
  have hdescent : baseEnd_4291530 < baseStart_4291530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291620 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4291620 : Nat := 118140960795 + 4291620 * 2 ^ 59
def prefixEnd_4291620 : Nat := 4983230072969 + 3 ^ 40 * 4291620 * 2
def baseEnd_4291620 : Nat := 2203663846448604250713205

theorem tailTrace_4291620 : CollatzResearch.WordTrace tailWord_4291620 prefixEnd_4291620 2203663846448604250713205 := by
  unfold tailWord_4291620
  simp only [CollatzResearch.WordTrace]
  refine ⟨78264120356100582593976157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104352160474800776791968209 78264120356100582593976157)
  ·
    refine ⟨29349045133537718472741059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78264120356100582593976157 29349045133537718472741059)
    ·
      refine ⟨44023567700306577709111589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29349045133537718472741059 44023567700306577709111589)
      ·
        refine ⟨8254418943807483320458423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44023567700306577709111589 8254418943807483320458423)
        ·
          refine ⟨12381628415711224980687635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254418943807483320458423 12381628415711224980687635)
          ·
            refine ⟨18572442623566837471031453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12381628415711224980687635 18572442623566837471031453)
            ·
              refine ⟨6964665983837564051636795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18572442623566837471031453 6964665983837564051636795)
              ·
                refine ⟨10446998975756346077455193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6964665983837564051636795 10446998975756346077455193)
                ·
                  refine ⟨7835249231817259558091395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10446998975756346077455193 7835249231817259558091395)
                  ·
                    refine ⟨11752873847725889337137093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7835249231817259558091395 11752873847725889337137093)
                    ·
                      refine ⟨2203663846448604250713205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11752873847725889337137093 2203663846448604250713205)
                      ·
                        rfl

theorem cell23_4291620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4291620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291620 prefixEnd_4291620 := by exact prefixLift 4291620
  have htrace : WordTrace (prefixWord ++ tailWord_4291620) baseStart_4291620 baseEnd_4291620 := by
    simpa [prefixWord, tailWord_4291620, baseEnd_4291620] using wordTrace_append hprefix tailTrace_4291620
  have hstable : (prefixWord ++ tailWord_4291620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291620).length < 2 ^ (prefixWord ++ tailWord_4291620).sum := by decide
  have hdescent : baseEnd_4291620 < baseStart_4291620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291680 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2]
def baseStart_4291680 : Nat := 118140960795 + 4291680 * 2 ^ 59
def prefixEnd_4291680 : Nat := 4983230072969 + 3 ^ 40 * 4291680 * 2
def baseEnd_4291680 : Nat := 2203694655287874015962929

theorem tailTrace_4291680 : CollatzResearch.WordTrace tailWord_4291680 prefixEnd_4291680 2203694655287874015962929 := by
  unfold tailWord_4291680
  simp only [CollatzResearch.WordTrace]
  refine ⟨78265214545991897717568247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104353619394655863623424329 78265214545991897717568247)
  ·
    refine ⟨117397821818987846576352371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78265214545991897717568247 117397821818987846576352371)
    ·
      refine ⟨176096732728481769864528557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117397821818987846576352371 176096732728481769864528557)
      ·
        refine ⟨66036274773180663699198209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176096732728481769864528557 66036274773180663699198209)
        ·
          refine ⟨49527206079885497774398657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66036274773180663699198209 49527206079885497774398657)
          ·
            refine ⟨37145404559914123330798993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49527206079885497774398657 37145404559914123330798993)
            ·
              refine ⟨27859053419935592498099245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37145404559914123330798993 27859053419935592498099245)
              ·
                refine ⟨10447145032475847186787217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27859053419935592498099245 10447145032475847186787217)
                ·
                  refine ⟨7835358774356885390090413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10447145032475847186787217 7835358774356885390090413)
                  ·
                    refine ⟨2938259540383832021283905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7835358774356885390090413 2938259540383832021283905)
                    ·
                      refine ⟨2203694655287874015962929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938259540383832021283905 2203694655287874015962929)
                      ·
                        rfl

theorem cell23_4291680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_4291680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291680 prefixEnd_4291680 := by exact prefixLift 4291680
  have htrace : WordTrace (prefixWord ++ tailWord_4291680) baseStart_4291680 baseEnd_4291680 := by
    simpa [prefixWord, tailWord_4291680, baseEnd_4291680] using wordTrace_append hprefix tailTrace_4291680
  have hstable : (prefixWord ++ tailWord_4291680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291680).length < 2 ^ (prefixWord ++ tailWord_4291680).sum := by decide
  have hdescent : baseEnd_4291680 < baseStart_4291680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291690 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4291690 : Nat := 118140960795 + 4291690 * 2 ^ 59
def prefixEnd_4291690 : Nat := 4983230072969 + 3 ^ 40 * 4291690 * 2
def baseEnd_4291690 : Nat := 734566596698139658945961

theorem tailTrace_4291690 : CollatzResearch.WordTrace tailWord_4291690 prefixEnd_4291690 734566596698139658945961 := by
  unfold tailWord_4291690
  simp only [CollatzResearch.WordTrace]
  refine ⟨39132698455486891785750131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104353862547965044762000349 39132698455486891785750131)
  ·
    refine ⟨58699047683230337678625197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39132698455486891785750131 58699047683230337678625197)
    ·
      refine ⟨22012142881211376629484449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58699047683230337678625197 22012142881211376629484449)
      ·
        refine ⟨16509107160908532472113337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22012142881211376629484449 16509107160908532472113337)
        ·
          refine ⟨12381830370681399354085003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16509107160908532472113337 12381830370681399354085003)
          ·
            refine ⟨18572745556022099031127505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12381830370681399354085003 18572745556022099031127505)
            ·
              refine ⟨13929559167016574273345629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18572745556022099031127505 13929559167016574273345629)
              ·
                refine ⟨5223584687631215352504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13929559167016574273345629 5223584687631215352504611)
                ·
                  refine ⟨7835377031446823028756917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223584687631215352504611 7835377031446823028756917)
                  ·
                    refine ⟨734566596698139658945961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7835377031446823028756917 734566596698139658945961)
                    ·
                      rfl

theorem cell23_4291690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4291690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291690 prefixEnd_4291690 := by exact prefixLift 4291690
  have htrace : WordTrace (prefixWord ++ tailWord_4291690) baseStart_4291690 baseEnd_4291690 := by
    simpa [prefixWord, tailWord_4291690, baseEnd_4291690] using wordTrace_append hprefix tailTrace_4291690
  have hstable : (prefixWord ++ tailWord_4291690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291690).length < 2 ^ (prefixWord ++ tailWord_4291690).sum := by decide
  have hdescent : baseEnd_4291690 < baseStart_4291690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291703 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 4, 4]
def baseStart_4291703 : Nat := 118140960795 + 4291703 * 2 ^ 59
def prefixEnd_4291703 : Nat := 4983230072969 + 3 ^ 40 * 4291703 * 2
def baseEnd_4291703 : Nat := 734568821780975808658441

theorem tailTrace_4291703 : CollatzResearch.WordTrace tailWord_4291703 prefixEnd_4291703 734568821780975808658441 := by
  unfold tailWord_4291703
  simp only [CollatzResearch.WordTrace]
  refine ⟨156531267970900470363223763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104354178647266980242149175 156531267970900470363223763)
  ·
    refine ⟨234796901956350705544835645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156531267970900470363223763 234796901956350705544835645)
    ·
      refine ⟨88048838233631514579313367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234796901956350705544835645 88048838233631514579313367)
      ·
        refine ⟨132073257350447271868970051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88048838233631514579313367 132073257350447271868970051)
        ·
          refine ⟨198109886025670907803455077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132073257350447271868970051 198109886025670907803455077)
          ·
            refine ⟨37145603629813295213147827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198109886025670907803455077 37145603629813295213147827)
            ·
              refine ⟨55718405444719942819721741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37145603629813295213147827 55718405444719942819721741)
              ·
                refine ⟨20894402041769978557395653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55718405444719942819721741 20894402041769978557395653)
                ·
                  refine ⟨3917700382831870979511685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20894402041769978557395653 3917700382831870979511685)
                  ·
                    refine ⟨734568821780975808658441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917700382831870979511685 734568821780975808658441)
                    ·
                      rfl

theorem cell23_4291703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_4291703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291703 prefixEnd_4291703 := by exact prefixLift 4291703
  have htrace : WordTrace (prefixWord ++ tailWord_4291703) baseStart_4291703 baseEnd_4291703 := by
    simpa [prefixWord, tailWord_4291703, baseEnd_4291703] using wordTrace_append hprefix tailTrace_4291703
  have hstable : (prefixWord ++ tailWord_4291703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291703).length < 2 ^ (prefixWord ++ tailWord_4291703).sum := by decide
  have hdescent : baseEnd_4291703 < baseStart_4291703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291740 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4291740 : Nat := 118140960795 + 4291740 * 2 ^ 59
def prefixEnd_4291740 : Nat := 4983230072969 + 3 ^ 40 * 4291740 * 2
def baseEnd_4291740 : Nat := 2203725464127143781212653

theorem tailTrace_4291740 : CollatzResearch.WordTrace tailWord_4291740 prefixEnd_4291740 2203725464127143781212653 := by
  unfold tailWord_4291740
  simp only [CollatzResearch.WordTrace]
  refine ⟨78266308735883212841160337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104355078314510950454880449 78266308735883212841160337)
  ·
    refine ⟨58699731551912409630870253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78266308735883212841160337 58699731551912409630870253)
    ·
      refine ⟨22012399331967153611576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58699731551912409630870253 22012399331967153611576345)
      ·
        refine ⟨16509299498975365208682259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22012399331967153611576345 16509299498975365208682259)
        ·
          refine ⟨24763949248463047813023389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16509299498975365208682259 24763949248463047813023389)
          ·
            refine ⟨9286480968173642929883771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24763949248463047813023389 9286480968173642929883771)
            ·
              refine ⟨13929721452260464394825657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9286480968173642929883771 13929721452260464394825657)
              ·
                refine ⟨10447291089195348296119243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13929721452260464394825657 10447291089195348296119243)
                ·
                  refine ⟨15670936633793022444178865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10447291089195348296119243 15670936633793022444178865)
                  ·
                    refine ⟨11753202475344766833134149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15670936633793022444178865 11753202475344766833134149)
                    ·
                      refine ⟨2203725464127143781212653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11753202475344766833134149 2203725464127143781212653)
                      ·
                        rfl

theorem cell23_4291740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4291740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291740 prefixEnd_4291740 := by exact prefixLift 4291740
  have htrace : WordTrace (prefixWord ++ tailWord_4291740) baseStart_4291740 baseEnd_4291740 := by
    simpa [prefixWord, tailWord_4291740, baseEnd_4291740] using wordTrace_append hprefix tailTrace_4291740
  have hstable : (prefixWord ++ tailWord_4291740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291740).length < 2 ^ (prefixWord ++ tailWord_4291740).sum := by decide
  have hdescent : baseEnd_4291740 < baseStart_4291740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291744 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 1, 2, 2]
def baseStart_4291744 : Nat := 118140960795 + 4291744 * 2 ^ 59
def prefixEnd_4291744 : Nat := 4983230072969 + 3 ^ 40 * 4291744 * 2
def baseEnd_4291744 : Nat := 2203727518049761765562635

theorem tailTrace_4291744 : CollatzResearch.WordTrace tailWord_4291744 prefixEnd_4291744 2203727518049761765562635 := by
  unfold tailWord_4291744
  simp only [CollatzResearch.WordTrace]
  refine ⟨78266381681875967182733143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104355175575834622910310857 78266381681875967182733143)
  ·
    refine ⟨117399572522813950774099715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78266381681875967182733143 117399572522813950774099715)
    ·
      refine ⟨176099358784220926161149573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117399572522813950774099715 176099358784220926161149573)
      ·
        refine ⟨33018629772041423655215545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176099358784220926161149573 33018629772041423655215545)
        ·
          refine ⟨24763972329031067741411659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33018629772041423655215545 24763972329031067741411659)
          ·
            refine ⟨37145958493546601612117489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24763972329031067741411659 37145958493546601612117489)
            ·
              refine ⟨27859468870159951209088117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37145958493546601612117489 27859468870159951209088117)
              ·
                refine ⟨2611825206577495425852011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27859468870159951209088117 2611825206577495425852011)
                ·
                  refine ⟨3917737809866243138778017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611825206577495425852011 3917737809866243138778017)
                  ·
                    refine ⟨2938303357399682354083513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917737809866243138778017 2938303357399682354083513)
                    ·
                      refine ⟨2203727518049761765562635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938303357399682354083513 2203727518049761765562635)
                      ·
                        rfl

theorem cell23_4291744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_4291744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291744 prefixEnd_4291744 := by exact prefixLift 4291744
  have htrace : WordTrace (prefixWord ++ tailWord_4291744) baseStart_4291744 baseEnd_4291744 := by
    simpa [prefixWord, tailWord_4291744, baseEnd_4291744] using wordTrace_append hprefix tailTrace_4291744
  have hstable : (prefixWord ++ tailWord_4291744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291744).length < 2 ^ (prefixWord ++ tailWord_4291744).sum := by decide
  have hdescent : baseEnd_4291744 < baseStart_4291744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291754 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4291754 : Nat := 118140960795 + 4291754 * 2 ^ 59
def prefixEnd_4291754 : Nat := 4983230072969 + 3 ^ 40 * 4291754 * 2
def baseEnd_4291754 : Nat := 734577550952102242145863

theorem tailTrace_4291754 : CollatzResearch.WordTrace tailWord_4291754 prefixEnd_4291754 734577550952102242145863 := by
  unfold tailWord_4291754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39133282023428926518332579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104355418729143804048886877 39133282023428926518332579)
  ·
    refine ⟨58699923035143389777498869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39133282023428926518332579 58699923035143389777498869)
    ·
      refine ⟨5503117784544692791640519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58699923035143389777498869 5503117784544692791640519)
      ·
        refine ⟨8254676676817039187460779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503117784544692791640519 8254676676817039187460779)
        ·
          refine ⟨12382015015225558781191169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254676676817039187460779 12382015015225558781191169)
          ·
            refine ⟨9286511261419169085893377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12382015015225558781191169 9286511261419169085893377)
            ·
              refine ⟨6964883446064376814420033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9286511261419169085893377 6964883446064376814420033)
              ·
                refine ⟨5223662584548282610815025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6964883446064376814420033 5223662584548282610815025)
                ·
                  refine ⟨3917746938411211958111269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223662584548282610815025 3917746938411211958111269)
                  ·
                    refine ⟨734577550952102242145863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917746938411211958111269 734577550952102242145863)
                    ·
                      rfl

theorem cell23_4291754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4291754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291754 prefixEnd_4291754 := by exact prefixLift 4291754
  have htrace : WordTrace (prefixWord ++ tailWord_4291754) baseStart_4291754 baseEnd_4291754 := by
    simpa [prefixWord, tailWord_4291754, baseEnd_4291754] using wordTrace_append hprefix tailTrace_4291754
  have hstable : (prefixWord ++ tailWord_4291754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291754).length < 2 ^ (prefixWord ++ tailWord_4291754).sum := by decide
  have hdescent : baseEnd_4291754 < baseStart_4291754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291761 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4291761 : Nat := 118140960795 + 4291761 * 2 ^ 59
def prefixEnd_4291761 : Nat := 4983230072969 + 3 ^ 40 * 4291761 * 2
def baseEnd_4291761 : Nat := 2203736247220888199050057

theorem tailTrace_4291761 : CollatzResearch.WordTrace tailWord_4291761 prefixEnd_4291761 2203736247220888199050057 := by
  unfold tailWord_4291761
  simp only [CollatzResearch.WordTrace]
  refine ⟨156533383404690346268835137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104355588936460230845890091 156533383404690346268835137)
  ·
    refine ⟨117400037553517759701626353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156533383404690346268835137 117400037553517759701626353)
    ·
      refine ⟨88050028165138319776219765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117400037553517759701626353 88050028165138319776219765)
      ·
        refine ⟨8254690140481717479020603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88050028165138319776219765 8254690140481717479020603)
        ·
          refine ⟨12382035210722576218530905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254690140481717479020603 12382035210722576218530905)
          ·
            refine ⟨9286526408041932163898179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12382035210722576218530905 9286526408041932163898179)
            ·
              refine ⟨13929789612062898245847269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9286526408041932163898179 13929789612062898245847269)
              ·
                refine ⟨2611835552261793421096363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13929789612062898245847269 2611835552261793421096363)
                ·
                  refine ⟨3917753328392690131644545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611835552261793421096363 3917753328392690131644545)
                  ·
                    refine ⟨2938314996294517598733409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917753328392690131644545 2938314996294517598733409)
                    ·
                      refine ⟨2203736247220888199050057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938314996294517598733409 2203736247220888199050057)
                      ·
                        rfl

theorem cell23_4291761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4291761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291761 prefixEnd_4291761 := by exact prefixLift 4291761
  have htrace : WordTrace (prefixWord ++ tailWord_4291761) baseStart_4291761 baseEnd_4291761 := by
    simpa [prefixWord, tailWord_4291761, baseEnd_4291761] using wordTrace_append hprefix tailTrace_4291761
  have hstable : (prefixWord ++ tailWord_4291761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291761).length < 2 ^ (prefixWord ++ tailWord_4291761).sum := by decide
  have hdescent : baseEnd_4291761 < baseStart_4291761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291777 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4291777 : Nat := 118140960795 + 4291777 * 2 ^ 59
def prefixEnd_4291777 : Nat := 4983230072969 + 3 ^ 40 * 4291777 * 2
def baseEnd_4291777 : Nat := 2203744462911360136449983

theorem tailTrace_4291777 : CollatzResearch.WordTrace tailWord_4291777 prefixEnd_4291777 2203744462911360136449983 := by
  unfold tailWord_4291777
  simp only [CollatzResearch.WordTrace]
  refine ⟨156533966972632381001417585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104355977981754920667611723 156533966972632381001417585)
  ·
    refine ⟨117400475229474285751063189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156533966972632381001417585 117400475229474285751063189)
    ·
      refine ⟨5503147276381607144581087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117400475229474285751063189 5503147276381607144581087)
      ·
        refine ⟨8254720914572410716871631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503147276381607144581087 8254720914572410716871631)
        ·
          refine ⟨12382081371858616075307447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254720914572410716871631 12382081371858616075307447)
          ·
            refine ⟨18573122057787924112961171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12382081371858616075307447 18573122057787924112961171)
            ·
              refine ⟨27859683086681886169441757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18573122057787924112961171 27859683086681886169441757)
              ·
                refine ⟨10447381157505707313540659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27859683086681886169441757 10447381157505707313540659)
                ·
                  refine ⟨15671071736258560970310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10447381157505707313540659 15671071736258560970310989)
                  ·
                    refine ⟨5876651901096960363866621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15671071736258560970310989 5876651901096960363866621)
                    ·
                      refine ⟨2203744462911360136449983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876651901096960363866621 2203744462911360136449983)
                      ·
                        rfl

theorem cell23_4291777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4291777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291777 prefixEnd_4291777 := by exact prefixLift 4291777
  have htrace : WordTrace (prefixWord ++ tailWord_4291777) baseStart_4291777 baseEnd_4291777 := by
    simpa [prefixWord, tailWord_4291777, baseEnd_4291777] using wordTrace_append hprefix tailTrace_4291777
  have hstable : (prefixWord ++ tailWord_4291777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291777).length < 2 ^ (prefixWord ++ tailWord_4291777).sum := by decide
  have hdescent : baseEnd_4291777 < baseStart_4291777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291778 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4291778 : Nat := 118140960795 + 4291778 * 2 ^ 59
def prefixEnd_4291778 : Nat := 4983230072969 + 3 ^ 40 * 4291778 * 2
def baseEnd_4291778 : Nat := 2203744976392014632537479

theorem tailTrace_4291778 : CollatzResearch.WordTrace tailWord_4291778 prefixEnd_4291778 2203744976392014632537479 := by
  unfold tailWord_4291778
  simp only [CollatzResearch.WordTrace]
  refine ⟨39133500861407189543050997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104356002297085838781469325 39133500861407189543050997)
  ·
    refine ⟨3668765705756924019661031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39133500861407189543050997 3668765705756924019661031)
    ·
      refine ⟨5503148558635386029491547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668765705756924019661031 5503148558635386029491547)
      ·
        refine ⟨8254722837953079044237321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503148558635386029491547 8254722837953079044237321)
        ·
          refine ⟨6191042128464809283177991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8254722837953079044237321 6191042128464809283177991)
          ·
            refine ⟨9286563192697213924766987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191042128464809283177991 9286563192697213924766987)
            ·
              refine ⟨13929844789045820887150481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9286563192697213924766987 13929844789045820887150481)
              ·
                refine ⟨10447383591784365665362861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13929844789045820887150481 10447383591784365665362861)
                ·
                  refine ⟨3917768846919137124511073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10447383591784365665362861 3917768846919137124511073)
                  ·
                    refine ⟨2938326635189352843383305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917768846919137124511073 2938326635189352843383305)
                    ·
                      refine ⟨2203744976392014632537479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938326635189352843383305 2203744976392014632537479)
                      ·
                        rfl

theorem cell23_4291778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4291778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291778 prefixEnd_4291778 := by exact prefixLift 4291778
  have htrace : WordTrace (prefixWord ++ tailWord_4291778) baseStart_4291778 baseEnd_4291778 := by
    simpa [prefixWord, tailWord_4291778, baseEnd_4291778] using wordTrace_append hprefix tailTrace_4291778
  have hstable : (prefixWord ++ tailWord_4291778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291778).length < 2 ^ (prefixWord ++ tailWord_4291778).sum := by decide
  have hdescent : baseEnd_4291778 < baseStart_4291778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291798 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4291798 : Nat := 118140960795 + 4291798 * 2 ^ 59
def prefixEnd_4291798 : Nat := 4983230072969 + 3 ^ 40 * 4291798 * 2
def baseEnd_4291798 : Nat := 2203755246005104554287387

theorem tailTrace_4291798 : CollatzResearch.WordTrace tailWord_4291798 prefixEnd_4291798 2203755246005104554287387 := by
  unfold tailWord_4291798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783420806597268849245753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104356488603704201058621365 9783420806597268849245753)
  ·
    refine ⟨7337565604947951636934315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9783420806597268849245753 7337565604947951636934315)
    ·
      refine ⟨11006348407421927455401473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7337565604947951636934315 11006348407421927455401473)
      ·
        refine ⟨8254761305566445591551105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11006348407421927455401473 8254761305566445591551105)
        ·
          refine ⟨6191070979174834193663329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8254761305566445591551105 6191070979174834193663329)
          ·
            refine ⟨4643303234381125645247497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6191070979174834193663329 4643303234381125645247497)
            ·
              refine ⟨3482477425785844233935623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643303234381125645247497 3482477425785844233935623)
              ·
                refine ⟨5223716138678766350903435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482477425785844233935623 5223716138678766350903435)
                ·
                  refine ⟨7835574208018149526355153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223716138678766350903435 7835574208018149526355153)
                  ·
                    refine ⟨5876680656013612144766365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7835574208018149526355153 5876680656013612144766365)
                    ·
                      refine ⟨2203755246005104554287387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876680656013612144766365 2203755246005104554287387)
                      ·
                        rfl

theorem cell23_4291798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4291798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291798 prefixEnd_4291798 := by exact prefixLift 4291798
  have htrace : WordTrace (prefixWord ++ tailWord_4291798) baseStart_4291798 baseEnd_4291798 := by
    simpa [prefixWord, tailWord_4291798, baseEnd_4291798] using wordTrace_append hprefix tailTrace_4291798
  have hstable : (prefixWord ++ tailWord_4291798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291798).length < 2 ^ (prefixWord ++ tailWord_4291798).sum := by decide
  have hdescent : baseEnd_4291798 < baseStart_4291798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291828 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4291828 : Nat := 118140960795 + 4291828 * 2 ^ 59
def prefixEnd_4291828 : Nat := 4983230072969 + 3 ^ 40 * 4291828 * 2
def baseEnd_4291828 : Nat := 2203770650424739436912249

theorem tailTrace_4291828 : CollatzResearch.WordTrace tailWord_4291828 prefixEnd_4291828 2203770650424739436912249 := by
  unfold tailWord_4291828
  simp only [CollatzResearch.WordTrace]
  refine ⟨78267913547723808355762069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104357218063631744474349425 78267913547723808355762069)
  ·
    refine ⟨3668808447549553516676347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78267913547723808355762069 3668808447549553516676347)
    ·
      refine ⟨5503212671324330275014521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668808447549553516676347 5503212671324330275014521)
      ·
        refine ⟨4127409503493247706260891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5503212671324330275014521 4127409503493247706260891)
        ·
          refine ⟨6191114255239871559391337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127409503493247706260891 6191114255239871559391337)
          ·
            refine ⟨4643335691429903669543503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6191114255239871559391337 4643335691429903669543503)
            ·
              refine ⟨6965003537144855504315255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4643335691429903669543503 6965003537144855504315255)
              ·
                refine ⟨10447505305717283256472883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965003537144855504315255 10447505305717283256472883)
                ·
                  refine ⟨15671257958575924884709325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10447505305717283256472883 15671257958575924884709325)
                  ·
                    refine ⟨5876721734465971831765997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15671257958575924884709325 5876721734465971831765997)
                    ·
                      refine ⟨2203770650424739436912249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876721734465971831765997 2203770650424739436912249)
                      ·
                        rfl

theorem cell23_4291828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4291828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291828 prefixEnd_4291828 := by exact prefixLift 4291828
  have htrace : WordTrace (prefixWord ++ tailWord_4291828) baseStart_4291828 baseEnd_4291828 := by
    simpa [prefixWord, tailWord_4291828, baseEnd_4291828] using wordTrace_append hprefix tailTrace_4291828
  have hstable : (prefixWord ++ tailWord_4291828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291828).length < 2 ^ (prefixWord ++ tailWord_4291828).sum := by decide
  have hdescent : baseEnd_4291828 < baseStart_4291828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291874 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_4291874 : Nat := 118140960795 + 4291874 * 2 ^ 59
def prefixEnd_4291874 : Nat := 4983230072969 + 3 ^ 40 * 4291874 * 2
def baseEnd_4291874 : Nat := 244866030059427361881893

theorem tailTrace_4291874 : CollatzResearch.WordTrace tailWord_4291874 prefixEnd_4291874 244866030059427361881893 := by
  unfold tailWord_4291874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39134376213320241641924669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104358336568853977711799117 39134376213320241641924669)
  ·
    refine ⟨14675391079995090615721751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39134376213320241641924669 14675391079995090615721751)
    ·
      refine ⟨22013086619992635923582627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14675391079995090615721751 22013086619992635923582627)
      ·
        refine ⟨33019629929988953885373941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22013086619992635923582627 33019629929988953885373941)
        ·
          refine ⟨3095590305936464426753807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33019629929988953885373941 3095590305936464426753807)
          ·
            refine ⟨4643385458904696640130711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095590305936464426753807 4643385458904696640130711)
            ·
              refine ⟨6965078188357044960196067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4643385458904696640130711 6965078188357044960196067)
              ·
                refine ⟨10447617282535567440294101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965078188357044960196067 10447617282535567440294101)
                ·
                  refine ⟨244866030059427361881893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10447617282535567440294101 244866030059427361881893)
                  ·
                    rfl

theorem cell23_4291874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_4291874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291874 prefixEnd_4291874 := by exact prefixLift 4291874
  have htrace : WordTrace (prefixWord ++ tailWord_4291874) baseStart_4291874 baseEnd_4291874 := by
    simpa [prefixWord, tailWord_4291874, baseEnd_4291874] using wordTrace_append hprefix tailTrace_4291874
  have hstable : (prefixWord ++ tailWord_4291874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291874).length < 2 ^ (prefixWord ++ tailWord_4291874).sum := by decide
  have hdescent : baseEnd_4291874 < baseStart_4291874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291880 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4291880 : Nat := 118140960795 + 4291880 * 2 ^ 59
def prefixEnd_4291880 : Nat := 4983230072969 + 3 ^ 40 * 4291880 * 2
def baseEnd_4291880 : Nat := 2203797351418773233462009

theorem tailTrace_4291880 : CollatzResearch.WordTrace tailWord_4291880 prefixEnd_4291880 2203797351418773233462009 := by
  unfold tailWord_4291880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78268861845629614796208547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104358482460839486394944729 78268861845629614796208547)
  ·
    refine ⟨117403292768444422194312821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78268861845629614796208547 117403292768444422194312821)
    ·
      refine ⟨11006558697041664580716827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117403292768444422194312821 11006558697041664580716827)
      ·
        refine ⟨16509838045562496871075241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11006558697041664580716827 16509838045562496871075241)
        ·
          refine ⟨12382378534171872653306431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16509838045562496871075241 12382378534171872653306431)
          ·
            refine ⟨18573567801257808979959647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12382378534171872653306431 18573567801257808979959647)
            ·
              refine ⟨27860351701886713469939471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18573567801257808979959647 27860351701886713469939471)
              ·
                refine ⟨41790527552830070204909207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27860351701886713469939471 41790527552830070204909207)
                ·
                  refine ⟨62685791329245105307363811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41790527552830070204909207 62685791329245105307363811)
                  ·
                    refine ⟨94028686993867657961045717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62685791329245105307363811 94028686993867657961045717)
                    ·
                      refine ⟨2203797351418773233462009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94028686993867657961045717 2203797351418773233462009)
                      ·
                        rfl

theorem cell23_4291880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4291880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291880 prefixEnd_4291880 := by exact prefixLift 4291880
  have htrace : WordTrace (prefixWord ++ tailWord_4291880) baseStart_4291880 baseEnd_4291880 := by
    simpa [prefixWord, tailWord_4291880, baseEnd_4291880] using wordTrace_append hprefix tailTrace_4291880
  have hstable : (prefixWord ++ tailWord_4291880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291880).length < 2 ^ (prefixWord ++ tailWord_4291880).sum := by decide
  have hdescent : baseEnd_4291880 < baseStart_4291880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291885 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4291885 : Nat := 118140960795 + 4291885 * 2 ^ 59
def prefixEnd_4291885 : Nat := 4983230072969 + 3 ^ 40 * 4291885 * 2
def baseEnd_4291885 : Nat := 2203799918822045713899487

theorem tailTrace_4291885 : CollatzResearch.WordTrace tailWord_4291885 prefixEnd_4291885 2203799918822045713899487 := by
  unfold tailWord_4291885
  simp only [CollatzResearch.WordTrace]
  refine ⟨156537906056241115446349109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104358604037494076964232739 156537906056241115446349109)
  ·
    refine ⟨14675428692772604573095229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156537906056241115446349109 14675428692772604573095229)
    ·
      refine ⟨5503285759789726714910711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14675428692772604573095229 5503285759789726714910711)
      ·
        refine ⟨8254928639684590072366067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503285759789726714910711 8254928639684590072366067)
        ·
          refine ⟨12382392959526885108549101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254928639684590072366067 12382392959526885108549101)
          ·
            refine ⟨4643397359822581915705913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12382392959526885108549101 4643397359822581915705913)
            ·
              refine ⟨3482548019866936436779435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643397359822581915705913 3482548019866936436779435)
              ·
                refine ⟨5223822029800404655169153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482548019866936436779435 5223822029800404655169153)
                ·
                  refine ⟨3917866522350303491376865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223822029800404655169153 3917866522350303491376865)
                  ·
                    refine ⟨2938399891762727618532649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917866522350303491376865 2938399891762727618532649)
                    ·
                      refine ⟨2203799918822045713899487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938399891762727618532649 2203799918822045713899487)
                      ·
                        rfl

theorem cell23_4291885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4291885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291885 prefixEnd_4291885 := by exact prefixLift 4291885
  have htrace : WordTrace (prefixWord ++ tailWord_4291885) baseStart_4291885 baseEnd_4291885 := by
    simpa [prefixWord, tailWord_4291885, baseEnd_4291885] using wordTrace_append hprefix tailTrace_4291885
  have hstable : (prefixWord ++ tailWord_4291885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291885).length < 2 ^ (prefixWord ++ tailWord_4291885).sum := by decide
  have hdescent : baseEnd_4291885 < baseStart_4291885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291913 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 10]
def baseStart_4291913 : Nat := 118140960795 + 4291913 * 2 ^ 59
def prefixEnd_4291913 : Nat := 4983230072969 + 3 ^ 40 * 4291913 * 2
def baseEnd_4291913 : Nat := 244868255142263511594373

theorem tailTrace_4291913 : CollatzResearch.WordTrace tailWord_4291913 prefixEnd_4291913 244868255142263511594373 := by
  unfold tailWord_4291913
  simp only [CollatzResearch.WordTrace]
  refine ⟨156538927300139676228368393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104359284866759784152245595 156538927300139676228368393)
  ·
    refine ⟨117404195475104757171276295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156538927300139676228368393 117404195475104757171276295)
    ·
      refine ⟨176106293212657135756914443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117404195475104757171276295 176106293212657135756914443)
      ·
        refine ⟨264159439818985703635371665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176106293212657135756914443 264159439818985703635371665)
        ·
          refine ⟨198119579864239277726528749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264159439818985703635371665 198119579864239277726528749)
          ·
            refine ⟨74294842449089729147448281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198119579864239277726528749 74294842449089729147448281)
            ·
              refine ⟨55721131836817296860586211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74294842449089729147448281 55721131836817296860586211)
              ·
                refine ⟨83581697755225945290879317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55721131836817296860586211 83581697755225945290879317)
                ·
                  refine ⟨244868255142263511594373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83581697755225945290879317 244868255142263511594373)
                  ·
                    rfl

theorem cell23_4291913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_4291913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291913 prefixEnd_4291913 := by exact prefixLift 4291913
  have htrace : WordTrace (prefixWord ++ tailWord_4291913) baseStart_4291913 baseEnd_4291913 := by
    simpa [prefixWord, tailWord_4291913, baseEnd_4291913] using wordTrace_append hprefix tailTrace_4291913
  have hstable : (prefixWord ++ tailWord_4291913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291913).length < 2 ^ (prefixWord ++ tailWord_4291913).sum := by decide
  have hdescent : baseEnd_4291913 < baseStart_4291913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291927 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_4291927 : Nat := 118140960795 + 4291927 * 2 ^ 59
def prefixEnd_4291927 : Nat := 4983230072969 + 3 ^ 40 * 4291927 * 2
def baseEnd_4291927 : Nat := 2203821485009534549574293

theorem tailTrace_4291927 : CollatzResearch.WordTrace tailWord_4291927 prefixEnd_4291927 2203821485009534549574293 := by
  unfold tailWord_4291927
  simp only [CollatzResearch.WordTrace]
  refine ⟨156539437922088956619378035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104359625281392637746252023 156539437922088956619378035)
  ·
    refine ⟨234809156883133434929067053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156539437922088956619378035 234809156883133434929067053)
    ·
      refine ⟨88053433831175038098400145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234809156883133434929067053 88053433831175038098400145)
      ·
        refine ⟨66040075373381278573800109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88053433831175038098400145 66040075373381278573800109)
        ·
          refine ⟨24765028265017979465175041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66040075373381278573800109 24765028265017979465175041)
          ·
            refine ⟨18573771198763484598881281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24765028265017979465175041 18573771198763484598881281)
            ·
              refine ⟨13930328399072613449160961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18573771198763484598881281 13930328399072613449160961)
              ·
                refine ⟨10447746299304460086870721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13930328399072613449160961 10447746299304460086870721)
                ·
                  refine ⟨7835809724478345065153041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10447746299304460086870721 7835809724478345065153041)
                  ·
                    refine ⟨5876857293358758798864781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7835809724478345065153041 5876857293358758798864781)
                    ·
                      refine ⟨2203821485009534549574293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876857293358758798864781 2203821485009534549574293)
                      ·
                        rfl

theorem cell23_4291927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_4291927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291927 prefixEnd_4291927 := by exact prefixLift 4291927
  have htrace : WordTrace (prefixWord ++ tailWord_4291927) baseStart_4291927 baseEnd_4291927 := by
    simpa [prefixWord, tailWord_4291927, baseEnd_4291927] using wordTrace_append hprefix tailTrace_4291927
  have hstable : (prefixWord ++ tailWord_4291927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291927).length < 2 ^ (prefixWord ++ tailWord_4291927).sum := by decide
  have hdescent : baseEnd_4291927 < baseStart_4291927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4291930 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_4291930 : Nat := 118140960795 + 4291930 * 2 ^ 59
def prefixEnd_4291930 : Nat := 4983230072969 + 3 ^ 40 * 4291930 * 2
def baseEnd_4291930 : Nat := 244869225050166448648531

theorem tailTrace_4291930 : CollatzResearch.WordTrace tailWord_4291930 prefixEnd_4291930 244869225050166448648531 := by
  unfold tailWord_4291930
  simp only [CollatzResearch.WordTrace]
  refine ⟨39134886835269522032934311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104359698227385392087824829 39134886835269522032934311)
  ·
    refine ⟨58702330252904283049401467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39134886835269522032934311 58702330252904283049401467)
    ·
      refine ⟨88053495379356424574102201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58702330252904283049401467 88053495379356424574102201)
      ·
        refine ⟨66040121534517318430576651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88053495379356424574102201 66040121534517318430576651)
        ·
          refine ⟨99060182301775977645864977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66040121534517318430576651 99060182301775977645864977)
          ·
            refine ⟨74295136726331983234398733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99060182301775977645864977 74295136726331983234398733)
            ·
              refine ⟨27860676272374493712899525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74295136726331983234398733 27860676272374493712899525)
              ·
                refine ⟨5223876801070217571168661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27860676272374493712899525 5223876801070217571168661)
                ·
                  refine ⟨244869225050166448648531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5223876801070217571168661 244869225050166448648531)
                  ·
                    rfl

theorem cell23_4291930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_4291930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4291930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4291930 prefixEnd_4291930 := by exact prefixLift 4291930
  have htrace : WordTrace (prefixWord ++ tailWord_4291930) baseStart_4291930 baseEnd_4291930 := by
    simpa [prefixWord, tailWord_4291930, baseEnd_4291930] using wordTrace_append hprefix tailTrace_4291930
  have hstable : (prefixWord ++ tailWord_4291930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4291930).length < 2 ^ (prefixWord ++ tailWord_4291930).sum := by decide
  have hdescent : baseEnd_4291930 < baseStart_4291930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4291930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292025 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4292025 : Nat := 118140960795 + 4292025 * 2 ^ 59
def prefixEnd_4292025 : Nat := 4983230072969 + 3 ^ 40 * 4292025 * 2
def baseEnd_4292025 : Nat := 2203871806113675166148843

theorem tailTrace_4292025 : CollatzResearch.WordTrace tailWord_4292025 prefixEnd_4292025 2203871806113675166148843 := by
  unfold tailWord_4292025
  simp only [CollatzResearch.WordTrace]
  refine ⟨156543012275733919356445529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104362008183822612904297019 156543012275733919356445529)
  ·
    refine ⟨117407259206800439517334147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156543012275733919356445529 117407259206800439517334147)
    ·
      refine ⟨176110888810200659276001221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117407259206800439517334147 176110888810200659276001221)
      ·
        refine ⟨33020791651912623614250229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176110888810200659276001221 33020791651912623614250229)
        ·
          refine ⟨3095699217366808463835959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33020791651912623614250229 3095699217366808463835959)
          ·
            refine ⟨4643548826050212695753939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095699217366808463835959 4643548826050212695753939)
            ·
              refine ⟨6965323239075319043630909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4643548826050212695753939 6965323239075319043630909)
              ·
                refine ⟨2611996214653244641361591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6965323239075319043630909 2611996214653244641361591)
                ·
                  refine ⟨3917994321979866962042387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611996214653244641361591 3917994321979866962042387)
                  ·
                    refine ⟨5876991482969800443063581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917994321979866962042387 5876991482969800443063581)
                    ·
                      refine ⟨2203871806113675166148843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5876991482969800443063581 2203871806113675166148843)
                      ·
                        rfl

theorem cell23_4292025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4292025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292025 prefixEnd_4292025 := by exact prefixLift 4292025
  have htrace : WordTrace (prefixWord ++ tailWord_4292025) baseStart_4292025 baseEnd_4292025 := by
    simpa [prefixWord, tailWord_4292025, baseEnd_4292025] using wordTrace_append hprefix tailTrace_4292025
  have hstable : (prefixWord ++ tailWord_4292025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292025).length < 2 ^ (prefixWord ++ tailWord_4292025).sum := by decide
  have hdescent : baseEnd_4292025 < baseStart_4292025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292054 : List Nat := [5, 2, 1, 1, 1, 3, 2, 8]
def baseStart_4292054 : Nat := 118140960795 + 4292054 * 2 ^ 59
def prefixEnd_4292054 : Nat := 4983230072969 + 3 ^ 40 * 4292054 * 2
def baseEnd_4292054 : Nat := 81625433224172427877267

theorem tailTrace_4292054 : CollatzResearch.WordTrace tailWord_4292054 prefixEnd_4292054 81625433224172427877267 := by
  unfold tailWord_4292054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784004374539303581828201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104362713328419238206167477 9784004374539303581828201)
  ·
    refine ⟨7338003280904477686371151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9784004374539303581828201 7338003280904477686371151)
    ·
      refine ⟨11007004921356716529556727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7338003280904477686371151 11007004921356716529556727)
      ·
        refine ⟨16510507382035074794335091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11007004921356716529556727 16510507382035074794335091)
        ·
          refine ⟨24765761073052612191502637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16510507382035074794335091 24765761073052612191502637)
          ·
            refine ⟨9287160402394729571813489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24765761073052612191502637 9287160402394729571813489)
            ·
              refine ⟨6965370301796047178860117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9287160402394729571813489 6965370301796047178860117)
              ·
                refine ⟨81625433224172427877267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6965370301796047178860117 81625433224172427877267)
                ·
                  rfl

theorem cell23_4292054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_4292054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292054 prefixEnd_4292054 := by exact prefixLift 4292054
  have htrace : WordTrace (prefixWord ++ tailWord_4292054) baseStart_4292054 baseEnd_4292054 := by
    simpa [prefixWord, tailWord_4292054, baseEnd_4292054] using wordTrace_append hprefix tailTrace_4292054
  have hstable : (prefixWord ++ tailWord_4292054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292054).length < 2 ^ (prefixWord ++ tailWord_4292054).sum := by decide
  have hdescent : baseEnd_4292054 < baseStart_4292054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292098 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4292098 : Nat := 118140960795 + 4292098 * 2 ^ 59
def prefixEnd_4292098 : Nat := 4983230072969 + 3 ^ 40 * 4292098 * 2
def baseEnd_4292098 : Nat := 2203909290201453380536007

theorem tailTrace_4292098 : CollatzResearch.WordTrace tailWord_4292098 prefixEnd_4292098 2203909290201453380536007 := by
  unfold tailWord_4292098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39136418701117363205963237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104363783202979635215901965 39136418701117363205963237)
  ·
    refine ⟨7338078506459505601118107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39136418701117363205963237 7338078506459505601118107)
    ·
      refine ⟨11007117759689258401677161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7338078506459505601118107 11007117759689258401677161)
      ·
        refine ⟨8255338319766943801257871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11007117759689258401677161 8255338319766943801257871)
        ·
          refine ⟨12383007479650415701886807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8255338319766943801257871 12383007479650415701886807)
          ·
            refine ⟨18574511219475623552830211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12383007479650415701886807 18574511219475623552830211)
            ·
              refine ⟨27861766829213435329245317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18574511219475623552830211 27861766829213435329245317)
              ·
                refine ⟨5224081280477519124233497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27861766829213435329245317 5224081280477519124233497)
                ·
                  refine ⟨3918060960358139343175123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224081280477519124233497 3918060960358139343175123)
                  ·
                    refine ⟨5877091440537209014762685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918060960358139343175123 5877091440537209014762685)
                    ·
                      refine ⟨2203909290201453380536007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877091440537209014762685 2203909290201453380536007)
                      ·
                        rfl

theorem cell23_4292098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4292098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292098 prefixEnd_4292098 := by exact prefixLift 4292098
  have htrace : WordTrace (prefixWord ++ tailWord_4292098) baseStart_4292098 baseEnd_4292098 := by
    simpa [prefixWord, tailWord_4292098, baseEnd_4292098] using wordTrace_append hprefix tailTrace_4292098
  have hstable : (prefixWord ++ tailWord_4292098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292098).length < 2 ^ (prefixWord ++ tailWord_4292098).sum := by decide
  have hdescent : baseEnd_4292098 < baseStart_4292098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292117 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4292117 : Nat := 118140960795 + 4292117 * 2 ^ 59
def prefixEnd_4292117 : Nat := 4983230072969 + 3 ^ 40 * 4292117 * 2
def baseEnd_4292117 : Nat := 2203919046333888806198419

theorem tailTrace_4292117 : CollatzResearch.WordTrace tailWord_4292117 prefixEnd_4292117 2203919046333888806198419 := by
  unfold tailWord_4292117
  simp only [CollatzResearch.WordTrace]
  refine ⟨156546367791400619068794605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104364245194267079379196403 156546367791400619068794605)
  ·
    refine ⟨58704887921775232150797977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156546367791400619068794605 58704887921775232150797977)
    ·
      refine ⟨44028665941331424113098483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58704887921775232150797977 44028665941331424113098483)
      ·
        refine ⟨66042998911997136169647725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44028665941331424113098483 66042998911997136169647725)
        ·
          refine ⟨24766124591998926063617897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66042998911997136169647725 24766124591998926063617897)
          ·
            refine ⟨18574593443999194547713423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24766124591998926063617897 18574593443999194547713423)
            ·
              refine ⟨27861890165998791821570135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18574593443999194547713423 27861890165998791821570135)
              ·
                refine ⟨41792835248998187732355203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27861890165998791821570135 41792835248998187732355203)
                ·
                  refine ⟨62689252873497281598532805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41792835248998187732355203 62689252873497281598532805)
                  ·
                    refine ⟨11754234913780740299724901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62689252873497281598532805 11754234913780740299724901)
                    ·
                      refine ⟨2203919046333888806198419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11754234913780740299724901 2203919046333888806198419)
                      ·
                        rfl

theorem cell23_4292117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4292117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292117 prefixEnd_4292117 := by exact prefixLift 4292117
  have htrace : WordTrace (prefixWord ++ tailWord_4292117) baseStart_4292117 baseEnd_4292117 := by
    simpa [prefixWord, tailWord_4292117, baseEnd_4292117] using wordTrace_append hprefix tailTrace_4292117
  have hstable : (prefixWord ++ tailWord_4292117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292117).length < 2 ^ (prefixWord ++ tailWord_4292117).sum := by decide
  have hdescent : baseEnd_4292117 < baseStart_4292117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292177 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_4292177 : Nat := 118140960795 + 4292177 * 2 ^ 59
def prefixEnd_4292177 : Nat := 4983230072969 + 3 ^ 40 * 4292177 * 2
def baseEnd_4292177 : Nat := 2203949855173158571448143

theorem tailTrace_4292177 : CollatzResearch.WordTrace tailWord_4292177 prefixEnd_4292177 2203949855173158571448143 := by
  unfold tailWord_4292177
  simp only [CollatzResearch.WordTrace]
  refine ⟨156548556171183249315978785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104365704114122166210652523 156548556171183249315978785)
  ·
    refine ⟨117411417128387436986984089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156548556171183249315978785 117411417128387436986984089)
    ·
      refine ⟨88058562846290577740238067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117411417128387436986984089 88058562846290577740238067)
      ·
        refine ⟨132087844269435866610357101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88058562846290577740238067 132087844269435866610357101)
        ·
          refine ⟨49532941601038449978883913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132087844269435866610357101 49532941601038449978883913)
          ·
            refine ⟨37149706200778837484162935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49532941601038449978883913 37149706200778837484162935)
            ·
              refine ⟨55724559301168256226244403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37149706200778837484162935 55724559301168256226244403)
              ·
                refine ⟨83586838951752384339366605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55724559301168256226244403 83586838951752384339366605)
                ·
                  refine ⟨31345064606907144127262477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83586838951752384339366605 31345064606907144127262477)
                  ·
                    refine ⟨11754399227590179047723429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31345064606907144127262477 11754399227590179047723429)
                    ·
                      refine ⟨2203949855173158571448143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11754399227590179047723429 2203949855173158571448143)
                      ·
                        rfl

theorem cell23_4292177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_4292177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292177 prefixEnd_4292177 := by exact prefixLift 4292177
  have htrace : WordTrace (prefixWord ++ tailWord_4292177) baseStart_4292177 baseEnd_4292177 := by
    simpa [prefixWord, tailWord_4292177, baseEnd_4292177] using wordTrace_append hprefix tailTrace_4292177
  have hstable : (prefixWord ++ tailWord_4292177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292177).length < 2 ^ (prefixWord ++ tailWord_4292177).sum := by decide
  have hdescent : baseEnd_4292177 < baseStart_4292177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292217 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 8]
def baseStart_4292217 : Nat := 118140960795 + 4292217 * 2 ^ 59
def prefixEnd_4292217 : Nat := 4983230072969 + 3 ^ 40 * 4292217 * 2
def baseEnd_4292217 : Nat := 244885599377704268327551

theorem tailTrace_4292217 : CollatzResearch.WordTrace tailWord_4292217 prefixEnd_4292217 244885599377704268327551 := by
  unfold tailWord_4292217
  simp only [CollatzResearch.WordTrace]
  refine ⟨156550015091038336147434905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104366676727358890764956603 156550015091038336147434905)
  ·
    refine ⟨117412511318278752110576179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156550015091038336147434905 117412511318278752110576179)
    ·
      refine ⟨176118766977418128165864269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117412511318278752110576179 176118766977418128165864269)
      ·
        refine ⟨66044537616531798062199101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176118766977418128165864269 66044537616531798062199101)
        ·
          refine ⟨24766701606199424273324663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66044537616531798062199101 24766701606199424273324663)
          ·
            refine ⟨37150052409299136409986995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24766701606199424273324663 37150052409299136409986995)
            ·
              refine ⟨55725078613948704614980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37150052409299136409986995 55725078613948704614980493)
              ·
                refine ⟨20896904480230764230617685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55725078613948704614980493 20896904480230764230617685)
                ·
                  refine ⟨244885599377704268327551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20896904480230764230617685 244885599377704268327551)
                  ·
                    rfl

theorem cell23_4292217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_4292217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292217 prefixEnd_4292217 := by exact prefixLift 4292217
  have htrace : WordTrace (prefixWord ++ tailWord_4292217) baseStart_4292217 baseEnd_4292217 := by
    simpa [prefixWord, tailWord_4292217, baseEnd_4292217] using wordTrace_append hprefix tailTrace_4292217
  have hstable : (prefixWord ++ tailWord_4292217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292217).length < 2 ^ (prefixWord ++ tailWord_4292217).sum := by decide
  have hdescent : baseEnd_4292217 < baseStart_4292217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292221 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_4292221 : Nat := 118140960795 + 4292221 * 2 ^ 59
def prefixEnd_4292221 : Nat := 4983230072969 + 3 ^ 40 * 4292221 * 2
def baseEnd_4292221 : Nat := 734657482773985466432647

theorem tailTrace_4292221 : CollatzResearch.WordTrace tailWord_4292221 prefixEnd_4292221 734657482773985466432647 := by
  unfold tailWord_4292221
  simp only [CollatzResearch.WordTrace]
  refine ⟨156550160983023844830580517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104366773988682563220387011 156550160983023844830580517)
  ·
    refine ⟨29353155184316970905733847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156550160983023844830580517 29353155184316970905733847)
    ·
      refine ⟨44029732776475456358600771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29353155184316970905733847 44029732776475456358600771)
      ·
        refine ⟨66044599164713184537901157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44029732776475456358600771 66044599164713184537901157)
        ·
          refine ⟨12383362343383722100856467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66044599164713184537901157 12383362343383722100856467)
          ·
            refine ⟨18575043515075583151284701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12383362343383722100856467 18575043515075583151284701)
            ·
              refine ⟨6965641318153343681731763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18575043515075583151284701 6965641318153343681731763)
              ·
                refine ⟨10448461977230015522597645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965641318153343681731763 10448461977230015522597645)
                ·
                  refine ⟨3918173241461255820974117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10448461977230015522597645 3918173241461255820974117)
                  ·
                    refine ⟨734657482773985466432647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918173241461255820974117 734657482773985466432647)
                    ·
                      rfl

theorem cell23_4292221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_4292221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292221 prefixEnd_4292221 := by exact prefixLift 4292221
  have htrace : WordTrace (prefixWord ++ tailWord_4292221) baseStart_4292221 baseEnd_4292221 := by
    simpa [prefixWord, tailWord_4292221, baseEnd_4292221] using wordTrace_append hprefix tailTrace_4292221
  have hstable : (prefixWord ++ tailWord_4292221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292221).length < 2 ^ (prefixWord ++ tailWord_4292221).sum := by decide
  have hdescent : baseEnd_4292221 < baseStart_4292221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292271 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 2, 3, 2]
def baseStart_4292271 : Nat := 118140960795 + 4292271 * 2 ^ 59
def prefixEnd_4292271 : Nat := 4983230072969 + 3 ^ 40 * 4292271 * 2
def baseEnd_4292271 : Nat := 2203998122354681203672711

theorem tailTrace_4292271 : CollatzResearch.WordTrace tailWord_4292271 prefixEnd_4292271 2203998122354681203672711 := by
  unfold tailWord_4292271
  simp only [CollatzResearch.WordTrace]
  refine ⟨156551984632842703369900667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104367989755228468913267111 156551984632842703369900667)
  ·
    refine ⟨234827976949264055054851001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156551984632842703369900667 234827976949264055054851001)
    ·
      refine ⟨176120982711948041291138251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234827976949264055054851001 176120982711948041291138251)
      ·
        refine ⟨264181474067922061936707377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176120982711948041291138251 264181474067922061936707377)
        ·
          refine ⟨198136105550941546452530533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264181474067922061936707377 198136105550941546452530533)
          ·
            refine ⟨37150519790801539959849475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198136105550941546452530533 37150519790801539959849475)
            ·
              refine ⟨55725779686202309939774213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37150519790801539959849475 55725779686202309939774213)
              ·
                refine ⟨10448583691162933113707665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55725779686202309939774213 10448583691162933113707665)
                ·
                  refine ⟨7836437768372199835280749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10448583691162933113707665 7836437768372199835280749)
                  ·
                    refine ⟨2938664163139574938230281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7836437768372199835280749 2938664163139574938230281)
                    ·
                      refine ⟨2203998122354681203672711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938664163139574938230281 2203998122354681203672711)
                      ·
                        rfl

theorem cell23_4292271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3, 2].length) (baseStart_4292271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292271 prefixEnd_4292271 := by exact prefixLift 4292271
  have htrace : WordTrace (prefixWord ++ tailWord_4292271) baseStart_4292271 baseEnd_4292271 := by
    simpa [prefixWord, tailWord_4292271, baseEnd_4292271] using wordTrace_append hprefix tailTrace_4292271
  have hstable : (prefixWord ++ tailWord_4292271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292271).length < 2 ^ (prefixWord ++ tailWord_4292271).sum := by decide
  have hdescent : baseEnd_4292271 < baseStart_4292271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292328 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4292328 : Nat := 118140960795 + 4292328 * 2 ^ 59
def prefixEnd_4292328 : Nat := 4983230072969 + 3 ^ 40 * 4292328 * 2
def baseEnd_4292328 : Nat := 734675796917329160219983

theorem tailTrace_4292328 : CollatzResearch.WordTrace tailWord_4292328 prefixEnd_4292328 734675796917329160219983 := by
  unfold tailWord_4292328
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277031796818101052362819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104369375729090801403150425 78277031796818101052362819)
  ·
    refine ⟨117415547695227151578544229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78277031796818101052362819 117415547695227151578544229)
    ·
      refine ⟨22015415192855090920977043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117415547695227151578544229 22015415192855090920977043)
      ·
        refine ⟨33023122789282636381465565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22015415192855090920977043 33023122789282636381465565)
        ·
          refine ⟨12383671045980988643049587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33023122789282636381465565 12383671045980988643049587)
          ·
            refine ⟨18575506568971482964574381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12383671045980988643049587 18575506568971482964574381)
            ·
              refine ⟨6965814963364306111715393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18575506568971482964574381 6965814963364306111715393)
              ·
                refine ⟨5224361222523229583786545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6965814963364306111715393 5224361222523229583786545)
                ·
                  refine ⟨3918270916892422187839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224361222523229583786545 3918270916892422187839909)
                  ·
                    refine ⟨734675796917329160219983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918270916892422187839909 734675796917329160219983)
                    ·
                      rfl

theorem cell23_4292328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4292328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292328 prefixEnd_4292328 := by exact prefixLift 4292328
  have htrace : WordTrace (prefixWord ++ tailWord_4292328) baseStart_4292328 baseEnd_4292328 := by
    simpa [prefixWord, tailWord_4292328, baseEnd_4292328] using wordTrace_append hprefix tailTrace_4292328
  have hstable : (prefixWord ++ tailWord_4292328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292328).length < 2 ^ (prefixWord ++ tailWord_4292328).sum := by decide
  have hdescent : baseEnd_4292328 < baseStart_4292328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292335 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 1, 2, 2]
def baseStart_4292335 : Nat := 118140960795 + 4292335 * 2 ^ 59
def prefixEnd_4292335 : Nat := 4983230072969 + 3 ^ 40 * 4292335 * 2
def baseEnd_4292335 : Nat := 2204030985116568953272417

theorem tailTrace_4292335 : CollatzResearch.WordTrace tailWord_4292335 prefixEnd_4292335 2204030985116568953272417 := by
  unfold tailWord_4292335
  simp only [CollatzResearch.WordTrace]
  refine ⟨156554318904610842300230459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104369545936407228200153639 156554318904610842300230459)
  ·
    refine ⟨234831478356916263450345689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156554318904610842300230459 234831478356916263450345689)
    ·
      refine ⟨176123608767687197587759267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234831478356916263450345689 176123608767687197587759267)
      ·
        refine ⟨264185413151530796381638901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176123608767687197587759267 264185413151530796381638901)
        ·
          refine ⟨24767382482956012160778647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264185413151530796381638901 24767382482956012160778647)
          ·
            refine ⟨37151073724434018241167971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24767382482956012160778647 37151073724434018241167971)
            ·
              refine ⟨55726610586651027361751957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37151073724434018241167971 55726610586651027361751957)
              ·
                refine ⟨2612184871249266907582123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55726610586651027361751957 2612184871249266907582123)
                ·
                  refine ⟨3918277306873900361373185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612184871249266907582123 3918277306873900361373185)
                  ·
                    refine ⟨2938707980155425271029889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3918277306873900361373185 2938707980155425271029889)
                    ·
                      refine ⟨2204030985116568953272417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938707980155425271029889 2204030985116568953272417)
                      ·
                        rfl

theorem cell23_4292335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 2, 2].length) (baseStart_4292335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292335 prefixEnd_4292335 := by exact prefixLift 4292335
  have htrace : WordTrace (prefixWord ++ tailWord_4292335) baseStart_4292335 baseEnd_4292335 := by
    simpa [prefixWord, tailWord_4292335, baseEnd_4292335] using wordTrace_append hprefix tailTrace_4292335
  have hstable : (prefixWord ++ tailWord_4292335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292335).length < 2 ^ (prefixWord ++ tailWord_4292335).sum := by decide
  have hdescent : baseEnd_4292335 < baseStart_4292335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292351 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_4292351 : Nat := 118140960795 + 4292351 * 2 ^ 59
def prefixEnd_4292351 : Nat := 4983230072969 + 3 ^ 40 * 4292351 * 2
def baseEnd_4292351 : Nat := 2204039200807040890672343

theorem tailTrace_4292351 : CollatzResearch.WordTrace tailWord_4292351 prefixEnd_4292351 2204039200807040890672343 := by
  unfold tailWord_4292351
  simp only [CollatzResearch.WordTrace]
  refine ⟨156554902472552877032812907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104369934981701918021875271 156554902472552877032812907)
  ·
    refine ⟨234832353708829315549219361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156554902472552877032812907 234832353708829315549219361)
    ·
      refine ⟨176124265281621986661914521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234832353708829315549219361 176124265281621986661914521)
      ·
        refine ⟨132093198961216489996435891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176124265281621986661914521 132093198961216489996435891)
        ·
          refine ⟨198139798441824734994653837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132093198961216489996435891 198139798441824734994653837)
          ·
            refine ⟨74302424415684275622995189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198139798441824734994653837 74302424415684275622995189)
            ·
              refine ⟨6965852288970400839655799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74302424415684275622995189 6965852288970400839655799)
              ·
                refine ⟨10448778433455601259483699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965852288970400839655799 10448778433455601259483699)
                ·
                  refine ⟨15673167650183401889225549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10448778433455601259483699 15673167650183401889225549)
                  ·
                    refine ⟨5877437868818775708459581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15673167650183401889225549 5877437868818775708459581)
                    ·
                      refine ⟨2204039200807040890672343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877437868818775708459581 2204039200807040890672343)
                      ·
                        rfl

theorem cell23_4292351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_4292351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292351 prefixEnd_4292351 := by exact prefixLift 4292351
  have htrace : WordTrace (prefixWord ++ tailWord_4292351) baseStart_4292351 baseEnd_4292351 := by
    simpa [prefixWord, tailWord_4292351, baseEnd_4292351] using wordTrace_append hprefix tailTrace_4292351
  have hstable : (prefixWord ++ tailWord_4292351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292351).length < 2 ^ (prefixWord ++ tailWord_4292351).sum := by decide
  have hdescent : baseEnd_4292351 < baseStart_4292351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292364 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4292364 : Nat := 118140960795 + 4292364 * 2 ^ 59
def prefixEnd_4292364 : Nat := 4983230072969 + 3 ^ 40 * 4292364 * 2
def baseEnd_4292364 : Nat := 2204045876055549339809783

theorem tailTrace_4292364 : CollatzResearch.WordTrace tailWord_4292364 prefixEnd_4292364 2204045876055549339809783 := by
  unfold tailWord_4292364
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277688310752890126518073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104370251081003853502024097 78277688310752890126518073)
  ·
    refine ⟨58708266233064667594888555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78277688310752890126518073 58708266233064667594888555)
    ·
      refine ⟨88062399349597001392332833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58708266233064667594888555 88062399349597001392332833)
      ·
        refine ⟨66046799512197751044249625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88062399349597001392332833 66046799512197751044249625)
        ·
          refine ⟨49535099634148313283187219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66046799512197751044249625 49535099634148313283187219)
          ·
            refine ⟨74302649451222469924780829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49535099634148313283187219 74302649451222469924780829)
            ·
              refine ⟨27863493544208426221792811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74302649451222469924780829 27863493544208426221792811)
              ·
                refine ⟨41795240316312639332689217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27863493544208426221792811 41795240316312639332689217)
                ·
                  refine ⟨31346430237234479499516913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41795240316312639332689217 31346430237234479499516913)
                  ·
                    refine ⟨23509822677925859624637685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31346430237234479499516913 23509822677925859624637685)
                    ·
                      refine ⟨2204045876055549339809783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23509822677925859624637685 2204045876055549339809783)
                      ·
                        rfl

theorem cell23_4292364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4292364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292364 prefixEnd_4292364 := by exact prefixLift 4292364
  have htrace : WordTrace (prefixWord ++ tailWord_4292364) baseStart_4292364 baseEnd_4292364 := by
    simpa [prefixWord, tailWord_4292364, baseEnd_4292364] using wordTrace_append hprefix tailTrace_4292364
  have hstable : (prefixWord ++ tailWord_4292364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292364).length < 2 ^ (prefixWord ++ tailWord_4292364).sum := by decide
  have hdescent : baseEnd_4292364 < baseStart_4292364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292372 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4292372 : Nat := 118140960795 + 4292372 * 2 ^ 59
def prefixEnd_4292372 : Nat := 4983230072969 + 3 ^ 40 * 4292372 * 2
def baseEnd_4292372 : Nat := 2204049983900785308509747

theorem tailTrace_4292372 : CollatzResearch.WordTrace tailWord_4292372 prefixEnd_4292372 2204049983900785308509747 := by
  unfold tailWord_4292372
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277834202738398809663685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104370445603651198412884913 78277834202738398809663685)
  ·
    refine ⟨14677093913013449776811941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78277834202738398809663685 14677093913013449776811941)
    ·
      refine ⟨2751955108690021833152239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14677093913013449776811941 2751955108690021833152239)
      ·
        refine ⟨4127932663035032749728359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751955108690021833152239 4127932663035032749728359)
        ·
          refine ⟨6191898994552549124592539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127932663035032749728359 6191898994552549124592539)
          ·
            refine ⟨9287848491828823686888809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191898994552549124592539 9287848491828823686888809)
            ·
              refine ⟨6965886368871617765166607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9287848491828823686888809 6965886368871617765166607)
              ·
                refine ⟨10448829553307426647749911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965886368871617765166607 10448829553307426647749911)
                ·
                  refine ⟨15673244329961139971624867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10448829553307426647749911 15673244329961139971624867)
                  ·
                    refine ⟨23509866494941709957437301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15673244329961139971624867 23509866494941709957437301)
                    ·
                      refine ⟨2204049983900785308509747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23509866494941709957437301 2204049983900785308509747)
                      ·
                        rfl

theorem cell23_4292372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4292372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292372 prefixEnd_4292372 := by exact prefixLift 4292372
  have htrace : WordTrace (prefixWord ++ tailWord_4292372) baseStart_4292372 baseEnd_4292372 := by
    simpa [prefixWord, tailWord_4292372, baseEnd_4292372] using wordTrace_append hprefix tailTrace_4292372
  have hstable : (prefixWord ++ tailWord_4292372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292372).length < 2 ^ (prefixWord ++ tailWord_4292372).sum := by decide
  have hdescent : baseEnd_4292372 < baseStart_4292372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292402 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_4292402 : Nat := 118140960795 + 4292402 * 2 ^ 59
def prefixEnd_4292402 : Nat := 4983230072969 + 3 ^ 40 * 4292402 * 2
def baseEnd_4292402 : Nat := 2204065388320420191134609

theorem tailTrace_4292402 : CollatzResearch.WordTrace tailWord_4292402 prefixEnd_4292402 2204065388320420191134609 := by
  unfold tailWord_4292402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39139190648842028185729865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104371175063578741828612973 39139190648842028185729865)
  ·
    refine ⟨29354392986631521139297399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39139190648842028185729865 29354392986631521139297399)
    ·
      refine ⟨44031589479947281708946099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29354392986631521139297399 44031589479947281708946099)
      ·
        refine ⟨66047384219920922563419149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44031589479947281708946099 66047384219920922563419149)
        ·
          refine ⟨24767769082470345961282181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66047384219920922563419149 24767769082470345961282181)
          ·
            refine ⟨4643956702963189867740409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24767769082470345961282181 4643956702963189867740409)
            ·
              refine ⟨3482967527222392400805307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643956702963189867740409 3482967527222392400805307)
              ·
                refine ⟨5224451290833588601207961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482967527222392400805307 5224451290833588601207961)
                ·
                  refine ⟨3918338468125191450905971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224451290833588601207961 3918338468125191450905971)
                  ·
                    refine ⟨5877507702187787176358957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918338468125191450905971 5877507702187787176358957)
                    ·
                      refine ⟨2204065388320420191134609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877507702187787176358957 2204065388320420191134609)
                      ·
                        rfl

theorem cell23_4292402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_4292402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292402 prefixEnd_4292402 := by exact prefixLift 4292402
  have htrace : WordTrace (prefixWord ++ tailWord_4292402) baseStart_4292402 baseEnd_4292402 := by
    simpa [prefixWord, tailWord_4292402, baseEnd_4292402] using wordTrace_append hprefix tailTrace_4292402
  have hstable : (prefixWord ++ tailWord_4292402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292402).length < 2 ^ (prefixWord ++ tailWord_4292402).sum := by decide
  have hdescent : baseEnd_4292402 < baseStart_4292402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292429 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4292429 : Nat := 118140960795 + 4292429 * 2 ^ 59
def prefixEnd_4292429 : Nat := 4983230072969 + 3 ^ 40 * 4292429 * 2
def baseEnd_4292429 : Nat := 2204079252298091585496985

theorem tailTrace_4292429 : CollatzResearch.WordTrace tailWord_4292429 prefixEnd_4292429 2204079252298091585496985 := by
  unfold tailWord_4292429
  simp only [CollatzResearch.WordTrace]
  refine ⟨156557747366270296354152341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104371831577513530902768227 156557747366270296354152341)
  ·
    refine ⟨7338644407793920141600891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156557747366270296354152341 7338644407793920141600891)
    ·
      refine ⟨11007966611690880212401337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7338644407793920141600891 11007966611690880212401337)
      ·
        refine ⟨8255974958768160159301003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11007966611690880212401337 8255974958768160159301003)
        ·
          refine ⟨12383962438152240238951505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8255974958768160159301003 12383962438152240238951505)
          ·
            refine ⟨9287971828614180179213629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12383962438152240238951505 9287971828614180179213629)
            ·
              refine ⟨3482989435730317567205111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9287971828614180179213629 3482989435730317567205111)
              ·
                refine ⟨5224484153595476350807667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482989435730317567205111 5224484153595476350807667)
                ·
                  refine ⟨7836726230393214526211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224484153595476350807667 7836726230393214526211501)
                  ·
                    refine ⟨2938772336397455447329313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7836726230393214526211501 2938772336397455447329313)
                    ·
                      refine ⟨2204079252298091585496985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938772336397455447329313 2204079252298091585496985)
                      ·
                        rfl

theorem cell23_4292429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4292429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292429 prefixEnd_4292429 := by exact prefixLift 4292429
  have htrace : WordTrace (prefixWord ++ tailWord_4292429) baseStart_4292429 baseEnd_4292429 := by
    simpa [prefixWord, tailWord_4292429, baseEnd_4292429] using wordTrace_append hprefix tailTrace_4292429
  have hstable : (prefixWord ++ tailWord_4292429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292429).length < 2 ^ (prefixWord ++ tailWord_4292429).sum := by decide
  have hdescent : baseEnd_4292429 < baseStart_4292429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292441 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_4292441 : Nat := 118140960795 + 4292441 * 2 ^ 59
def prefixEnd_4292441 : Nat := 4983230072969 + 3 ^ 40 * 4292441 * 2
def baseEnd_4292441 : Nat := 2204085414065945538546929

theorem tailTrace_4292441 : CollatzResearch.WordTrace tailWord_4292441 prefixEnd_4292441 2204085414065945538546929 := by
  unfold tailWord_4292441
  simp only [CollatzResearch.WordTrace]
  refine ⟨156558185042226822403589177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104372123361484548269059451 156558185042226822403589177)
  ·
    refine ⟨117418638781670116802691883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156558185042226822403589177 117418638781670116802691883)
    ·
      refine ⟨176127958172505175204037825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117418638781670116802691883 176127958172505175204037825)
      ·
        refine ⟨132095968629378881403028369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176127958172505175204037825 132095968629378881403028369)
        ·
          refine ⟨99071976472034161052271277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132095968629378881403028369 99071976472034161052271277)
          ·
            refine ⟨37151991177012810394601729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99071976472034161052271277 37151991177012810394601729)
            ·
              refine ⟨27863993382759607795951297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37151991177012810394601729 27863993382759607795951297)
              ·
                refine ⟨20897995037069705846963473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27863993382759607795951297 20897995037069705846963473)
                ·
                  refine ⟨15673496277802279385222605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20897995037069705846963473 15673496277802279385222605)
                  ·
                    refine ⟨5877561104175854769458477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15673496277802279385222605 5877561104175854769458477)
                    ·
                      refine ⟨2204085414065945538546929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877561104175854769458477 2204085414065945538546929)
                      ·
                        rfl

theorem cell23_4292441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_4292441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292441 prefixEnd_4292441 := by exact prefixLift 4292441
  have htrace : WordTrace (prefixWord ++ tailWord_4292441) baseStart_4292441 baseEnd_4292441 := by
    simpa [prefixWord, tailWord_4292441, baseEnd_4292441] using wordTrace_append hprefix tailTrace_4292441
  have hstable : (prefixWord ++ tailWord_4292441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292441).length < 2 ^ (prefixWord ++ tailWord_4292441).sum := by decide
  have hdescent : baseEnd_4292441 < baseStart_4292441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292448 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 5]
def baseStart_4292448 : Nat := 118140960795 + 4292448 * 2 ^ 59
def prefixEnd_4292448 : Nat := 4983230072969 + 3 ^ 40 * 4292448 * 2
def baseEnd_4292448 : Nat := 244898778714503001239933

theorem tailTrace_4292448 : CollatzResearch.WordTrace tailWord_4292448 prefixEnd_4292448 244898778714503001239933 := by
  unfold tailWord_4292448
  simp only [CollatzResearch.WordTrace]
  refine ⟨78279220176600731299546999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104372293568800975066062665 78279220176600731299546999)
  ·
    refine ⟨117418830264901096949320499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78279220176600731299546999 117418830264901096949320499)
    ·
      refine ⟨176128245397351645423980749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117418830264901096949320499 176128245397351645423980749)
      ·
        refine ⟨66048092024006867033992781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176128245397351645423980749 66048092024006867033992781)
        ·
          refine ⟨24768034509002575137747293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66048092024006867033992781 24768034509002575137747293)
          ·
            refine ⟨9288012940875965676655235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24768034509002575137747293 9288012940875965676655235)
            ·
              refine ⟨13932019411313948514982853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9288012940875965676655235 13932019411313948514982853)
              ·
                refine ⟨2612253639621365346559285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13932019411313948514982853 2612253639621365346559285)
                ·
                  refine ⟨244898778714503001239933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612253639621365346559285 244898778714503001239933)
                  ·
                    rfl

theorem cell23_4292448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 5].length) (baseStart_4292448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292448 prefixEnd_4292448 := by exact prefixLift 4292448
  have htrace : WordTrace (prefixWord ++ tailWord_4292448) baseStart_4292448 baseEnd_4292448 := by
    simpa [prefixWord, tailWord_4292448, baseEnd_4292448] using wordTrace_append hprefix tailTrace_4292448
  have hstable : (prefixWord ++ tailWord_4292448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292448).length < 2 ^ (prefixWord ++ tailWord_4292448).sum := by decide
  have hdescent : baseEnd_4292448 < baseStart_4292448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292461 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_4292461 : Nat := 118140960795 + 4292461 * 2 ^ 59
def prefixEnd_4292461 : Nat := 4983230072969 + 3 ^ 40 * 4292461 * 2
def baseEnd_4292461 : Nat := 734698561226345153432279

theorem tailTrace_4292461 : CollatzResearch.WordTrace tailWord_4292461 prefixEnd_4292461 734698561226345153432279 := by
  unfold tailWord_4292461
  simp only [CollatzResearch.WordTrace]
  refine ⟨156558914502154365819317237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104372609668102910546211491 156558914502154365819317237)
  ·
    refine ⟨14677398234576971795560991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156558914502154365819317237 14677398234576971795560991)
    ·
      refine ⟨22016097351865457693341487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14677398234576971795560991 22016097351865457693341487)
      ·
        refine ⟨33024146027798186540012231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22016097351865457693341487 33024146027798186540012231)
        ·
          refine ⟨49536219041697279810018347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33024146027798186540012231 49536219041697279810018347)
          ·
            refine ⟨74304328562545919715027521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49536219041697279810018347 74304328562545919715027521)
            ·
              refine ⟨55728246421909439786270641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74304328562545919715027521 55728246421909439786270641)
              ·
                refine ⟨41796184816432079839702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55728246421909439786270641 41796184816432079839702981)
                ·
                  refine ⟨7836784653081014969944309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41796184816432079839702981 7836784653081014969944309)
                  ·
                    refine ⟨734698561226345153432279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7836784653081014969944309 734698561226345153432279)
                    ·
                      rfl

theorem cell23_4292461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_4292461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292461 prefixEnd_4292461 := by exact prefixLift 4292461
  have htrace : WordTrace (prefixWord ++ tailWord_4292461) baseStart_4292461 baseEnd_4292461 := by
    simpa [prefixWord, tailWord_4292461, baseEnd_4292461] using wordTrace_append hprefix tailTrace_4292461
  have hstable : (prefixWord ++ tailWord_4292461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292461).length < 2 ^ (prefixWord ++ tailWord_4292461).sum := by decide
  have hdescent : baseEnd_4292461 < baseStart_4292461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292491 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 7, 4]
def baseStart_4292491 : Nat := 118140960795 + 4292491 * 2 ^ 59
def prefixEnd_4292491 : Nat := 4983230072969 + 3 ^ 40 * 4292491 * 2
def baseEnd_4292491 : Nat := 734703696032890114307233

theorem tailTrace_4292491 : CollatzResearch.WordTrace tailWord_4292491 prefixEnd_4292491 734703696032890114307233 := by
  unfold tailWord_4292491
  simp only [CollatzResearch.WordTrace]
  refine ⟨156560008692045680942909327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104373339128030453961939551 156560008692045680942909327)
  ·
    refine ⟨234840013038068521414363991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156560008692045680942909327 234840013038068521414363991)
    ·
      refine ⟨352260019557102782121545987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234840013038068521414363991 352260019557102782121545987)
      ·
        refine ⟨528390029335654173182318981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352260019557102782121545987 528390029335654173182318981)
        ·
          refine ⟨99073130500435157471684809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 528390029335654173182318981 99073130500435157471684809)
          ·
            refine ⟨74304847875326368103763607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99073130500435157471684809 74304847875326368103763607)
            ·
              refine ⟨111457271812989552155645411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74304847875326368103763607 111457271812989552155645411)
              ·
                refine ⟨167185907719484328233468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111457271812989552155645411 167185907719484328233468117)
                ·
                  refine ⟨3918419712175413942971909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167185907719484328233468117 3918419712175413942971909)
                  ·
                    refine ⟨734703696032890114307233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918419712175413942971909 734703696032890114307233)
                    ·
                      rfl

theorem cell23_4292491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 4].length) (baseStart_4292491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292491 prefixEnd_4292491 := by exact prefixLift 4292491
  have htrace : WordTrace (prefixWord ++ tailWord_4292491) baseStart_4292491 baseEnd_4292491 := by
    simpa [prefixWord, tailWord_4292491, baseEnd_4292491] using wordTrace_append hprefix tailTrace_4292491
  have hstable : (prefixWord ++ tailWord_4292491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292491).length < 2 ^ (prefixWord ++ tailWord_4292491).sum := by decide
  have hdescent : baseEnd_4292491 < baseStart_4292491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292531 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3]
def baseStart_4292531 : Nat := 118140960795 + 4292531 * 2 ^ 59
def prefixEnd_4292531 : Nat := 4983230072969 + 3 ^ 40 * 4292531 * 2
def baseEnd_4292531 : Nat := 2204131627324850186421515

theorem tailTrace_4292531 : CollatzResearch.WordTrace tailWord_4292531 prefixEnd_4292531 2204131627324850186421515 := by
  unfold tailWord_4292531
  simp only [CollatzResearch.WordTrace]
  refine ⟨156561467611900767774365447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104374311741267178516243631 156561467611900767774365447)
  ·
    refine ⟨234842201417851151661548171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156561467611900767774365447 234842201417851151661548171)
    ·
      refine ⟨352263302126776727492322257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234842201417851151661548171 352263302126776727492322257)
      ·
        refine ⟨264197476595082545619241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352263302126776727492322257 264197476595082545619241693)
        ·
          refine ⟨99074053723155954607215635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264197476595082545619241693 99074053723155954607215635)
          ·
            refine ⟨148611080584733931910823453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99074053723155954607215635 148611080584733931910823453)
            ·
              refine ⟨55729155219275224466558795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148611080584733931910823453 55729155219275224466558795)
              ·
                refine ⟨83593732828912836699838193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55729155219275224466558795 83593732828912836699838193)
                ·
                  refine ⟨62695299621684627524878645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83593732828912836699838193 62695299621684627524878645)
                  ·
                    refine ⟨5877684339532933830457373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62695299621684627524878645 5877684339532933830457373)
                    ·
                      refine ⟨2204131627324850186421515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877684339532933830457373 2204131627324850186421515)
                      ·
                        rfl

theorem cell23_4292531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_4292531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292531 prefixEnd_4292531 := by exact prefixLift 4292531
  have htrace : WordTrace (prefixWord ++ tailWord_4292531) baseStart_4292531 baseEnd_4292531 := by
    simpa [prefixWord, tailWord_4292531, baseEnd_4292531] using wordTrace_append hprefix tailTrace_4292531
  have hstable : (prefixWord ++ tailWord_4292531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292531).length < 2 ^ (prefixWord ++ tailWord_4292531).sum := by decide
  have hdescent : baseEnd_4292531 < baseStart_4292531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292542 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_4292542 : Nat := 118140960795 + 4292542 * 2 ^ 59
def prefixEnd_4292542 : Nat := 4983230072969 + 3 ^ 40 * 4292542 * 2
def baseEnd_4292542 : Nat := 734712425204016547794655

theorem tailTrace_4292542 : CollatzResearch.WordTrace tailWord_4292542 prefixEnd_4292542 734712425204016547794655 := by
  unfold tailWord_4292542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570233601857614581626985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104374579209907277768677253 19570233601857614581626985)
  ·
    refine ⟨14677675201393210936220239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19570233601857614581626985 14677675201393210936220239)
    ·
      refine ⟨22016512802089816404330359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14677675201393210936220239 22016512802089816404330359)
      ·
        refine ⟨33024769203134724606495539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22016512802089816404330359 33024769203134724606495539)
        ·
          refine ⟨49537153804702086909743309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33024769203134724606495539 49537153804702086909743309)
          ·
            refine ⟨18576432676763282591153741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49537153804702086909743309 18576432676763282591153741)
            ·
              refine ⟨6966162253786230971682653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18576432676763282591153741 6966162253786230971682653)
              ·
                refine ⟨2612310845169836614380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6966162253786230971682653 2612310845169836614380995)
                ·
                  refine ⟨3918466267754754921571493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612310845169836614380995 3918466267754754921571493)
                  ·
                    refine ⟨734712425204016547794655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918466267754754921571493 734712425204016547794655)
                    ·
                      rfl

theorem cell23_4292542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_4292542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292542 prefixEnd_4292542 := by exact prefixLift 4292542
  have htrace : WordTrace (prefixWord ++ tailWord_4292542) baseStart_4292542 baseEnd_4292542 := by
    simpa [prefixWord, tailWord_4292542, baseEnd_4292542] using wordTrace_append hprefix tailTrace_4292542
  have hstable : (prefixWord ++ tailWord_4292542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292542).length < 2 ^ (prefixWord ++ tailWord_4292542).sum := by decide
  have hdescent : baseEnd_4292542 < baseStart_4292542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292551 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 5, 5]
def baseStart_4292551 : Nat := 118140960795 + 4292551 * 2 ^ 59
def prefixEnd_4292551 : Nat := 4983230072969 + 3 ^ 40 * 4292551 * 2
def baseEnd_4292551 : Nat := 734713965645980036057141

theorem tailTrace_4292551 : CollatzResearch.WordTrace tailWord_4292551 prefixEnd_4292551 734713965645980036057141 := by
  unfold tailWord_4292551
  simp only [CollatzResearch.WordTrace]
  refine ⟨156562197071828311190093507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104374798047885540793395671 156562197071828311190093507)
  ·
    refine ⟨234843295607742466785140261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156562197071828311190093507 234843295607742466785140261)
    ·
      refine ⟨44033117926451712522213799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234843295607742466785140261 44033117926451712522213799)
      ·
        refine ⟨66049676889677568783320699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44033117926451712522213799 66049676889677568783320699)
        ·
          refine ⟨99074515334516353174981049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66049676889677568783320699 99074515334516353174981049)
          ·
            refine ⟨74305886500887264881235787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99074515334516353174981049 74305886500887264881235787)
            ·
              refine ⟨111458829751330897321853681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74305886500887264881235787 111458829751330897321853681)
              ·
                refine ⟨83594122313498172991390261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111458829751330897321853681 83594122313498172991390261)
                ·
                  refine ⟨7836948966890453717942837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83594122313498172991390261 7836948966890453717942837)
                  ·
                    refine ⟨734713965645980036057141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7836948966890453717942837 734713965645980036057141)
                    ·
                      rfl

theorem cell23_4292551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_4292551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292551 prefixEnd_4292551 := by exact prefixLift 4292551
  have htrace : WordTrace (prefixWord ++ tailWord_4292551) baseStart_4292551 baseEnd_4292551 := by
    simpa [prefixWord, tailWord_4292551, baseEnd_4292551] using wordTrace_append hprefix tailTrace_4292551
  have hstable : (prefixWord ++ tailWord_4292551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292551).length < 2 ^ (prefixWord ++ tailWord_4292551).sum := by decide
  have hdescent : baseEnd_4292551 < baseStart_4292551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292588 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_4292588 : Nat := 118140960795 + 4292588 * 2 ^ 59
def prefixEnd_4292588 : Nat := 4983230072969 + 3 ^ 40 * 4292588 * 2
def baseEnd_4292588 : Nat := 2204160895722156463408753

theorem tailTrace_4292588 : CollatzResearch.WordTrace tailWord_4292588 prefixEnd_4292588 2204160895722156463408753 := by
  unfold tailWord_4292588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78281773286347133254595209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104375697715129511006126945 78281773286347133254595209)
  ·
    refine ⟨58711329964760349940946407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78281773286347133254595209 58711329964760349940946407)
    ·
      refine ⟨88066994947140524911419611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58711329964760349940946407 88066994947140524911419611)
      ·
        refine ⟨132100492420710787367129417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88066994947140524911419611 132100492420710787367129417)
        ·
          refine ⟨99075369315533090525347063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132100492420710787367129417 99075369315533090525347063)
          ·
            refine ⟨148613053973299635788020595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99075369315533090525347063 148613053973299635788020595)
            ·
              refine ⟨222919580959949453682030893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148613053973299635788020595 222919580959949453682030893)
              ·
                refine ⟨83594842859981045130761585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222919580959949453682030893 83594842859981045130761585)
                ·
                  refine ⟨62696132144985783848071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83594842859981045130761585 62696132144985783848071189)
                  ·
                    refine ⟨2938881194296208617878337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62696132144985783848071189 2938881194296208617878337)
                    ·
                      refine ⟨2204160895722156463408753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938881194296208617878337 2204160895722156463408753)
                      ·
                        rfl

theorem cell23_4292588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_4292588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292588 prefixEnd_4292588 := by exact prefixLift 4292588
  have htrace : WordTrace (prefixWord ++ tailWord_4292588) baseStart_4292588 baseEnd_4292588 := by
    simpa [prefixWord, tailWord_4292588, baseEnd_4292588] using wordTrace_append hprefix tailTrace_4292588
  have hstable : (prefixWord ++ tailWord_4292588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292588).length < 2 ^ (prefixWord ++ tailWord_4292588).sum := by decide
  have hdescent : baseEnd_4292588 < baseStart_4292588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292615 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 2, 4]
def baseStart_4292615 : Nat := 118140960795 + 4292615 * 2 ^ 59
def prefixEnd_4292615 : Nat := 4983230072969 + 3 ^ 40 * 4292615 * 2
def baseEnd_4292615 : Nat := 734724919899942619257043

theorem tailTrace_4292615 : CollatzResearch.WordTrace tailWord_4292615 prefixEnd_4292615 734724919899942619257043 := by
  unfold tailWord_4292615
  simp only [CollatzResearch.WordTrace]
  refine ⟨156564531343596450120423299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104376354229064300080282199 156564531343596450120423299)
  ·
    refine ⟨234846797015394675180634949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156564531343596450120423299 234846797015394675180634949)
    ·
      refine ⟨44033774440386501596369053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234846797015394675180634949 44033774440386501596369053)
      ·
        refine ⟨16512665415144938098638395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44033774440386501596369053 16512665415144938098638395)
        ·
          refine ⟨24768998122717407147957593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16512665415144938098638395 24768998122717407147957593)
          ·
            refine ⟨18576748592038055360968195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24768998122717407147957593 18576748592038055360968195)
            ·
              refine ⟨27865122888057083041452293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18576748592038055360968195 27865122888057083041452293)
              ·
                refine ⟨5224710541510703070272305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27865122888057083041452293 5224710541510703070272305)
                ·
                  refine ⟨3918532906133027302704229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224710541510703070272305 3918532906133027302704229)
                  ·
                    refine ⟨734724919899942619257043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918532906133027302704229 734724919899942619257043)
                    ·
                      rfl

theorem cell23_4292615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_4292615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292615 prefixEnd_4292615 := by exact prefixLift 4292615
  have htrace : WordTrace (prefixWord ++ tailWord_4292615) baseStart_4292615 baseEnd_4292615 := by
    simpa [prefixWord, tailWord_4292615, baseEnd_4292615] using wordTrace_append hprefix tailTrace_4292615
  have hstable : (prefixWord ++ tailWord_4292615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292615).length < 2 ^ (prefixWord ++ tailWord_4292615).sum := by decide
  have hdescent : baseEnd_4292615 < baseStart_4292615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292622 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4292622 : Nat := 118140960795 + 4292622 * 2 ^ 59
def prefixEnd_4292622 : Nat := 4983230072969 + 3 ^ 40 * 4292622 * 2
def baseEnd_4292622 : Nat := 2204178354064409330383597

theorem tailTrace_4292622 : CollatzResearch.WordTrace tailWord_4292622 prefixEnd_4292622 2204178354064409330383597 := by
  unfold tailWord_4292622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570598331821386289491015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104376524436380726877285413 19570598331821386289491015)
  ·
    refine ⟨29355897497732079434236523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19570598331821386289491015 29355897497732079434236523)
    ·
      refine ⟨44033846246598119151354785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29355897497732079434236523 44033846246598119151354785)
      ·
        refine ⟨33025384684948589363516089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44033846246598119151354785 33025384684948589363516089)
        ·
          refine ⟨24769038513711442022637067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33025384684948589363516089 24769038513711442022637067)
          ·
            refine ⟨37153557770567163033955601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24769038513711442022637067 37153557770567163033955601)
            ·
              refine ⟨27865168327925372275466701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37153557770567163033955601 27865168327925372275466701)
              ·
                refine ⟨10449438122972014603300013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27865168327925372275466701 10449438122972014603300013)
                ·
                  refine ⟨3918539296114505476237505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10449438122972014603300013 3918539296114505476237505)
                  ·
                    refine ⟨2938904472085879107178129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3918539296114505476237505 2938904472085879107178129)
                    ·
                      refine ⟨2204178354064409330383597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938904472085879107178129 2204178354064409330383597)
                      ·
                        rfl

theorem cell23_4292622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4292622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292622 prefixEnd_4292622 := by exact prefixLift 4292622
  have htrace : WordTrace (prefixWord ++ tailWord_4292622) baseStart_4292622 baseEnd_4292622 := by
    simpa [prefixWord, tailWord_4292622, baseEnd_4292622] using wordTrace_append hprefix tailTrace_4292622
  have hstable : (prefixWord ++ tailWord_4292622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292622).length < 2 ^ (prefixWord ++ tailWord_4292622).sum := by decide
  have hdescent : baseEnd_4292622 < baseStart_4292622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292672 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_4292672 : Nat := 118140960795 + 4292672 * 2 ^ 59
def prefixEnd_4292672 : Nat := 4983230072969 + 3 ^ 40 * 4292672 * 2
def baseEnd_4292672 : Nat := 2204204028097134134758367

theorem tailTrace_4292672 : CollatzResearch.WordTrace tailWord_4292672 prefixEnd_4292672 2204204028097134134758367 := by
  unfold tailWord_4292672
  simp only [CollatzResearch.WordTrace]
  refine ⟨78283305152194974427624135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104377740202926632570165513 78283305152194974427624135)
  ·
    refine ⟨117424957728292461641436203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78283305152194974427624135 117424957728292461641436203)
    ·
      refine ⟨176137436592438692462154305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117424957728292461641436203 176137436592438692462154305)
      ·
        refine ⟨132103077444329019346615729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176137436592438692462154305 132103077444329019346615729)
        ·
          refine ⟨99077308083246764509961797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132103077444329019346615729 99077308083246764509961797)
          ·
            refine ⟨18576995265608768345617837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99077308083246764509961797 18576995265608768345617837)
            ·
              refine ⟨6966373224603288129606689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18576995265608768345617837 6966373224603288129606689)
              ·
                refine ⟨5224779918452466097205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966373224603288129606689 5224779918452466097205017)
                ·
                  refine ⟨3918584938839349572903763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224779918452466097205017 3918584938839349572903763)
                  ·
                    refine ⟨5877877408259024359355645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918584938839349572903763 5877877408259024359355645)
                    ·
                      refine ⟨2204204028097134134758367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5877877408259024359355645 2204204028097134134758367)
                      ·
                        rfl

theorem cell23_4292672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_4292672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292672 prefixEnd_4292672 := by exact prefixLift 4292672
  have htrace : WordTrace (prefixWord ++ tailWord_4292672) baseStart_4292672 baseEnd_4292672 := by
    simpa [prefixWord, tailWord_4292672, baseEnd_4292672] using wordTrace_append hprefix tailTrace_4292672
  have hstable : (prefixWord ++ tailWord_4292672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292672).length < 2 ^ (prefixWord ++ tailWord_4292672).sum := by decide
  have hdescent : baseEnd_4292672 < baseStart_4292672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292698 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4292698 : Nat := 118140960795 + 4292698 * 2 ^ 59
def prefixEnd_4292698 : Nat := 4983230072969 + 3 ^ 40 * 4292698 * 2
def baseEnd_4292698 : Nat := 2204217378594151033033247

theorem tailTrace_4292698 : CollatzResearch.WordTrace tailWord_4292698 prefixEnd_4292698 2204217378594151033033247 := by
  unfold tailWord_4292698
  simp only [CollatzResearch.WordTrace]
  refine ⟨39141889650573938823923687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104378372401530503530463165 39141889650573938823923687)
  ·
    refine ⟨58712834475860908235885531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39141889650573938823923687 58712834475860908235885531)
    ·
      refine ⟨88069251713791362353828297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58712834475860908235885531 88069251713791362353828297)
      ·
        refine ⟨66051938785343521765371223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88069251713791362353828297 66051938785343521765371223)
        ·
          refine ⟨99077908178015282648056835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66051938785343521765371223 99077908178015282648056835)
          ·
            refine ⟨148616862267022923972085253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99077908178015282648056835 148616862267022923972085253)
            ·
              refine ⟨27865661675066798244765985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148616862267022923972085253 27865661675066798244765985)
              ·
                refine ⟨20899246256300098683574489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27865661675066798244765985 20899246256300098683574489)
                ·
                  refine ⟨15674434692225074012680867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20899246256300098683574489 15674434692225074012680867)
                  ·
                    refine ⟨23511652038337611019021301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15674434692225074012680867 23511652038337611019021301)
                    ·
                      refine ⟨2204217378594151033033247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23511652038337611019021301 2204217378594151033033247)
                      ·
                        rfl

theorem cell23_4292698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4292698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292698 prefixEnd_4292698 := by exact prefixLift 4292698
  have htrace : WordTrace (prefixWord ++ tailWord_4292698) baseStart_4292698 baseEnd_4292698 := by
    simpa [prefixWord, tailWord_4292698, baseEnd_4292698] using wordTrace_append hprefix tailTrace_4292698
  have hstable : (prefixWord ++ tailWord_4292698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292698).length < 2 ^ (prefixWord ++ tailWord_4292698).sum := by decide
  have hdescent : baseEnd_4292698 < baseStart_4292698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292708 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4292708 : Nat := 118140960795 + 4292708 * 2 ^ 59
def prefixEnd_4292708 : Nat := 4983230072969 + 3 ^ 40 * 4292708 * 2
def baseEnd_4292708 : Nat := 2204222513400695993908201

theorem tailTrace_4292708 : CollatzResearch.WordTrace tailWord_4292708 prefixEnd_4292708 2204222513400695993908201 := by
  unfold tailWord_4292708
  simp only [CollatzResearch.WordTrace]
  refine ⟨78283961666129763501779389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104378615554839684669039185 78283961666129763501779389)
  ·
    refine ⟨29356485624798661313167271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78283961666129763501779389 29356485624798661313167271)
    ·
      refine ⟨44034728437197991969750907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29356485624798661313167271 44034728437197991969750907)
      ·
        refine ⟨66052092655796987954626361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44034728437197991969750907 66052092655796987954626361)
        ·
          refine ⟨49539069491847740965969771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66052092655796987954626361 49539069491847740965969771)
          ·
            refine ⟨74308604237771611448954657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49539069491847740965969771 74308604237771611448954657)
            ·
              refine ⟨55731453178328708586715993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74308604237771611448954657 55731453178328708586715993)
              ·
                refine ⟨41798589883746531440036995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55731453178328708586715993 41798589883746531440036995)
                ·
                  refine ⟨62697884825619797160055493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41798589883746531440036995 62697884825619797160055493)
                  ·
                    refine ⟨11755853404803711967510405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62697884825619797160055493 11755853404803711967510405)
                    ·
                      refine ⟨2204222513400695993908201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11755853404803711967510405 2204222513400695993908201)
                      ·
                        rfl

theorem cell23_4292708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4292708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292708 prefixEnd_4292708 := by exact prefixLift 4292708
  have htrace : WordTrace (prefixWord ++ tailWord_4292708) baseStart_4292708 baseEnd_4292708 := by
    simpa [prefixWord, tailWord_4292708, baseEnd_4292708] using wordTrace_append hprefix tailTrace_4292708
  have hstable : (prefixWord ++ tailWord_4292708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292708).length < 2 ^ (prefixWord ++ tailWord_4292708).sum := by decide
  have hdescent : baseEnd_4292708 < baseStart_4292708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292746 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4292746 : Nat := 118140960795 + 4292746 * 2 ^ 59
def prefixEnd_4292746 : Nat := 4983230072969 + 3 ^ 40 * 4292746 * 2
def baseEnd_4292746 : Nat := 2204242025665566845233027

theorem tailTrace_4292746 : CollatzResearch.WordTrace tailWord_4292746 prefixEnd_4292746 2204242025665566845233027 := by
  unfold tailWord_4292746
  simp only [CollatzResearch.WordTrace]
  refine ⟨39142327326530464873360523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104379539537414572995628061 39142327326530464873360523)
  ·
    refine ⟨58713490989795697310040785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39142327326530464873360523 58713490989795697310040785)
    ·
      refine ⟨44035118242346772982530589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58713490989795697310040785 44035118242346772982530589)
      ·
        refine ⟨16513169340880039868448971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44035118242346772982530589 16513169340880039868448971)
        ·
          refine ⟨24769754011320059802673457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16513169340880039868448971 24769754011320059802673457)
          ·
            refine ⟨18577315508490044852005093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24769754011320059802673457 18577315508490044852005093)
            ·
              refine ⟨3483246657841883409750955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18577315508490044852005093 3483246657841883409750955)
              ·
                refine ⟨5224869986762825114626433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483246657841883409750955 5224869986762825114626433)
                ·
                  refine ⟨3918652490072118835969825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5224869986762825114626433 3918652490072118835969825)
                  ·
                    refine ⟨2938989367554089126977369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3918652490072118835969825 2938989367554089126977369)
                    ·
                      refine ⟨2204242025665566845233027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2938989367554089126977369 2204242025665566845233027)
                      ·
                        rfl

theorem cell23_4292746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4292746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292746 prefixEnd_4292746 := by exact prefixLift 4292746
  have htrace : WordTrace (prefixWord ++ tailWord_4292746) baseStart_4292746 baseEnd_4292746 := by
    simpa [prefixWord, tailWord_4292746, baseEnd_4292746] using wordTrace_append hprefix tailTrace_4292746
  have hstable : (prefixWord ++ tailWord_4292746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292746).length < 2 ^ (prefixWord ++ tailWord_4292746).sum := by decide
  have hdescent : baseEnd_4292746 < baseStart_4292746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292765 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4292765 : Nat := 118140960795 + 4292765 * 2 ^ 59
def prefixEnd_4292765 : Nat := 4983230072969 + 3 ^ 40 * 4292765 * 2
def baseEnd_4292765 : Nat := 734750593932667423631813

theorem tailTrace_4292765 : CollatzResearch.WordTrace tailWord_4292765 prefixEnd_4292765 734750593932667423631813 := by
  unfold tailWord_4292765
  simp only [CollatzResearch.WordTrace]
  refine ⟨156570002293053025738383749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104380001528702017158922499 156570002293053025738383749)
  ·
    refine ⟨29356875429947442325946953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156570002293053025738383749 29356875429947442325946953)
    ·
      refine ⟨22017656572460581744460215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29356875429947442325946953 22017656572460581744460215)
      ·
        refine ⟨33026484858690872616690323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22017656572460581744460215 33026484858690872616690323)
        ·
          refine ⟨49539727288036308925035485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33026484858690872616690323 49539727288036308925035485)
          ·
            refine ⟨18577397733013615846888307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49539727288036308925035485 18577397733013615846888307)
            ·
              refine ⟨27866096599520423770332461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18577397733013615846888307 27866096599520423770332461)
              ·
                refine ⟨10449786224820158913874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27866096599520423770332461 10449786224820158913874673)
                ·
                  refine ⟨7837339668615119185406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10449786224820158913874673 7837339668615119185406005)
                  ·
                    refine ⟨734750593932667423631813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7837339668615119185406005 734750593932667423631813)
                    ·
                      rfl

theorem cell23_4292765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4292765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292765 prefixEnd_4292765 := by exact prefixLift 4292765
  have htrace : WordTrace (prefixWord ++ tailWord_4292765) baseStart_4292765 baseEnd_4292765 := by
    simpa [prefixWord, tailWord_4292765, baseEnd_4292765] using wordTrace_append hprefix tailTrace_4292765
  have hstable : (prefixWord ++ tailWord_4292765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292765).length < 2 ^ (prefixWord ++ tailWord_4292765).sum := by decide
  have hdescent : baseEnd_4292765 < baseStart_4292765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292795 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 3, 4]
def baseStart_4292795 : Nat := 118140960795 + 4292795 * 2 ^ 59
def prefixEnd_4292795 : Nat := 4983230072969 + 3 ^ 40 * 4292795 * 2
def baseEnd_4292795 : Nat := 734755728739212384506767

theorem tailTrace_4292795 : CollatzResearch.WordTrace tailWord_4292795 prefixEnd_4292795 734755728739212384506767 := by
  unfold tailWord_4292795
  simp only [CollatzResearch.WordTrace]
  refine ⟨156571096482944340861975839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104380730988629560574650559 156571096482944340861975839)
  ·
    refine ⟨234856644724416511292963759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156571096482944340861975839 234856644724416511292963759)
    ·
      refine ⟨352284967086624766939445639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234856644724416511292963759 352284967086624766939445639)
      ·
        refine ⟨528427450629937150409168459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352284967086624766939445639 528427450629937150409168459)
        ·
          refine ⟨792641175944905725613752689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528427450629937150409168459 792641175944905725613752689)
          ·
            refine ⟨594480881958679294210314517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792641175944905725613752689 594480881958679294210314517)
            ·
              refine ⟨27866291341813091916108493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 594480881958679294210314517 27866291341813091916108493)
              ·
                refine ⟨10449859253179909468540685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27866291341813091916108493 10449859253179909468540685)
                ·
                  refine ⟨3918697219942466050702757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10449859253179909468540685 3918697219942466050702757)
                  ·
                    refine ⟨734755728739212384506767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918697219942466050702757 734755728739212384506767)
                    ·
                      rfl

theorem cell23_4292795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 4].length) (baseStart_4292795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292795 prefixEnd_4292795 := by exact prefixLift 4292795
  have htrace : WordTrace (prefixWord ++ tailWord_4292795) baseStart_4292795 baseEnd_4292795 := by
    simpa [prefixWord, tailWord_4292795, baseEnd_4292795] using wordTrace_append hprefix tailTrace_4292795
  have hstable : (prefixWord ++ tailWord_4292795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292795).length < 2 ^ (prefixWord ++ tailWord_4292795).sum := by decide
  have hdescent : baseEnd_4292795 < baseStart_4292795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292805 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_4292805 : Nat := 118140960795 + 4292805 * 2 ^ 59
def prefixEnd_4292805 : Nat := 4983230072969 + 3 ^ 40 * 4292805 * 2
def baseEnd_4292805 : Nat := 2204272321024182114395255

theorem tailTrace_4292805 : CollatzResearch.WordTrace tailWord_4292805 prefixEnd_4292805 2204272321024182114395255 := by
  unfold tailWord_4292805
  simp only [CollatzResearch.WordTrace]
  refine ⟨156571461212908112569839869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104380974141938741713226579 156571461212908112569839869)
  ·
    refine ⟨58714297954840542213689951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156571461212908112569839869 58714297954840542213689951)
    ·
      refine ⟨88071446932260813320534927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58714297954840542213689951 88071446932260813320534927)
      ·
        refine ⟨132107170398391219980802391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88071446932260813320534927 132107170398391219980802391)
        ·
          refine ⟨198160755597586829971203587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132107170398391219980802391 198160755597586829971203587)
          ·
            refine ⟨297241133396380244956805381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198160755597586829971203587 297241133396380244956805381)
            ·
              refine ⟨55732712511821295929401009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297241133396380244956805381 55732712511821295929401009)
              ·
                refine ⟨41799534383865971947050757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55732712511821295929401009 41799534383865971947050757)
                ·
                  refine ⟨7837412696974869740072017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41799534383865971947050757 7837412696974869740072017)
                  ·
                    refine ⟨5878059522731152305054013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7837412696974869740072017 5878059522731152305054013)
                    ·
                      refine ⟨2204272321024182114395255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878059522731152305054013 2204272321024182114395255)
                      ·
                        rfl

theorem cell23_4292805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_4292805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292805 prefixEnd_4292805 := by exact prefixLift 4292805
  have htrace : WordTrace (prefixWord ++ tailWord_4292805) baseStart_4292805 baseEnd_4292805 := by
    simpa [prefixWord, tailWord_4292805, baseEnd_4292805] using wordTrace_append hprefix tailTrace_4292805
  have hstable : (prefixWord ++ tailWord_4292805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292805).length < 2 ^ (prefixWord ++ tailWord_4292805).sum := by decide
  have hdescent : baseEnd_4292805 < baseStart_4292805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292808 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 10]
def baseStart_4292808 : Nat := 118140960795 + 4292808 * 2 ^ 59
def prefixEnd_4292808 : Nat := 4983230072969 + 3 ^ 40 * 4292808 * 2
def baseEnd_4292808 : Nat := 244919317940682844739749

theorem tailTrace_4292808 : CollatzResearch.WordTrace tailWord_4292808 prefixEnd_4292808 244919317940682844739749 := by
  unfold tailWord_4292808
  simp only [CollatzResearch.WordTrace]
  refine ⟨78285785315948622041099539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104381047087931496054799385 78285785315948622041099539)
  ·
    refine ⟨117428677973922933061649309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78285785315948622041099539 117428677973922933061649309)
    ·
      refine ⟨44035754240221099898118491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117428677973922933061649309 44035754240221099898118491)
      ·
        refine ⟨66053631360331649847177737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44035754240221099898118491 66053631360331649847177737)
        ·
          refine ⟨49540223520248737385383303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66053631360331649847177737 49540223520248737385383303)
          ·
            refine ⟨74310335280373106078074955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49540223520248737385383303 74310335280373106078074955)
            ·
              refine ⟨111465502920559659117112433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74310335280373106078074955 111465502920559659117112433)
              ·
                refine ⟨83599127190419744337834325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111465502920559659117112433 83599127190419744337834325)
                ·
                  refine ⟨244919317940682844739749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83599127190419744337834325 244919317940682844739749)
                  ·
                    rfl

theorem cell23_4292808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_4292808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292808 prefixEnd_4292808 := by exact prefixLift 4292808
  have htrace : WordTrace (prefixWord ++ tailWord_4292808) baseStart_4292808 baseEnd_4292808 := by
    simpa [prefixWord, tailWord_4292808, baseEnd_4292808] using wordTrace_append hprefix tailTrace_4292808
  have hstable : (prefixWord ++ tailWord_4292808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292808).length < 2 ^ (prefixWord ++ tailWord_4292808).sum := by decide
  have hdescent : baseEnd_4292808 < baseStart_4292808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292872 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_4292872 : Nat := 118140960795 + 4292872 * 2 ^ 59
def prefixEnd_4292872 : Nat := 4983230072969 + 3 ^ 40 * 4292872 * 2
def baseEnd_4292872 : Nat := 734768908076011117419149

theorem tailTrace_4292872 : CollatzResearch.WordTrace tailWord_4292872 prefixEnd_4292872 734768908076011117419149 := by
  unfold tailWord_4292872
  simp only [CollatzResearch.WordTrace]
  refine ⟨78286952451832691506264435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104382603269110255341685913 78286952451832691506264435)
  ·
    refine ⟨117430428677749037259396653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78286952451832691506264435 117430428677749037259396653)
    ·
      refine ⟨44036410754155888972273745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117430428677749037259396653 44036410754155888972273745)
      ·
        refine ⟨33027308065616916729205309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44036410754155888972273745 33027308065616916729205309)
        ·
          refine ⟨12385240524606343773451991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33027308065616916729205309 12385240524606343773451991)
          ·
            refine ⟨18577860786909515660177987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12385240524606343773451991 18577860786909515660177987)
            ·
              refine ⟨27866791180364273490266981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18577860786909515660177987 27866791180364273490266981)
              ·
                refine ⟨5225023346318301279425059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27866791180364273490266981 5225023346318301279425059)
                ·
                  refine ⟨7837535019477451919137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5225023346318301279425059 7837535019477451919137589)
                  ·
                    refine ⟨734768908076011117419149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7837535019477451919137589 734768908076011117419149)
                    ·
                      rfl

theorem cell23_4292872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_4292872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292872 prefixEnd_4292872 := by exact prefixLift 4292872
  have htrace : WordTrace (prefixWord ++ tailWord_4292872) baseStart_4292872 baseEnd_4292872 := by
    simpa [prefixWord, tailWord_4292872, baseEnd_4292872] using wordTrace_append hprefix tailTrace_4292872
  have hstable : (prefixWord ++ tailWord_4292872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292872).length < 2 ^ (prefixWord ++ tailWord_4292872).sum := by decide
  have hdescent : baseEnd_4292872 < baseStart_4292872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292885 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4292885 : Nat := 118140960795 + 4292885 * 2 ^ 59
def prefixEnd_4292885 : Nat := 4983230072969 + 3 ^ 40 * 4292885 * 2
def baseEnd_4292885 : Nat := 734771133158847267131629

theorem tailTrace_4292885 : CollatzResearch.WordTrace tailWord_4292885 prefixEnd_4292885 734771133158847267131629 := by
  unfold tailWord_4292885
  simp only [CollatzResearch.WordTrace]
  refine ⟨156574379052618286232752109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104382919368412190821834739 156574379052618286232752109)
  ·
    refine ⟨58715392144731857337282041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156574379052618286232752109 58715392144731857337282041)
    ·
      refine ⟨44036544108548893002961531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58715392144731857337282041 44036544108548893002961531)
      ·
        refine ⟨66054816162823339504442297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44036544108548893002961531 66054816162823339504442297)
        ·
          refine ⟨49541112122117504628331723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66054816162823339504442297 49541112122117504628331723)
          ·
            refine ⟨74311668183176256942497585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49541112122117504628331723 74311668183176256942497585)
            ·
              refine ⟨55733751137382192706873189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74311668183176256942497585 55733751137382192706873189)
              ·
                refine ⟨10450078338259161132538723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55733751137382192706873189 10450078338259161132538723)
                ·
                  refine ⟨15675117507388741698808085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10450078338259161132538723 15675117507388741698808085)
                  ·
                    refine ⟨734771133158847267131629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15675117507388741698808085 734771133158847267131629)
                    ·
                      rfl

theorem cell23_4292885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4292885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292885 prefixEnd_4292885 := by exact prefixLift 4292885
  have htrace : WordTrace (prefixWord ++ tailWord_4292885) baseStart_4292885 baseEnd_4292885 := by
    simpa [prefixWord, tailWord_4292885, baseEnd_4292885] using wordTrace_append hprefix tailTrace_4292885
  have hstable : (prefixWord ++ tailWord_4292885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292885).length < 2 ^ (prefixWord ++ tailWord_4292885).sum := by decide
  have hdescent : baseEnd_4292885 < baseStart_4292885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292915 : List Nat := [1, 1, 1, 2, 5, 1, 4, 8]
def baseStart_4292915 : Nat := 118140960795 + 4292915 * 2 ^ 59
def prefixEnd_4292915 : Nat := 4983230072969 + 3 ^ 40 * 4292915 * 2
def baseEnd_4292915 : Nat := 81641807551710247556287

theorem tailTrace_4292915 : CollatzResearch.WordTrace tailWord_4292915 prefixEnd_4292915 81641807551710247556287 := by
  unfold tailWord_4292915
  simp only [CollatzResearch.WordTrace]
  refine ⟨156575473242509601356344199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104383648828339734237562799 156575473242509601356344199)
  ·
    refine ⟨234863209863764402034516299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156575473242509601356344199 234863209863764402034516299)
    ·
      refine ⟨352294814795646603051774449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234863209863764402034516299 352294814795646603051774449)
      ·
        refine ⟨264221111096734952288830837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352294814795646603051774449 264221111096734952288830837)
        ·
          refine ⟨24770729165318901777077891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264221111096734952288830837 24770729165318901777077891)
          ·
            refine ⟨37156093747978352665616837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24770729165318901777077891 37156093747978352665616837)
            ·
              refine ⟨6966767577745941124803157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37156093747978352665616837 6966767577745941124803157)
              ·
                refine ⟨81641807551710247556287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6966767577745941124803157 81641807551710247556287)
                ·
                  rfl

theorem cell23_4292915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 8].length) (baseStart_4292915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292915 prefixEnd_4292915 := by exact prefixLift 4292915
  have htrace : WordTrace (prefixWord ++ tailWord_4292915) baseStart_4292915 baseEnd_4292915 := by
    simpa [prefixWord, tailWord_4292915, baseEnd_4292915] using wordTrace_append hprefix tailTrace_4292915
  have hstable : (prefixWord ++ tailWord_4292915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292915).length < 2 ^ (prefixWord ++ tailWord_4292915).sum := by decide
  have hdescent : baseEnd_4292915 < baseStart_4292915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292926 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4292926 : Nat := 118140960795 + 4292926 * 2 ^ 59
def prefixEnd_4292926 : Nat := 4983230072969 + 3 ^ 40 * 4292926 * 2
def baseEnd_4292926 : Nat := 2204334452183376140982199

theorem tailTrace_4292926 : CollatzResearch.WordTrace tailWord_4292926 prefixEnd_4292926 2204334452183376140982199 := by
  unfold tailWord_4292926
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571984305683718779374329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104383916296979833489996421 19571984305683718779374329)
  ·
    refine ⟨14678988229262789084530747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19571984305683718779374329 14678988229262789084530747)
    ·
      refine ⟨22018482343894183626796121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14678988229262789084530747 22018482343894183626796121)
      ·
        refine ⟨16513861757920637720097091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22018482343894183626796121 16513861757920637720097091)
        ·
          refine ⟨24770792636880956580145637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16513861757920637720097091 24770792636880956580145637)
          ·
            refine ⟨4644523619415179358777307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24770792636880956580145637 4644523619415179358777307)
            ·
              refine ⟨6966785429122769038165961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644523619415179358777307 6966785429122769038165961)
              ·
                refine ⟨5225089071842076778624471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966785429122769038165961 5225089071842076778624471)
                ·
                  refine ⟨7837633607763115167936707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5225089071842076778624471 7837633607763115167936707)
                  ·
                    refine ⟨11756450411644672751905061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7837633607763115167936707 11756450411644672751905061)
                    ·
                      refine ⟨2204334452183376140982199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11756450411644672751905061 2204334452183376140982199)
                      ·
                        rfl

theorem cell23_4292926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4292926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292926 prefixEnd_4292926 := by exact prefixLift 4292926
  have htrace : WordTrace (prefixWord ++ tailWord_4292926) baseStart_4292926 baseEnd_4292926 := by
    simpa [prefixWord, tailWord_4292926, baseEnd_4292926] using wordTrace_append hprefix tailTrace_4292926
  have hstable : (prefixWord ++ tailWord_4292926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292926).length < 2 ^ (prefixWord ++ tailWord_4292926).sum := by decide
  have hdescent : baseEnd_4292926 < baseStart_4292926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292959 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_4292959 : Nat := 118140960795 + 4292959 * 2 ^ 59
def prefixEnd_4292959 : Nat := 4983230072969 + 3 ^ 40 * 4292959 * 2
def baseEnd_4292959 : Nat := 2204351397044974511869547

theorem tailTrace_4292959 : CollatzResearch.WordTrace tailWord_4292959 prefixEnd_4292959 2204351397044974511869547 := by
  unfold tailWord_4292959
  simp only [CollatzResearch.WordTrace]
  refine ⟨156577078054350196870945931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104384718702900131247297287 156577078054350196870945931)
  ·
    refine ⟨234865617081525295306418897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156577078054350196870945931 234865617081525295306418897)
    ·
      refine ⟨176149212811143971479814173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234865617081525295306418897 176149212811143971479814173)
      ·
        refine ⟨66055954804178989304930315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176149212811143971479814173 66055954804178989304930315)
        ·
          refine ⟨99083932206268483957395473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66055954804178989304930315 99083932206268483957395473)
          ·
            refine ⟨74312949154701362968046605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99083932206268483957395473 74312949154701362968046605)
            ·
              refine ⟨27867355933013011113017477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74312949154701362968046605 27867355933013011113017477)
              ·
                refine ⟨5225129237439939583690777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27867355933013011113017477 5225129237439939583690777)
                ·
                  refine ⟨3918846928079954687768083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5225129237439939583690777 3918846928079954687768083)
                  ·
                    refine ⟨5878270392119932031652125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918846928079954687768083 5878270392119932031652125)
                    ·
                      refine ⟨2204351397044974511869547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878270392119932031652125 2204351397044974511869547)
                      ·
                        rfl

theorem cell23_4292959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_4292959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292959 prefixEnd_4292959 := by exact prefixLift 4292959
  have htrace : WordTrace (prefixWord ++ tailWord_4292959) baseStart_4292959 baseEnd_4292959 := by
    simpa [prefixWord, tailWord_4292959, baseEnd_4292959] using wordTrace_append hprefix tailTrace_4292959
  have hstable : (prefixWord ++ tailWord_4292959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292959).length < 2 ^ (prefixWord ++ tailWord_4292959).sum := by decide
  have hdescent : baseEnd_4292959 < baseStart_4292959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292962 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4292962 : Nat := 118140960795 + 4292962 * 2 ^ 59
def prefixEnd_4292962 : Nat := 4983230072969 + 3 ^ 40 * 4292962 * 2
def baseEnd_4292962 : Nat := 734784312495646000044011

theorem tailTrace_4292962 : CollatzResearch.WordTrace tailWord_4292962 prefixEnd_4292962 734784312495646000044011 := by
  unfold tailWord_4292962
  simp only [CollatzResearch.WordTrace]
  refine ⟨39144296868334832095826285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104384791648892885588870093 39144296868334832095826285)
  ·
    refine ⟨14679111325625562035934857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39144296868334832095826285 14679111325625562035934857)
    ·
      refine ⟨11009333494219171526951143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14679111325625562035934857 11009333494219171526951143)
      ·
        refine ⟨16514000241328757290426715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11009333494219171526951143 16514000241328757290426715)
        ·
          refine ⟨24771000361993135935640073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16514000241328757290426715 24771000361993135935640073)
          ·
            refine ⟨18578250271494851951730055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24771000361993135935640073 18578250271494851951730055)
            ·
              refine ⟨27867375407242277927595083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18578250271494851951730055 27867375407242277927595083)
              ·
                refine ⟨41801063110863416891392625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27867375407242277927595083 41801063110863416891392625)
                ·
                  refine ⟨31350797333147562668544469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41801063110863416891392625 31350797333147562668544469)
                  ·
                    refine ⟨734784312495646000044011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31350797333147562668544469 734784312495646000044011)
                    ·
                      rfl

theorem cell23_4292962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4292962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292962 prefixEnd_4292962 := by exact prefixLift 4292962
  have htrace : WordTrace (prefixWord ++ tailWord_4292962) baseStart_4292962 baseEnd_4292962 := by
    simpa [prefixWord, tailWord_4292962, baseEnd_4292962] using wordTrace_append hprefix tailTrace_4292962
  have hstable : (prefixWord ++ tailWord_4292962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292962).length < 2 ^ (prefixWord ++ tailWord_4292962).sum := by decide
  have hdescent : baseEnd_4292962 < baseStart_4292962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4292999 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_4292999 : Nat := 118140960795 + 4292999 * 2 ^ 59
def prefixEnd_4292999 : Nat := 4983230072969 + 3 ^ 40 * 4292999 * 2
def baseEnd_4292999 : Nat := 2204371936271154355369363

theorem tailTrace_4292999 : CollatzResearch.WordTrace tailWord_4292999 prefixEnd_4292999 2204371936271154355369363 := by
  unfold tailWord_4292999
  simp only [CollatzResearch.WordTrace]
  refine ⟨156578536974205283702402051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104385691316136855801601367 156578536974205283702402051)
  ·
    refine ⟨234867805461307925553603077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156578536974205283702402051 234867805461307925553603077)
    ·
      refine ⟨44037713523995236041300577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234867805461307925553603077 44037713523995236041300577)
      ·
        refine ⟨33028285142996427030975433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44037713523995236041300577 33028285142996427030975433)
        ·
          refine ⟨24771213857247320273231575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33028285142996427030975433 24771213857247320273231575)
          ·
            refine ⟨37156820785870980409847363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24771213857247320273231575 37156820785870980409847363)
            ·
              refine ⟨55735231178806470614771045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37156820785870980409847363 55735231178806470614771045)
              ·
                refine ⟨10450355846026213240269571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55735231178806470614771045 10450355846026213240269571)
                ·
                  refine ⟨15675533769039319860404357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10450355846026213240269571 15675533769039319860404357)
                  ·
                    refine ⟨2939162581694872473825817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15675533769039319860404357 2939162581694872473825817)
                    ·
                      refine ⟨2204371936271154355369363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939162581694872473825817 2204371936271154355369363)
                      ·
                        rfl

theorem cell23_4292999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_4292999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4292999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4292999 prefixEnd_4292999 := by exact prefixLift 4292999
  have htrace : WordTrace (prefixWord ++ tailWord_4292999) baseStart_4292999 baseEnd_4292999 := by
    simpa [prefixWord, tailWord_4292999, baseEnd_4292999] using wordTrace_append hprefix tailTrace_4292999
  have hstable : (prefixWord ++ tailWord_4292999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4292999).length < 2 ^ (prefixWord ++ tailWord_4292999).sum := by decide
  have hdescent : baseEnd_4292999 < baseStart_4292999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4292999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293003 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 1, 3, 2]
def baseStart_4293003 : Nat := 118140960795 + 4293003 * 2 ^ 59
def prefixEnd_4293003 : Nat := 4983230072969 + 3 ^ 40 * 4293003 * 2
def baseEnd_4293003 : Nat := 2204373990193772339719345

theorem tailTrace_4293003 : CollatzResearch.WordTrace tailWord_4293003 prefixEnd_4293003 2204373990193772339719345 := by
  unfold tailWord_4293003
  simp only [CollatzResearch.WordTrace]
  refine ⟨156578682866190792385547663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104385788577460528257031775 156578682866190792385547663)
  ·
    refine ⟨234868024299286188578321495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156578682866190792385547663 234868024299286188578321495)
    ·
      refine ⟨352302036448929282867482243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234868024299286188578321495 352302036448929282867482243)
      ·
        refine ⟨528453054673393924301223365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352302036448929282867482243 528453054673393924301223365)
        ·
          refine ⟨99084947751261360806479381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 528453054673393924301223365 99084947751261360806479381)
          ·
            refine ⟨4644606925840376287803721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99084947751261360806479381 4644606925840376287803721)
            ·
              refine ⟨3483455194380282215852791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4644606925840376287803721 3483455194380282215852791)
              ·
                refine ⟨5225182791570423323779187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483455194380282215852791 5225182791570423323779187)
                ·
                  refine ⟨7837774187355634985668781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5225182791570423323779187 7837774187355634985668781)
                  ·
                    refine ⟨2939165320258363119625793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7837774187355634985668781 2939165320258363119625793)
                    ·
                      refine ⟨2204373990193772339719345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939165320258363119625793 2204373990193772339719345)
                      ·
                        rfl

theorem cell23_4293003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 3, 2].length) (baseStart_4293003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293003 prefixEnd_4293003 := by exact prefixLift 4293003
  have htrace : WordTrace (prefixWord ++ tailWord_4293003) baseStart_4293003 baseEnd_4293003 := by
    simpa [prefixWord, tailWord_4293003, baseEnd_4293003] using wordTrace_append hprefix tailTrace_4293003
  have hstable : (prefixWord ++ tailWord_4293003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293003).length < 2 ^ (prefixWord ++ tailWord_4293003).sum := by decide
  have hdescent : baseEnd_4293003 < baseStart_4293003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293089 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_4293089 : Nat := 118140960795 + 4293089 * 2 ^ 59
def prefixEnd_4293089 : Nat := 4983230072969 + 3 ^ 40 * 4293089 * 2
def baseEnd_4293089 : Nat := 2204418149530059003243949

theorem tailTrace_4293089 : CollatzResearch.WordTrace tailWord_4293089 prefixEnd_4293089 2204418149530059003243949 := by
  unfold tailWord_4293089
  simp only [CollatzResearch.WordTrace]
  refine ⟨156581819543879229073178321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104387879695919486048785547 156581819543879229073178321)
  ·
    refine ⟨117436364657909421804883741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156581819543879229073178321 117436364657909421804883741)
    ·
      refine ⟨44038636746716033176831403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117436364657909421804883741 44038636746716033176831403)
      ·
        refine ⟨66057955120074049765247105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44038636746716033176831403 66057955120074049765247105)
        ·
          refine ⟨49543466340055537323935329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66057955120074049765247105 49543466340055537323935329)
          ·
            refine ⟨37157599755041652992951497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49543466340055537323935329 37157599755041652992951497)
            ·
              refine ⟨27868199816281239744713623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37157599755041652992951497 27868199816281239744713623)
              ·
                refine ⟨41802299724421859617070435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27868199816281239744713623 41802299724421859617070435)
                ·
                  refine ⟨62703449586632789425605653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41802299724421859617070435 62703449586632789425605653)
                  ·
                    refine ⟨2939224199373412004325265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62703449586632789425605653 2939224199373412004325265)
                    ·
                      refine ⟨2204418149530059003243949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939224199373412004325265 2204418149530059003243949)
                      ·
                        rfl

theorem cell23_4293089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_4293089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293089 prefixEnd_4293089 := by exact prefixLift 4293089
  have htrace : WordTrace (prefixWord ++ tailWord_4293089) baseStart_4293089 baseEnd_4293089 := by
    simpa [prefixWord, tailWord_4293089, baseEnd_4293089] using wordTrace_append hprefix tailTrace_4293089
  have hstable : (prefixWord ++ tailWord_4293089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293089).length < 2 ^ (prefixWord ++ tailWord_4293089).sum := by decide
  have hdescent : baseEnd_4293089 < baseStart_4293089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293116 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_4293116 : Nat := 118140960795 + 4293116 * 2 ^ 59
def prefixEnd_4293116 : Nat := 4983230072969 + 3 ^ 40 * 4293116 * 2
def baseEnd_4293116 : Nat := 734810671169243465868775

theorem tailTrace_4293116 : CollatzResearch.WordTrace tailWord_4293116 prefixEnd_4293116 734810671169243465868775 := by
  unfold tailWord_4293116
  simp only [CollatzResearch.WordTrace]
  refine ⟨78291402157390706342205601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104388536209854275122940801 78291402157390706342205601)
  ·
    refine ⟨58718551618043029756654201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78291402157390706342205601 58718551618043029756654201)
    ·
      refine ⟨44038913713532272317490651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58718551618043029756654201 44038913713532272317490651)
      ·
        refine ⟨66058370570298408476235977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44038913713532272317490651 66058370570298408476235977)
        ·
          refine ⟨49543777927723806357176983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66058370570298408476235977 49543777927723806357176983)
          ·
            refine ⟨74315666891585709535765475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49543777927723806357176983 74315666891585709535765475)
            ·
              refine ⟨111473500337378564303648213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74315666891585709535765475 111473500337378564303648213)
              ·
                refine ⟨2612660164157310100866755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111473500337378564303648213 2612660164157310100866755)
                ·
                  refine ⟨3918990246235965151300133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612660164157310100866755 3918990246235965151300133)
                  ·
                    refine ⟨734810671169243465868775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918990246235965151300133 734810671169243465868775)
                    ·
                      rfl

theorem cell23_4293116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_4293116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293116 prefixEnd_4293116 := by exact prefixLift 4293116
  have htrace : WordTrace (prefixWord ++ tailWord_4293116) baseStart_4293116 baseEnd_4293116 := by
    simpa [prefixWord, tailWord_4293116, baseEnd_4293116] using wordTrace_append hprefix tailTrace_4293116
  have hstable : (prefixWord ++ tailWord_4293116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293116).length < 2 ^ (prefixWord ++ tailWord_4293116).sum := by decide
  have hdescent : baseEnd_4293116 < baseStart_4293116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293190 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4293190 : Nat := 118140960795 + 4293190 * 2 ^ 59
def prefixEnd_4293190 : Nat := 4983230072969 + 3 ^ 40 * 4293190 * 2
def baseEnd_4293190 : Nat := 2204470011076163108080985

theorem tailTrace_4293190 : CollatzResearch.WordTrace tailWord_4293190 prefixEnd_4293190 2204470011076163108080985 := by
  unfold tailWord_4293190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893296978641041353831407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104390335544342215548403349 4893296978641041353831407)
  ·
    refine ⟨7339945467961562030747111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893296978641041353831407 7339945467961562030747111)
    ·
      refine ⟨11009918201942343046120667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339945467961562030747111 11009918201942343046120667)
      ·
        refine ⟨16514877302913514569181001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11009918201942343046120667 16514877302913514569181001)
        ·
          refine ⟨12386157977185135926885751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16514877302913514569181001 12386157977185135926885751)
          ·
            refine ⟨18579236965777703890328627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12386157977185135926885751 18579236965777703890328627)
            ·
              refine ⟨27868855448666555835492941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18579236965777703890328627 27868855448666555835492941)
              ·
                refine ⟨10450820793249958438309853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27868855448666555835492941 10450820793249958438309853)
                ·
                  refine ⟨3919057797468734414366195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10450820793249958438309853 3919057797468734414366195)
                  ·
                    refine ⟨5878586696203101621549293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919057797468734414366195 5878586696203101621549293)
                    ·
                      refine ⟨2204470011076163108080985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878586696203101621549293 2204470011076163108080985)
                      ·
                        rfl

theorem cell23_4293190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4293190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293190 prefixEnd_4293190 := by exact prefixLift 4293190
  have htrace : WordTrace (prefixWord ++ tailWord_4293190) baseStart_4293190 baseEnd_4293190 := by
    simpa [prefixWord, tailWord_4293190, baseEnd_4293190] using wordTrace_append hprefix tailTrace_4293190
  have hstable : (prefixWord ++ tailWord_4293190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293190).length < 2 ^ (prefixWord ++ tailWord_4293190).sum := by decide
  have hdescent : baseEnd_4293190 < baseStart_4293190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293199 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_4293199 : Nat := 118140960795 + 4293199 * 2 ^ 59
def prefixEnd_4293199 : Nat := 4983230072969 + 3 ^ 40 * 4293199 * 2
def baseEnd_4293199 : Nat := 2204474632402053572868443

theorem tailTrace_4293199 : CollatzResearch.WordTrace tailWord_4293199 prefixEnd_4293199 2204474632402053572868443 := by
  unfold tailWord_4293199
  simp only [CollatzResearch.WordTrace]
  refine ⟨156585831573480717859682651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104390554382320478573121767 156585831573480717859682651)
  ·
    refine ⟨234878747360221076789523977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156585831573480717859682651 234878747360221076789523977)
    ·
      refine ⟨176159060520165807592142983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234878747360221076789523977 176159060520165807592142983)
      ·
        refine ⟨264238590780248711388214475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176159060520165807592142983 264238590780248711388214475)
        ·
          refine ⟨396357886170373067082321713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264238590780248711388214475 396357886170373067082321713)
          ·
            refine ⟨297268414627779800311741285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396357886170373067082321713 297268414627779800311741285)
            ·
              refine ⟨55737827742708712558451491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297268414627779800311741285 55737827742708712558451491)
              ·
                refine ⟨83606741614063068837677237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55737827742708712558451491 83606741614063068837677237)
                ·
                  refine ⟨7838132026318412703532241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83606741614063068837677237 7838132026318412703532241)
                  ·
                    refine ⟨5878599019738809527649181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7838132026318412703532241 5878599019738809527649181)
                    ·
                      refine ⟨2204474632402053572868443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878599019738809527649181 2204474632402053572868443)
                      ·
                        rfl

theorem cell23_4293199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_4293199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293199 prefixEnd_4293199 := by exact prefixLift 4293199
  have htrace : WordTrace (prefixWord ++ tailWord_4293199) baseStart_4293199 baseEnd_4293199 := by
    simpa [prefixWord, tailWord_4293199, baseEnd_4293199] using wordTrace_append hprefix tailTrace_4293199
  have hstable : (prefixWord ++ tailWord_4293199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293199).length < 2 ^ (prefixWord ++ tailWord_4293199).sum := by decide
  have hdescent : baseEnd_4293199 < baseStart_4293199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293216 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_4293216 : Nat := 118140960795 + 4293216 * 2 ^ 59
def prefixEnd_4293216 : Nat := 4983230072969 + 3 ^ 40 * 4293216 * 2
def baseEnd_4293216 : Nat := 2204483361573180006355865

theorem tailTrace_4293216 : CollatzResearch.WordTrace tailWord_4293216 prefixEnd_4293216 2204483361573180006355865 := by
  unfold tailWord_4293216
  simp only [CollatzResearch.WordTrace]
  refine ⟨78293225807209564881525751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104390967742946086508701001 78293225807209564881525751)
  ·
    refine ⟨117439838710814347322288627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78293225807209564881525751 117439838710814347322288627)
    ·
      refine ⟨176159758066221520983432941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117439838710814347322288627 176159758066221520983432941)
      ·
        refine ⟨66059909274833070368787353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176159758066221520983432941 66059909274833070368787353)
        ·
          refine ⟨49544931956124802776590515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66059909274833070368787353 49544931956124802776590515)
          ·
            refine ⟨74317397934187204164885773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49544931956124802776590515 74317397934187204164885773)
            ·
              refine ⟨27869024225320201561832165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74317397934187204164885773 27869024225320201561832165)
              ·
                refine ⟨5225442042247537792843531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27869024225320201561832165 5225442042247537792843531)
                ·
                  refine ⟨7838163063371306689265297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5225442042247537792843531 7838163063371306689265297)
                  ·
                    refine ⟨5878622297528480016948973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7838163063371306689265297 5878622297528480016948973)
                    ·
                      refine ⟨2204483361573180006355865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878622297528480016948973 2204483361573180006355865)
                      ·
                        rfl

theorem cell23_4293216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_4293216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293216 prefixEnd_4293216 := by exact prefixLift 4293216
  have htrace : WordTrace (prefixWord ++ tailWord_4293216) baseStart_4293216 baseEnd_4293216 := by
    simpa [prefixWord, tailWord_4293216, baseEnd_4293216] using wordTrace_append hprefix tailTrace_4293216
  have hstable : (prefixWord ++ tailWord_4293216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293216).length < 2 ^ (prefixWord ++ tailWord_4293216).sum := by decide
  have hdescent : baseEnd_4293216 < baseStart_4293216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293224 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4293224 : Nat := 118140960795 + 4293224 * 2 ^ 59
def prefixEnd_4293224 : Nat := 4983230072969 + 3 ^ 40 * 4293224 * 2
def baseEnd_4293224 : Nat := 2204487469418415975055829

theorem tailTrace_4293224 : CollatzResearch.WordTrace tailWord_4293224 prefixEnd_4293224 2204487469418415975055829 := by
  unfold tailWord_4293224
  simp only [CollatzResearch.WordTrace]
  refine ⟨78293371699195073564671363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104391162265593431419561817 78293371699195073564671363)
  ·
    refine ⟨117440057548792610347007045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78293371699195073564671363 117440057548792610347007045)
    ·
      refine ⟨22020010790398614440063821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117440057548792610347007045 22020010790398614440063821)
      ·
        refine ⟨8257504046399480415023933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22020010790398614440063821 8257504046399480415023933)
        ·
          refine ⟨3096564017399805155633975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8257504046399480415023933 3096564017399805155633975)
          ·
            refine ⟨4644846026099707733450963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096564017399805155633975 4644846026099707733450963)
            ·
              refine ⟨6967269039149561600176445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644846026099707733450963 6967269039149561600176445)
              ·
                refine ⟨2612725889681085600066167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6967269039149561600176445 2612725889681085600066167)
                ·
                  refine ⟨3919088834521628400099251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612725889681085600066167 3919088834521628400099251)
                  ·
                    refine ⟨5878633251782442600148877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919088834521628400099251 5878633251782442600148877)
                    ·
                      refine ⟨2204487469418415975055829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878633251782442600148877 2204487469418415975055829)
                      ·
                        rfl

theorem cell23_4293224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4293224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293224 prefixEnd_4293224 := by exact prefixLift 4293224
  have htrace : WordTrace (prefixWord ++ tailWord_4293224) baseStart_4293224 baseEnd_4293224 := by
    simpa [prefixWord, tailWord_4293224, baseEnd_4293224] using wordTrace_append hprefix tailTrace_4293224
  have hstable : (prefixWord ++ tailWord_4293224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293224).length < 2 ^ (prefixWord ++ tailWord_4293224).sum := by decide
  have hdescent : baseEnd_4293224 < baseStart_4293224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293249 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_4293249 : Nat := 118140960795 + 4293249 * 2 ^ 59
def prefixEnd_4293249 : Nat := 4983230072969 + 3 ^ 40 * 4293249 * 2
def baseEnd_4293249 : Nat := 734833435478259459081071

theorem tailTrace_4293249 : CollatzResearch.WordTrace tailWord_4293249 prefixEnd_4293249 734833435478259459081071 := by
  unfold tailWord_4293249
  simp only [CollatzResearch.WordTrace]
  refine ⟨156587655223299576399002801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104391770148866384266001867 156587655223299576399002801)
  ·
    refine ⟨117440741417474682299252101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156587655223299576399002801 117440741417474682299252101)
    ·
      refine ⟨22020139015776502931109769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117440741417474682299252101 22020139015776502931109769)
      ·
        refine ⟨16515104261832377198332327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22020139015776502931109769 16515104261832377198332327)
        ·
          refine ⟨24772656392748565797498491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16515104261832377198332327 24772656392748565797498491)
          ·
            refine ⟨37158984589122848696247737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24772656392748565797498491 37158984589122848696247737)
            ·
              refine ⟨27869238441842136522185803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37158984589122848696247737 27869238441842136522185803)
              ·
                refine ⟨41803857662763204783278705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27869238441842136522185803 41803857662763204783278705)
                ·
                  refine ⟨31352893247072403587459029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41803857662763204783278705 31352893247072403587459029)
                  ·
                    refine ⟨734833435478259459081071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31352893247072403587459029 734833435478259459081071)
                    ·
                      rfl

theorem cell23_4293249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_4293249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293249 prefixEnd_4293249 := by exact prefixLift 4293249
  have htrace : WordTrace (prefixWord ++ tailWord_4293249) baseStart_4293249 baseEnd_4293249 := by
    simpa [prefixWord, tailWord_4293249, baseEnd_4293249] using wordTrace_append hprefix tailTrace_4293249
  have hstable : (prefixWord ++ tailWord_4293249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293249).length < 2 ^ (prefixWord ++ tailWord_4293249).sum := by decide
  have hdescent : baseEnd_4293249 < baseStart_4293249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293289 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_4293289 : Nat := 118140960795 + 4293289 * 2 ^ 59
def prefixEnd_4293289 : Nat := 4983230072969 + 3 ^ 40 * 4293289 * 2
def baseEnd_4293289 : Nat := 2204520845660958220743029

theorem tailTrace_4293289 : CollatzResearch.WordTrace tailWord_4293289 prefixEnd_4293289 2204520845660958220743029 := by
  unfold tailWord_4293289
  simp only [CollatzResearch.WordTrace]
  refine ⟨156589114143154663230458921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104392742762103108820305947 156589114143154663230458921)
  ·
    refine ⟨117441835607365997422844191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156589114143154663230458921 117441835607365997422844191)
    ·
      refine ⟨176162753411048996134266287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117441835607365997422844191 176162753411048996134266287)
      ·
        refine ⟨264244130116573494201399431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176162753411048996134266287 264244130116573494201399431)
        ·
          refine ⟨396366195174860241302099147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264244130116573494201399431 396366195174860241302099147)
          ·
            refine ⟨594549292762290361953148721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396366195174860241302099147 594549292762290361953148721)
            ·
              refine ⟨445911969571717771464861541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594549292762290361953148721 445911969571717771464861541)
              ·
                refine ⟨83608494294697082149661539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445911969571717771464861541 83608494294697082149661539)
                ·
                  refine ⟨125412741442045623224492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83608494294697082149661539 125412741442045623224492309)
                  ·
                    refine ⟨5878722255095888588648077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125412741442045623224492309 5878722255095888588648077)
                    ·
                      refine ⟨2204520845660958220743029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878722255095888588648077 2204520845660958220743029)
                      ·
                        rfl

theorem cell23_4293289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_4293289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293289 prefixEnd_4293289 := by exact prefixLift 4293289
  have htrace : WordTrace (prefixWord ++ tailWord_4293289) baseStart_4293289 baseEnd_4293289 := by
    simpa [prefixWord, tailWord_4293289, baseEnd_4293289] using wordTrace_append hprefix tailTrace_4293289
  have hstable : (prefixWord ++ tailWord_4293289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293289).length < 2 ^ (prefixWord ++ tailWord_4293289).sum := by decide
  have hdescent : baseEnd_4293289 < baseStart_4293289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293297 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4293297 : Nat := 118140960795 + 4293297 * 2 ^ 59
def prefixEnd_4293297 : Nat := 4983230072969 + 3 ^ 40 * 4293297 * 2
def baseEnd_4293297 : Nat := 2204524953506194189442993

theorem tailTrace_4293297 : CollatzResearch.WordTrace tailWord_4293297 prefixEnd_4293297 2204524953506194189442993 := by
  unfold tailWord_4293297
  simp only [CollatzResearch.WordTrace]
  refine ⟨156589405927125680596750145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104392937284750453731166763 156589405927125680596750145)
  ·
    refine ⟨117442054445344260447562609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156589405927125680596750145 117442054445344260447562609)
    ·
      refine ⟨88081540834008195335671957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117442054445344260447562609 88081540834008195335671957)
      ·
        refine ⟨4128822226594134156359623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88081540834008195335671957 4128822226594134156359623)
        ·
          refine ⟨6193233339891201234539435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128822226594134156359623 6193233339891201234539435)
          ·
            refine ⟨9289850009836801851809153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193233339891201234539435 9289850009836801851809153)
            ·
              refine ⟨6967387507377601388856865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9289850009836801851809153 6967387507377601388856865)
              ·
                refine ⟨5225540630533201041642649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6967387507377601388856865 5225540630533201041642649)
                ·
                  refine ⟨3919155472899900781231987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5225540630533201041642649 3919155472899900781231987)
                  ·
                    refine ⟨5878733209349851171847981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919155472899900781231987 5878733209349851171847981)
                    ·
                      refine ⟨2204524953506194189442993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878733209349851171847981 2204524953506194189442993)
                      ·
                        rfl

theorem cell23_4293297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4293297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293297 prefixEnd_4293297 := by exact prefixLift 4293297
  have htrace : WordTrace (prefixWord ++ tailWord_4293297) baseStart_4293297 baseEnd_4293297 := by
    simpa [prefixWord, tailWord_4293297, baseEnd_4293297] using wordTrace_append hprefix tailTrace_4293297
  have hstable : (prefixWord ++ tailWord_4293297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293297).length < 2 ^ (prefixWord ++ tailWord_4293297).sum := by decide
  have hdescent : baseEnd_4293297 < baseStart_4293297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293316 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4293316 : Nat := 118140960795 + 4293316 * 2 ^ 59
def prefixEnd_4293316 : Nat := 4983230072969 + 3 ^ 40 * 4293316 * 2
def baseEnd_4293316 : Nat := 2204534709638629615105405

theorem tailTrace_4293316 : CollatzResearch.WordTrace tailWord_4293316 prefixEnd_4293316 2204534709638629615105405 := by
  unfold tailWord_4293316
  simp only [CollatzResearch.WordTrace]
  refine ⟨78295049457028423420845901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104393399276037897894461201 78295049457028423420845901)
  ·
    refine ⟨29360643546385658782817213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78295049457028423420845901 29360643546385658782817213)
    ·
      refine ⟨11010241329894622043556455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29360643546385658782817213 11010241329894622043556455)
      ·
        refine ⟨16515361994841933065334683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010241329894622043556455 16515361994841933065334683)
        ·
          refine ⟨24773042992262899598002025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16515361994841933065334683 24773042992262899598002025)
          ·
            refine ⟨18579782244197174698501519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24773042992262899598002025 18579782244197174698501519)
            ·
              refine ⟨27869673366295762047752279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18579782244197174698501519 27869673366295762047752279)
              ·
                refine ⟨41804510049443643071628419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27869673366295762047752279 41804510049443643071628419)
                ·
                  refine ⟨62706765074165464607442629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41804510049443643071628419 62706765074165464607442629)
                  ·
                    refine ⟨11757518451406024613895493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62706765074165464607442629 11757518451406024613895493)
                    ·
                      refine ⟨2204534709638629615105405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11757518451406024613895493 2204534709638629615105405)
                      ·
                        rfl

theorem cell23_4293316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4293316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293316 prefixEnd_4293316 := by exact prefixLift 4293316
  have htrace : WordTrace (prefixWord ++ tailWord_4293316) baseStart_4293316 baseEnd_4293316 := by
    simpa [prefixWord, tailWord_4293316, baseEnd_4293316] using wordTrace_append hprefix tailTrace_4293316
  have hstable : (prefixWord ++ tailWord_4293316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293316).length < 2 ^ (prefixWord ++ tailWord_4293316).sum := by decide
  have hdescent : baseEnd_4293316 < baseStart_4293316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293320 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_4293320 : Nat := 118140960795 + 4293320 * 2 ^ 59
def prefixEnd_4293320 : Nat := 4983230072969 + 3 ^ 40 * 4293320 * 2
def baseEnd_4293320 : Nat := 2204536763561247599455387

theorem tailTrace_4293320 : CollatzResearch.WordTrace tailWord_4293320 prefixEnd_4293320 2204536763561247599455387 := by
  unfold tailWord_4293320
  simp only [CollatzResearch.WordTrace]
  refine ⟨78295122403021177762418707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104393496537361570349891609 78295122403021177762418707)
  ·
    refine ⟨117442683604531766643628061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78295122403021177762418707 117442683604531766643628061)
    ·
      refine ⟨44041006351699412491360523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117442683604531766643628061 44041006351699412491360523)
      ·
        refine ⟨66061509527549118737040785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44041006351699412491360523 66061509527549118737040785)
        ·
          refine ⟨49546132145661839052780589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66061509527549118737040785 49546132145661839052780589)
          ·
            refine ⟨18579799554623189644792721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49546132145661839052780589 18579799554623189644792721)
            ·
              refine ⟨13934849665967392233594541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18579799554623189644792721 13934849665967392233594541)
              ·
                refine ⟨5225568624737772087597953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13934849665967392233594541 5225568624737772087597953)
                ·
                  refine ⟨3919176468553329065698465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5225568624737772087597953 3919176468553329065698465)
                  ·
                    refine ⟨2939382351414996799273849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3919176468553329065698465 2939382351414996799273849)
                    ·
                      refine ⟨2204536763561247599455387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939382351414996799273849 2204536763561247599455387)
                      ·
                        rfl

theorem cell23_4293320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_4293320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293320 prefixEnd_4293320 := by exact prefixLift 4293320
  have htrace : WordTrace (prefixWord ++ tailWord_4293320) baseStart_4293320 baseEnd_4293320 := by
    simpa [prefixWord, tailWord_4293320, baseEnd_4293320] using wordTrace_append hprefix tailTrace_4293320
  have hstable : (prefixWord ++ tailWord_4293320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293320).length < 2 ^ (prefixWord ++ tailWord_4293320).sum := by decide
  have hdescent : baseEnd_4293320 < baseStart_4293320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293326 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_4293326 : Nat := 118140960795 + 4293326 * 2 ^ 59
def prefixEnd_4293326 : Nat := 4983230072969 + 3 ^ 40 * 4293326 * 2
def baseEnd_4293326 : Nat := 244948871605019397331151

theorem tailTrace_4293326 : CollatzResearch.WordTrace tailWord_4293326 prefixEnd_4293326 244948871605019397331151 := by
  unfold tailWord_4293326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19573807955502577318694479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104393642429347079033037221 19573807955502577318694479)
  ·
    refine ⟨29360711933253865978041719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19573807955502577318694479 29360711933253865978041719)
    ·
      refine ⟨44041067899880798967062579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29360711933253865978041719 44041067899880798967062579)
      ·
        refine ⟨66061601849821198450593869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44041067899880798967062579 66061601849821198450593869)
        ·
          refine ⟨24773100693682949418972701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66061601849821198450593869 24773100693682949418972701)
          ·
            refine ⟨9289912760131106032114763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24773100693682949418972701 9289912760131106032114763)
            ·
              refine ⟨13934869140196659048172145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9289912760131106032114763 13934869140196659048172145)
              ·
                refine ⟨10451151855147494286129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13934869140196659048172145 10451151855147494286129109)
                ·
                  refine ⟨244948871605019397331151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10451151855147494286129109 244948871605019397331151)
                  ·
                    rfl

theorem cell23_4293326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_4293326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293326 prefixEnd_4293326 := by exact prefixLift 4293326
  have htrace : WordTrace (prefixWord ++ tailWord_4293326) baseStart_4293326 baseEnd_4293326 := by
    simpa [prefixWord, tailWord_4293326, baseEnd_4293326] using wordTrace_append hprefix tailTrace_4293326
  have hstable : (prefixWord ++ tailWord_4293326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293326).length < 2 ^ (prefixWord ++ tailWord_4293326).sum := by decide
  have hdescent : baseEnd_4293326 < baseStart_4293326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 8, 5]
def baseStart_4293339 : Nat := 118140960795 + 4293339 * 2 ^ 59
def prefixEnd_4293339 : Nat := 4983230072969 + 3 ^ 40 * 4293339 * 2
def baseEnd_4293339 : Nat := 734848839897894341705933

theorem tailTrace_4293339 : CollatzResearch.WordTrace tailWord_4293339 prefixEnd_4293339 734848839897894341705933 := by
  unfold tailWord_4293339
  simp only [CollatzResearch.WordTrace]
  refine ⟨156590937792973521769779071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104393958528649014513186047 156590937792973521769779071)
  ·
    refine ⟨234886406689460282654668607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156590937792973521769779071 234886406689460282654668607)
    ·
      refine ⟨352329610034190423982002911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234886406689460282654668607 352329610034190423982002911)
      ·
        refine ⟨528494415051285635973004367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352329610034190423982002911 528494415051285635973004367)
        ·
          refine ⟨792741622576928453959506551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528494415051285635973004367 792741622576928453959506551)
          ·
            refine ⟨1189112433865392680939259827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792741622576928453959506551 1189112433865392680939259827)
            ·
              refine ⟨1783668650798089021408889741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189112433865392680939259827 1783668650798089021408889741)
              ·
                refine ⟨668875744049283383028333653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783668650798089021408889741 668875744049283383028333653)
                ·
                  refine ⟨7838387625577539644863285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 668875744049283383028333653 7838387625577539644863285)
                  ·
                    refine ⟨734848839897894341705933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7838387625577539644863285 734848839897894341705933)
                    ·
                      rfl

theorem cell23_4293339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].length) (baseStart_4293339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293339 prefixEnd_4293339 := by exact prefixLift 4293339
  have htrace : WordTrace (prefixWord ++ tailWord_4293339) baseStart_4293339 baseEnd_4293339 := by
    simpa [prefixWord, tailWord_4293339, baseEnd_4293339] using wordTrace_append hprefix tailTrace_4293339
  have hstable : (prefixWord ++ tailWord_4293339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293339).length < 2 ^ (prefixWord ++ tailWord_4293339).sum := by decide
  have hdescent : baseEnd_4293339 < baseStart_4293339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293343 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 5]
def baseStart_4293343 : Nat := 118140960795 + 4293343 * 2 ^ 59
def prefixEnd_4293343 : Nat := 4983230072969 + 3 ^ 40 * 4293343 * 2
def baseEnd_4293343 : Nat := 244949841512922334385309

theorem tailTrace_4293343 : CollatzResearch.WordTrace tailWord_4293343 prefixEnd_4293343 244949841512922334385309 := by
  unfold tailWord_4293343
  simp only [CollatzResearch.WordTrace]
  refine ⟨156591083684959030452924683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104394055789972686968616455 156591083684959030452924683)
  ·
    refine ⟨234886625527438545679387025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156591083684959030452924683 234886625527438545679387025)
    ·
      refine ⟨176164969145578909259540269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234886625527438545679387025 176164969145578909259540269)
      ·
        refine ⟨66061863429592090972327601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176164969145578909259540269 66061863429592090972327601)
        ·
          refine ⟨49546397572194068229245701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66061863429592090972327601 49546397572194068229245701)
          ·
            refine ⟨9289949544786387792983569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49546397572194068229245701 9289949544786387792983569)
            ·
              refine ⟨6967462158589790844737677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9289949544786387792983569 6967462158589790844737677)
              ·
                refine ⟨2612798309471171566776629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6967462158589790844737677 2612798309471171566776629)
                ·
                  refine ⟨244949841512922334385309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612798309471171566776629 244949841512922334385309)
                  ·
                    rfl

theorem cell23_4293343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 5].length) (baseStart_4293343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293343 prefixEnd_4293343 := by exact prefixLift 4293343
  have htrace : WordTrace (prefixWord ++ tailWord_4293343) baseStart_4293343 baseEnd_4293343 := by
    simpa [prefixWord, tailWord_4293343, baseEnd_4293343] using wordTrace_append hprefix tailTrace_4293343
  have hstable : (prefixWord ++ tailWord_4293343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293343).length < 2 ^ (prefixWord ++ tailWord_4293343).sum := by decide
  have hdescent : baseEnd_4293343 < baseStart_4293343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293366 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4293366 : Nat := 118140960795 + 4293366 * 2 ^ 59
def prefixEnd_4293366 : Nat := 4983230072969 + 3 ^ 40 * 4293366 * 2
def baseEnd_4293366 : Nat := 2204560383671354419480175

theorem tailTrace_4293366 : CollatzResearch.WordTrace tailWord_4293366 prefixEnd_4293366 2204560383671354419480175 := by
  unfold tailWord_4293366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9786995160242231586313247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104394615042583803587341301 9786995160242231586313247)
  ·
    refine ⟨14680492740363347379469871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9786995160242231586313247 14680492740363347379469871)
    ·
      refine ⟨22020739110545021069204807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14680492740363347379469871 22020739110545021069204807)
      ·
        refine ⟨33031108665817531603807211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22020739110545021069204807 33031108665817531603807211)
        ·
          refine ⟨49546662998726297405710817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33031108665817531603807211 49546662998726297405710817)
          ·
            refine ⟨37159997249044723054283113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49546662998726297405710817 37159997249044723054283113)
            ·
              refine ⟨27869997936783542290712335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37159997249044723054283113 27869997936783542290712335)
              ·
                refine ⟨41804996905175313436068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27869997936783542290712335 41804996905175313436068503)
                ·
                  refine ⟨62707495357762970154102755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41804996905175313436068503 62707495357762970154102755)
                  ·
                    refine ⟨94061243036644455231154133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62707495357762970154102755 94061243036644455231154133)
                    ·
                      refine ⟨2204560383671354419480175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94061243036644455231154133 2204560383671354419480175)
                      ·
                        rfl

theorem cell23_4293366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4293366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293366 prefixEnd_4293366 := by exact prefixLift 4293366
  have htrace : WordTrace (prefixWord ++ tailWord_4293366) baseStart_4293366 baseEnd_4293366 := by
    simpa [prefixWord, tailWord_4293366, baseEnd_4293366] using wordTrace_append hprefix tailTrace_4293366
  have hstable : (prefixWord ++ tailWord_4293366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293366).length < 2 ^ (prefixWord ++ tailWord_4293366).sum := by decide
  have hdescent : baseEnd_4293366 < baseStart_4293366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293394 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_4293394 : Nat := 118140960795 + 4293394 * 2 ^ 59
def prefixEnd_4293394 : Nat := 4983230072969 + 3 ^ 40 * 4293394 * 2
def baseEnd_4293394 : Nat := 244952751236631145547783

theorem tailTrace_4293394 : CollatzResearch.WordTrace tailWord_4293394 prefixEnd_4293394 244952751236631145547783 := by
  unfold tailWord_4293394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39148235951943566540757809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104395295871849510775354157 39148235951943566540757809)
  ·
    refine ⟨29361176963957674905568357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39148235951943566540757809 29361176963957674905568357)
    ·
      refine ⟨5505220680742064044794067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29361176963957674905568357 5505220680742064044794067)
      ·
        refine ⟨8257831021113096067191101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505220680742064044794067 8257831021113096067191101)
        ·
          refine ⟨3096686632917411025196663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8257831021113096067191101 3096686632917411025196663)
          ·
            refine ⟨4645029949376116537794995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096686632917411025196663 4645029949376116537794995)
            ·
              refine ⟨6967544924064174806692493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645029949376116537794995 6967544924064174806692493)
              ·
                refine ⟨2612829346524065552509685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6967544924064174806692493 2612829346524065552509685)
                ·
                  refine ⟨244952751236631145547783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612829346524065552509685 244952751236631145547783)
                  ·
                    rfl

theorem cell23_4293394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_4293394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293394 prefixEnd_4293394 := by exact prefixLift 4293394
  have htrace : WordTrace (prefixWord ++ tailWord_4293394) baseStart_4293394 baseEnd_4293394 := by
    simpa [prefixWord, tailWord_4293394, baseEnd_4293394] using wordTrace_append hprefix tailTrace_4293394
  have hstable : (prefixWord ++ tailWord_4293394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293394).length < 2 ^ (prefixWord ++ tailWord_4293394).sum := by decide
  have hdescent : baseEnd_4293394 < baseStart_4293394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293413 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_4293413 : Nat := 118140960795 + 4293413 * 2 ^ 59
def prefixEnd_4293413 : Nat := 4983230072969 + 3 ^ 40 * 4293413 * 2
def baseEnd_4293413 : Nat := 2204584517262115735592459

theorem tailTrace_4293413 : CollatzResearch.WordTrace tailWord_4293413 prefixEnd_4293413 2204584517262115735592459 := by
  unfold tailWord_4293413
  simp only [CollatzResearch.WordTrace]
  refine ⟨156593636794705432407972893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104395757863136954938648595 156593636794705432407972893)
  ·
    refine ⟨58722613798014537152989835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156593636794705432407972893 58722613798014537152989835)
    ·
      refine ⟨88083920697021805729484753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58722613798014537152989835 88083920697021805729484753)
      ·
        refine ⟨66062940522766354297113565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88083920697021805729484753 66062940522766354297113565)
        ·
          refine ⟨24773602696037382861417587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66062940522766354297113565 24773602696037382861417587)
          ·
            refine ⟨37160404044056074292126381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24773602696037382861417587 37160404044056074292126381)
            ·
              refine ⟨13935151516521027859547393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37160404044056074292126381 13935151516521027859547393)
              ·
                refine ⟨10451363637390770894660545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13935151516521027859547393 10451363637390770894660545)
                ·
                  refine ⟨7838522728043078170995409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10451363637390770894660545 7838522728043078170995409)
                  ·
                    refine ⟨5878892046032308628246557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7838522728043078170995409 5878892046032308628246557)
                    ·
                      refine ⟨2204584517262115735592459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878892046032308628246557 2204584517262115735592459)
                      ·
                        rfl

theorem cell23_4293413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_4293413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293413 prefixEnd_4293413 := by exact prefixLift 4293413
  have htrace : WordTrace (prefixWord ++ tailWord_4293413) baseStart_4293413 baseEnd_4293413 := by
    simpa [prefixWord, tailWord_4293413, baseEnd_4293413] using wordTrace_append hprefix tailTrace_4293413
  have hstable : (prefixWord ++ tailWord_4293413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293413).length < 2 ^ (prefixWord ++ tailWord_4293413).sum := by decide
  have hdescent : baseEnd_4293413 < baseStart_4293413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293416 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 8]
def baseStart_4293416 : Nat := 118140960795 + 4293416 * 2 ^ 59
def prefixEnd_4293416 : Nat := 4983230072969 + 3 ^ 40 * 4293416 * 2
def baseEnd_4293416 : Nat := 244954006411564358206105

theorem tailTrace_4293416 : CollatzResearch.WordTrace tailWord_4293416 prefixEnd_4293416 244954006411564358206105 := by
  unfold tailWord_4293416
  simp only [CollatzResearch.WordTrace]
  refine ⟨78296873106847281960166051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104395830809129709280221401 78296873106847281960166051)
  ·
    refine ⟨117445309660270922940249077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78296873106847281960166051 117445309660270922940249077)
    ·
      refine ⟨11010497780650399025648351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117445309660270922940249077 11010497780650399025648351)
      ·
        refine ⟨16515746670975598538472527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010497780650399025648351 16515746670975598538472527)
        ·
          refine ⟨24773620006463397807708791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16515746670975598538472527 24773620006463397807708791)
          ·
            refine ⟨37160430009695096711563187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24773620006463397807708791 37160430009695096711563187)
            ·
              refine ⟨55740645014542645067344781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37160430009695096711563187 55740645014542645067344781)
              ·
                refine ⟨20902741880453491900254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55740645014542645067344781 20902741880453491900254293)
                ·
                  refine ⟨244954006411564358206105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20902741880453491900254293 244954006411564358206105)
                  ·
                    rfl

theorem cell23_4293416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_4293416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293416 prefixEnd_4293416 := by exact prefixLift 4293416
  have htrace : WordTrace (prefixWord ++ tailWord_4293416) baseStart_4293416 baseEnd_4293416 := by
    simpa [prefixWord, tailWord_4293416, baseEnd_4293416] using wordTrace_append hprefix tailTrace_4293416
  have hstable : (prefixWord ++ tailWord_4293416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293416).length < 2 ^ (prefixWord ++ tailWord_4293416).sum := by decide
  have hdescent : baseEnd_4293416 < baseStart_4293416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293443 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 3]
def baseStart_4293443 : Nat := 118140960795 + 4293443 * 2 ^ 59
def prefixEnd_4293443 : Nat := 4983230072969 + 3 ^ 40 * 4293443 * 2
def baseEnd_4293443 : Nat := 2204599921681750618217321

theorem tailTrace_4293443 : CollatzResearch.WordTrace tailWord_4293443 prefixEnd_4293443 2204599921681750618217321 := by
  unfold tailWord_4293443
  simp only [CollatzResearch.WordTrace]
  refine ⟨156594730984596747531564983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104396487323064498354376655 156594730984596747531564983)
  ·
    refine ⟨234892096476895121297347475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156594730984596747531564983 234892096476895121297347475)
    ·
      refine ⟨352338144715342681946021213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234892096476895121297347475 352338144715342681946021213)
      ·
        refine ⟨132126804268253505729757955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352338144715342681946021213 132126804268253505729757955)
        ·
          refine ⟨198190206402380258594636933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132126804268253505729757955 198190206402380258594636933)
          ·
            refine ⟨37160663700446298486494425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198190206402380258594636933 37160663700446298486494425)
            ·
              refine ⟨27870497775334723864870819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37160663700446298486494425 27870497775334723864870819)
              ·
                refine ⟨41805746663002085797306229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27870497775334723864870819 41805746663002085797306229)
                ·
                  refine ⟨3919288749656445543497459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41805746663002085797306229 3919288749656445543497459)
                  ·
                    refine ⟨5878933124484668315246189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919288749656445543497459 5878933124484668315246189)
                    ·
                      refine ⟨2204599921681750618217321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5878933124484668315246189 2204599921681750618217321)
                      ·
                        rfl

theorem cell23_4293443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_4293443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293443 prefixEnd_4293443 := by exact prefixLift 4293443
  have htrace : WordTrace (prefixWord ++ tailWord_4293443) baseStart_4293443 baseEnd_4293443 := by
    simpa [prefixWord, tailWord_4293443, baseEnd_4293443] using wordTrace_append hprefix tailTrace_4293443
  have hstable : (prefixWord ++ tailWord_4293443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293443).length < 2 ^ (prefixWord ++ tailWord_4293443).sum := by decide
  have hdescent : baseEnd_4293443 < baseStart_4293443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293493 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4293493 : Nat := 118140960795 + 4293493 * 2 ^ 59
def prefixEnd_4293493 : Nat := 4983230072969 + 3 ^ 40 * 4293493 * 2
def baseEnd_4293493 : Nat := 734875198571491807530697

theorem tailTrace_4293493 : CollatzResearch.WordTrace tailWord_4293493 prefixEnd_4293493 734875198571491807530697 := by
  unfold tailWord_4293493
  simp only [CollatzResearch.WordTrace]
  refine ⟨156596554634415606070885133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104397703089610404047256755 156596554634415606070885133)
  ·
    refine ⟨58723707987905852276581925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156596554634415606070885133 58723707987905852276581925)
    ·
      refine ⟨11010695247732347301859111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58723707987905852276581925 11010695247732347301859111)
      ·
        refine ⟨16516042871598520952788667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010695247732347301859111 16516042871598520952788667)
        ·
          refine ⟨24774064307397781429183001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16516042871598520952788667 24774064307397781429183001)
          ·
            refine ⟨18580548230548336071887251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24774064307397781429183001 18580548230548336071887251)
            ·
              refine ⟨27870822345822504107830877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18580548230548336071887251 27870822345822504107830877)
              ·
                refine ⟨10451558379683439040436579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27870822345822504107830877 10451558379683439040436579)
                ·
                  refine ⟨15677337569525158560654869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10451558379683439040436579 15677337569525158560654869)
                  ·
                    refine ⟨734875198571491807530697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15677337569525158560654869 734875198571491807530697)
                    ·
                      rfl

theorem cell23_4293493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4293493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293493 prefixEnd_4293493 := by exact prefixLift 4293493
  have htrace : WordTrace (prefixWord ++ tailWord_4293493) baseStart_4293493 baseEnd_4293493 := by
    simpa [prefixWord, tailWord_4293493, baseEnd_4293493] using wordTrace_append hprefix tailTrace_4293493
  have hstable : (prefixWord ++ tailWord_4293493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293493).length < 2 ^ (prefixWord ++ tailWord_4293493).sum := by decide
  have hdescent : baseEnd_4293493 < baseStart_4293493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293503 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_4293503 : Nat := 118140960795 + 4293503 * 2 ^ 59
def prefixEnd_4293503 : Nat := 4983230072969 + 3 ^ 40 * 4293503 * 2
def baseEnd_4293503 : Nat := 2204630730521020383467045

theorem tailTrace_4293503 : CollatzResearch.WordTrace tailWord_4293503 prefixEnd_4293503 2204630730521020383467045 := by
  unfold tailWord_4293503
  simp only [CollatzResearch.WordTrace]
  refine ⟨156596919364379377778749163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104397946242919585185832775 156596919364379377778749163)
  ·
    refine ⟨234895379046569066668123745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156596919364379377778749163 234895379046569066668123745)
    ·
      refine ⟨176171534284926800001092809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234895379046569066668123745 176171534284926800001092809)
      ·
        refine ⟨132128650713695100000819607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176171534284926800001092809 132128650713695100000819607)
        ·
          refine ⟨198192976070542650001229411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132128650713695100000819607 198192976070542650001229411)
          ·
            refine ⟨297289464105813975001844117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198192976070542650001229411 297289464105813975001844117)
            ·
              refine ⟨13935443629960030078211443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297289464105813975001844117 13935443629960030078211443)
              ·
                refine ⟨20903165444940045117317165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13935443629960030078211443 20903165444940045117317165)
                ·
                  refine ⟨7838687041852516918993937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20903165444940045117317165 7838687041852516918993937)
                  ·
                    refine ⟨5879015281389387689245453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7838687041852516918993937 5879015281389387689245453)
                    ·
                      refine ⟨2204630730521020383467045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879015281389387689245453 2204630730521020383467045)
                      ·
                        rfl

theorem cell23_4293503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_4293503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293503 prefixEnd_4293503 := by exact prefixLift 4293503
  have htrace : WordTrace (prefixWord ++ tailWord_4293503) baseStart_4293503 baseEnd_4293503 := by
    simpa [prefixWord, tailWord_4293503, baseEnd_4293503] using wordTrace_append hprefix tailTrace_4293503
  have hstable : (prefixWord ++ tailWord_4293503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293503).length < 2 ^ (prefixWord ++ tailWord_4293503).sum := by decide
  have hdescent : baseEnd_4293503 < baseStart_4293503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293513 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_4293513 : Nat := 118140960795 + 4293513 * 2 ^ 59
def prefixEnd_4293513 : Nat := 4983230072969 + 3 ^ 40 * 4293513 * 2
def baseEnd_4293513 : Nat := 2204635865327565344341999

theorem tailTrace_4293513 : CollatzResearch.WordTrace tailWord_4293513 prefixEnd_4293513 2204635865327565344341999 := by
  unfold tailWord_4293513
  simp only [CollatzResearch.WordTrace]
  refine ⟨156597284094343149486613193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104398189396228766324408795 156597284094343149486613193)
  ·
    refine ⟨117447963070757362114959895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156597284094343149486613193 117447963070757362114959895)
    ·
      refine ⟨176171944606136043172439843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117447963070757362114959895 176171944606136043172439843)
      ·
        refine ⟨264257916909204064758659765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176171944606136043172439843 264257916909204064758659765)
        ·
          refine ⟨24774179710237881071124353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264257916909204064758659765 24774179710237881071124353)
          ·
            refine ⟨18580634782678410803343265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24774179710237881071124353 18580634782678410803343265)
            ·
              refine ⟨13935476087008808102507449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18580634782678410803343265 13935476087008808102507449)
              ·
                refine ⟨10451607065256606076880587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13935476087008808102507449 10451607065256606076880587)
                ·
                  refine ⟨15677410597884909115320881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10451607065256606076880587 15677410597884909115320881)
                  ·
                    refine ⟨11758057948413681836490661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15677410597884909115320881 11758057948413681836490661)
                    ·
                      refine ⟨2204635865327565344341999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11758057948413681836490661 2204635865327565344341999)
                      ·
                        rfl

theorem cell23_4293513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_4293513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293513 prefixEnd_4293513 := by exact prefixLift 4293513
  have htrace : WordTrace (prefixWord ++ tailWord_4293513) baseStart_4293513 baseEnd_4293513 := by
    simpa [prefixWord, tailWord_4293513, baseEnd_4293513] using wordTrace_append hprefix tailTrace_4293513
  have hstable : (prefixWord ++ tailWord_4293513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293513).length < 2 ^ (prefixWord ++ tailWord_4293513).sum := by decide
  have hdescent : baseEnd_4293513 < baseStart_4293513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293536 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_4293536 : Nat := 118140960795 + 4293536 * 2 ^ 59
def prefixEnd_4293536 : Nat := 4983230072969 + 3 ^ 40 * 4293536 * 2
def baseEnd_4293536 : Nat := 734882558460872918118131

theorem tailTrace_4293536 : CollatzResearch.WordTrace tailWord_4293536 prefixEnd_4293536 734882558460872918118131 := by
  unfold tailWord_4293536
  simp only [CollatzResearch.WordTrace]
  refine ⟨78299061486629912207350231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104398748648839882943133641 78299061486629912207350231)
  ·
    refine ⟨117448592229944868311025347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78299061486629912207350231 117448592229944868311025347)
    ·
      refine ⟨176172888344917302466538021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117448592229944868311025347 176172888344917302466538021)
      ·
        refine ⟨33032416564671994212475879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176172888344917302466538021 33032416564671994212475879)
        ·
          refine ⟨49548624847007991318713819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33032416564671994212475879 49548624847007991318713819)
          ·
            refine ⟨74322937270511986978070729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49548624847007991318713819 74322937270511986978070729)
            ·
              refine ⟨55742202952883990233553047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74322937270511986978070729 55742202952883990233553047)
              ·
                refine ⟨83613304429325985350329571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55742202952883990233553047 83613304429325985350329571)
                ·
                  refine ⟨125419956643988978025494357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83613304429325985350329571 125419956643988978025494357)
                  ·
                    refine ⟨734882558460872918118131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125419956643988978025494357 734882558460872918118131)
                    ·
                      rfl

theorem cell23_4293536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_4293536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293536 prefixEnd_4293536 := by exact prefixLift 4293536
  have htrace : WordTrace (prefixWord ++ tailWord_4293536) baseStart_4293536 baseEnd_4293536 := by
    simpa [prefixWord, tailWord_4293536, baseEnd_4293536] using wordTrace_append hprefix tailTrace_4293536
  have hstable : (prefixWord ++ tailWord_4293536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293536).length < 2 ^ (prefixWord ++ tailWord_4293536).sum := by decide
  have hdescent : baseEnd_4293536 < baseStart_4293536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293603 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4293603 : Nat := 118140960795 + 4293603 * 2 ^ 59
def prefixEnd_4293603 : Nat := 4983230072969 + 3 ^ 40 * 4293603 * 2
def baseEnd_4293603 : Nat := 2204682078586469992216585

theorem tailTrace_4293603 : CollatzResearch.WordTrace tailWord_4293603 prefixEnd_4293603 2204682078586469992216585 := by
  unfold tailWord_4293603
  simp only [CollatzResearch.WordTrace]
  refine ⟨156600566664017094857389463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104400377776011396571592975 156600566664017094857389463)
  ·
    refine ⟨234900849996025642286084195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156600566664017094857389463 234900849996025642286084195)
    ·
      refine ⟨352351274994038463429126293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234900849996025642286084195 352351274994038463429126293)
      ·
        refine ⟨16516466015345552973240295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 352351274994038463429126293 16516466015345552973240295)
        ·
          refine ⟨24774699023018329459860443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16516466015345552973240295 24774699023018329459860443)
          ·
            refine ⟨37162048534527494189790665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24774699023018329459860443 37162048534527494189790665)
            ·
              refine ⟨27871536400895620642342999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37162048534527494189790665 27871536400895620642342999)
              ·
                refine ⟨41807304601343430963514499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27871536400895620642342999 41807304601343430963514499)
                ·
                  refine ⟨62710956902015146445271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41807304601343430963514499 62710956902015146445271749)
                  ·
                    refine ⟨11758304419127839958488453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62710956902015146445271749 11758304419127839958488453)
                    ·
                      refine ⟨2204682078586469992216585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11758304419127839958488453 2204682078586469992216585)
                      ·
                        rfl

theorem cell23_4293603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4293603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293603 prefixEnd_4293603 := by exact prefixLift 4293603
  have htrace : WordTrace (prefixWord ++ tailWord_4293603) baseStart_4293603 baseEnd_4293603 := by
    simpa [prefixWord, tailWord_4293603, baseEnd_4293603] using wordTrace_append hprefix tailTrace_4293603
  have hstable : (prefixWord ++ tailWord_4293603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293603).length < 2 ^ (prefixWord ++ tailWord_4293603).sum := by decide
  have hdescent : baseEnd_4293603 < baseStart_4293603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293680 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2]
def baseStart_4293680 : Nat := 118140960795 + 4293680 * 2 ^ 59
def prefixEnd_4293680 : Nat := 4983230072969 + 3 ^ 40 * 4293680 * 2
def baseEnd_4293680 : Nat := 2204721616596866190953731

theorem tailTrace_4293680 : CollatzResearch.WordTrace tailWord_4293680 prefixEnd_4293680 2204721616596866190953731 := by
  unfold tailWord_4293680
  simp only [CollatzResearch.WordTrace]
  refine ⟨78301687542369068503971247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104402250056492091338628329 78301687542369068503971247)
  ·
    refine ⟨117452531313553602755956871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78301687542369068503971247 117452531313553602755956871)
    ·
      refine ⟨176178796970330404133935307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117452531313553602755956871 176178796970330404133935307)
      ·
        refine ⟨264268195455495606200902961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176178796970330404133935307 264268195455495606200902961)
        ·
          refine ⟨198201146591621704650677221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264268195455495606200902961 198201146591621704650677221)
          ·
            refine ⟨37162714985929069622001979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198201146591621704650677221 37162714985929069622001979)
            ·
              refine ⟨55744072478893604433002969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37162714985929069622001979 55744072478893604433002969)
              ·
                refine ⟨41808054359170203324752227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55744072478893604433002969 41808054359170203324752227)
                ·
                  refine ⟨62712081538755304987128341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41808054359170203324752227 62712081538755304987128341)
                  ·
                    refine ⟨2939628822129154921271641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62712081538755304987128341 2939628822129154921271641)
                    ·
                      refine ⟨2204721616596866190953731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939628822129154921271641 2204721616596866190953731)
                      ·
                        rfl

theorem cell23_4293680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2].length) (baseStart_4293680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293680 prefixEnd_4293680 := by exact prefixLift 4293680
  have htrace : WordTrace (prefixWord ++ tailWord_4293680) baseStart_4293680 baseEnd_4293680 := by
    simpa [prefixWord, tailWord_4293680, baseEnd_4293680] using wordTrace_append hprefix tailTrace_4293680
  have hstable : (prefixWord ++ tailWord_4293680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293680).length < 2 ^ (prefixWord ++ tailWord_4293680).sum := by decide
  have hdescent : baseEnd_4293680 < baseStart_4293680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293741 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_4293741 : Nat := 118140960795 + 4293741 * 2 ^ 59
def prefixEnd_4293741 : Nat := 4983230072969 + 3 ^ 40 * 4293741 * 2
def baseEnd_4293741 : Nat := 734917646305596817430317

theorem tailTrace_4293741 : CollatzResearch.WordTrace tailWord_4293741 prefixEnd_4293741 734917646305596817430317 := by
  unfold tailWord_4293741
  simp only [CollatzResearch.WordTrace]
  refine ⟨156605599937517144425913077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104403733291678096283942051 156605599937517144425913077)
  ·
    refine ⟨14681774994142232289929351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156605599937517144425913077 14681774994142232289929351)
    ·
      refine ⟨22022662491213348434894027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14681774994142232289929351 22022662491213348434894027)
      ·
        refine ⟨33033993736820022652341041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22022662491213348434894027 33033993736820022652341041)
        ·
          refine ⟨24775495302615016989255781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33033993736820022652341041 24775495302615016989255781)
          ·
            refine ⟨4645405369240315685485459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24775495302615016989255781 4645405369240315685485459)
            ·
              refine ⟨6968108053860473528228189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645405369240315685485459 6968108053860473528228189)
              ·
                refine ⟨2613040520197677573085571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6968108053860473528228189 2613040520197677573085571)
                ·
                  refine ⟨3919560780296516359628357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613040520197677573085571 3919560780296516359628357)
                  ·
                    refine ⟨734917646305596817430317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919560780296516359628357 734917646305596817430317)
                    ·
                      rfl

theorem cell23_4293741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_4293741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293741 prefixEnd_4293741 := by exact prefixLift 4293741
  have htrace : WordTrace (prefixWord ++ tailWord_4293741) baseStart_4293741 baseEnd_4293741 := by
    simpa [prefixWord, tailWord_4293741, baseEnd_4293741] using wordTrace_append hprefix tailTrace_4293741
  have hstable : (prefixWord ++ tailWord_4293741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293741).length < 2 ^ (prefixWord ++ tailWord_4293741).sum := by decide
  have hdescent : baseEnd_4293741 < baseStart_4293741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293764 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_4293764 : Nat := 118140960795 + 4293764 * 2 ^ 59
def prefixEnd_4293764 : Nat := 4983230072969 + 3 ^ 40 * 4293764 * 2
def baseEnd_4293764 : Nat := 2204764748971843862303345

theorem tailTrace_4293764 : CollatzResearch.WordTrace tailWord_4293764 prefixEnd_4293764 2204764748971843862303345 := by
  unfold tailWord_4293764
  simp only [CollatzResearch.WordTrace]
  refine ⟨78303219408216909677000173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104404292544289212902666897 78303219408216909677000173)
  ·
    refine ⟨29363707278081341128875065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78303219408216909677000173 29363707278081341128875065)
    ·
      refine ⟨22022780458561005846656299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29363707278081341128875065 22022780458561005846656299)
      ·
        refine ⟨33034170687841508769984449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22022780458561005846656299 33034170687841508769984449)
        ·
          refine ⟨24775628015881131577488337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33034170687841508769984449 24775628015881131577488337)
          ·
            refine ⟨18581721011910848683116253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24775628015881131577488337 18581721011910848683116253)
            ·
              refine ⟨6968145379466568256168595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18581721011910848683116253 6968145379466568256168595)
              ·
                refine ⟨10452218069199852384252893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968145379466568256168595 10452218069199852384252893)
                ·
                  refine ⟨3919581775949944644094835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10452218069199852384252893 3919581775949944644094835)
                  ·
                    refine ⟨5879372663924916966142253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919581775949944644094835 5879372663924916966142253)
                    ·
                      refine ⟨2204764748971843862303345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879372663924916966142253 2204764748971843862303345)
                      ·
                        rfl

theorem cell23_4293764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_4293764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293764 prefixEnd_4293764 := by exact prefixLift 4293764
  have htrace : WordTrace (prefixWord ++ tailWord_4293764) baseStart_4293764 baseEnd_4293764 := by
    simpa [prefixWord, tailWord_4293764, baseEnd_4293764] using wordTrace_append hprefix tailTrace_4293764
  have hstable : (prefixWord ++ tailWord_4293764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293764).length < 2 ^ (prefixWord ++ tailWord_4293764).sum := by decide
  have hdescent : baseEnd_4293764 < baseStart_4293764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293784 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_4293784 : Nat := 118140960795 + 4293784 * 2 ^ 59
def prefixEnd_4293784 : Nat := 4983230072969 + 3 ^ 40 * 4293784 * 2
def baseEnd_4293784 : Nat := 734925006194977928017751

theorem tailTrace_4293784 : CollatzResearch.WordTrace tailWord_4293784 prefixEnd_4293784 734925006194977928017751 := by
  unfold tailWord_4293784
  simp only [CollatzResearch.WordTrace]
  refine ⟨78303584138180681384864203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104404778850907575179818937 78303584138180681384864203)
  ·
    refine ⟨117455376207271022077296305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78303584138180681384864203 117455376207271022077296305)
    ·
      refine ⟨88091532155453266557972229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117455376207271022077296305 88091532155453266557972229)
      ·
        refine ⟨16517162279147487479619793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88091532155453266557972229 16517162279147487479619793)
        ·
          refine ⟨12387871709360615609714845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16517162279147487479619793 12387871709360615609714845)
          ·
            refine ⟨4645451891010230853643067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12387871709360615609714845 4645451891010230853643067)
            ·
              refine ⟨6968177836515346280464601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645451891010230853643067 6968177836515346280464601)
              ·
                refine ⟨5226133377386509710348451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6968177836515346280464601 5226133377386509710348451)
                ·
                  refine ⟨7839200066079764565522677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226133377386509710348451 7839200066079764565522677)
                  ·
                    refine ⟨734925006194977928017751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7839200066079764565522677 734925006194977928017751)
                    ·
                      rfl

theorem cell23_4293784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_4293784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293784 prefixEnd_4293784 := by exact prefixLift 4293784
  have htrace : WordTrace (prefixWord ++ tailWord_4293784) baseStart_4293784 baseEnd_4293784 := by
    simpa [prefixWord, tailWord_4293784, baseEnd_4293784] using wordTrace_append hprefix tailTrace_4293784
  have hstable : (prefixWord ++ tailWord_4293784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293784).length < 2 ^ (prefixWord ++ tailWord_4293784).sum := by decide
  have hdescent : baseEnd_4293784 < baseStart_4293784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293791 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4293791 : Nat := 118140960795 + 4293791 * 2 ^ 59
def prefixEnd_4293791 : Nat := 4983230072969 + 3 ^ 40 * 4293791 * 2
def baseEnd_4293791 : Nat := 2204778612949515256665721

theorem tailTrace_4293791 : CollatzResearch.WordTrace tailWord_4293791 prefixEnd_4293791 2204778612949515256665721 := by
  unfold tailWord_4293791
  simp only [CollatzResearch.WordTrace]
  refine ⟨156607423587336002965233227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104404949058224001976822151 156607423587336002965233227)
  ·
    refine ⟨234911135381004004447849841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156607423587336002965233227 234911135381004004447849841)
    ·
      refine ⟨176183351535753003335887381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234911135381004004447849841 176183351535753003335887381)
      ·
        refine ⟨8258594603238422031369721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176183351535753003335887381 8258594603238422031369721)
        ·
          refine ⟨6193945952428816523527291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8258594603238422031369721 6193945952428816523527291)
          ·
            refine ⟨9290918928643224785290937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193945952428816523527291 9290918928643224785290937)
            ·
              refine ⟨6968189196482418588968203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9290918928643224785290937 6968189196482418588968203)
              ·
                refine ⟨10452283794723627883452305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968189196482418588968203 10452283794723627883452305)
                ·
                  refine ⟨7839212846042720912589229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10452283794723627883452305 7839212846042720912589229)
                  ·
                    refine ⟨2939704817266020342220961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7839212846042720912589229 2939704817266020342220961)
                    ·
                      refine ⟨2204778612949515256665721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939704817266020342220961 2204778612949515256665721)
                      ·
                        rfl

theorem cell23_4293791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4293791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293791 prefixEnd_4293791 := by exact prefixLift 4293791
  have htrace : WordTrace (prefixWord ++ tailWord_4293791) baseStart_4293791 baseEnd_4293791 := by
    simpa [prefixWord, tailWord_4293791, baseEnd_4293791] using wordTrace_append hprefix tailTrace_4293791
  have hstable : (prefixWord ++ tailWord_4293791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293791).length < 2 ^ (prefixWord ++ tailWord_4293791).sum := by decide
  have hdescent : baseEnd_4293791 < baseStart_4293791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293807 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_4293807 : Nat := 118140960795 + 4293807 * 2 ^ 59
def prefixEnd_4293807 : Nat := 4983230072969 + 3 ^ 40 * 4293807 * 2
def baseEnd_4293807 : Nat := 2204786828639987194065647

theorem tailTrace_4293807 : CollatzResearch.WordTrace tailWord_4293807 prefixEnd_4293807 2204786828639987194065647 := by
  unfold tailWord_4293807
  simp only [CollatzResearch.WordTrace]
  refine ⟨156608007155278037697815675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104405338103518691798543783 156608007155278037697815675)
  ·
    refine ⟨234912010732917056546723513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156608007155278037697815675 234912010732917056546723513)
    ·
      refine ⟨176184008049687792410042635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234912010732917056546723513 176184008049687792410042635)
      ·
        refine ⟨264276012074531688615063953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176184008049687792410042635 264276012074531688615063953)
        ·
          refine ⟨198207009055898766461297965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264276012074531688615063953 198207009055898766461297965)
          ·
            refine ⟨74327628395962037422986737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198207009055898766461297965 74327628395962037422986737)
            ·
              refine ⟨55745721296971528067240053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74327628395962037422986737 55745721296971528067240053)
              ·
                refine ⟨5226161371591080756303755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55745721296971528067240053 5226161371591080756303755)
                ·
                  refine ⟨7839242057386621134455633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226161371591080756303755 7839242057386621134455633)
                  ·
                    refine ⟨5879431543039965850841725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7839242057386621134455633 5879431543039965850841725)
                    ·
                      refine ⟨2204786828639987194065647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879431543039965850841725 2204786828639987194065647)
                      ·
                        rfl

theorem cell23_4293807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_4293807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293807 prefixEnd_4293807 := by exact prefixLift 4293807
  have htrace : WordTrace (prefixWord ++ tailWord_4293807) baseStart_4293807 baseEnd_4293807 := by
    simpa [prefixWord, tailWord_4293807, baseEnd_4293807] using wordTrace_append hprefix tailTrace_4293807
  have hstable : (prefixWord ++ tailWord_4293807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293807).length < 2 ^ (prefixWord ++ tailWord_4293807).sum := by decide
  have hdescent : baseEnd_4293807 < baseStart_4293807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293850 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4293850 : Nat := 118140960795 + 4293850 * 2 ^ 59
def prefixEnd_4293850 : Nat := 4983230072969 + 3 ^ 40 * 4293850 * 2
def baseEnd_4293850 : Nat := 2204808908308130525827949

theorem tailTrace_4293850 : CollatzResearch.WordTrace tailWord_4293850 prefixEnd_4293850 2204808908308130525827949 := by
  unfold tailWord_4293850
  simp only [CollatzResearch.WordTrace]
  refine ⟨39152393873530564010407751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104406383662748170694420669 39152393873530564010407751)
  ·
    refine ⟨58728590810295846015611627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39152393873530564010407751 58728590810295846015611627)
    ·
      refine ⟨88092886215443769023417441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58728590810295846015611627 88092886215443769023417441)
      ·
        refine ⟨66069664661582826767563081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88092886215443769023417441 66069664661582826767563081)
        ·
          refine ⟨49552248496187120075672311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66069664661582826767563081 49552248496187120075672311)
          ·
            refine ⟨74328372744280680113508467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49552248496187120075672311 74328372744280680113508467)
            ·
              refine ⟨111492559116421020170262701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74328372744280680113508467 111492559116421020170262701)
              ·
                refine ⟨41809709668657882563848513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111492559116421020170262701 41809709668657882563848513)
                ·
                  refine ⟨31357282251493411922886385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41809709668657882563848513 31357282251493411922886385)
                  ·
                    refine ⟨23517961688620058942164789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31357282251493411922886385 23517961688620058942164789)
                    ·
                      refine ⟨2204808908308130525827949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23517961688620058942164789 2204808908308130525827949)
                      ·
                        rfl

theorem cell23_4293850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4293850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293850 prefixEnd_4293850 := by exact prefixLift 4293850
  have htrace : WordTrace (prefixWord ++ tailWord_4293850) baseStart_4293850 baseEnd_4293850 := by
    simpa [prefixWord, tailWord_4293850, baseEnd_4293850] using wordTrace_append hprefix tailTrace_4293850
  have hstable : (prefixWord ++ tailWord_4293850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293850).length < 2 ^ (prefixWord ++ tailWord_4293850).sum := by decide
  have hdescent : baseEnd_4293850 < baseStart_4293850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293880 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_4293880 : Nat := 118140960795 + 4293880 * 2 ^ 59
def prefixEnd_4293880 : Nat := 4983230072969 + 3 ^ 40 * 4293880 * 2
def baseEnd_4293880 : Nat := 2204824312727765408452811

theorem tailTrace_4293880 : CollatzResearch.WordTrace tailWord_4293880 prefixEnd_4293880 2204824312727765408452811 := by
  unfold tailWord_4293880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78305334842006785582611547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104407113122675714110148729 78305334842006785582611547)
  ·
    refine ⟨117458002263010178373917321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78305334842006785582611547 117458002263010178373917321)
    ·
      refine ⟨88093501697257633780437991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117458002263010178373917321 88093501697257633780437991)
      ·
        refine ⟨132140252545886450670656987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88093501697257633780437991 132140252545886450670656987)
        ·
          refine ⟨198210378818829676005985481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132140252545886450670656987 198210378818829676005985481)
          ·
            refine ⟨148657784114122257004489111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198210378818829676005985481 148657784114122257004489111)
            ·
              refine ⟨222986676171183385506733667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148657784114122257004489111 222986676171183385506733667)
              ·
                refine ⟨334480014256775078260100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222986676171183385506733667 334480014256775078260100501)
                ·
                  refine ⟨15678750668286331793442211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 334480014256775078260100501 15678750668286331793442211)
                  ·
                    refine ⟨23518126002429497690163317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15678750668286331793442211 23518126002429497690163317)
                    ·
                      refine ⟨2204824312727765408452811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23518126002429497690163317 2204824312727765408452811)
                      ·
                        rfl

theorem cell23_4293880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_4293880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293880 prefixEnd_4293880 := by exact prefixLift 4293880
  have htrace : WordTrace (prefixWord ++ tailWord_4293880) baseStart_4293880 baseEnd_4293880 := by
    simpa [prefixWord, tailWord_4293880, baseEnd_4293880] using wordTrace_append hprefix tailTrace_4293880
  have hstable : (prefixWord ++ tailWord_4293880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293880).length < 2 ^ (prefixWord ++ tailWord_4293880).sum := by decide
  have hdescent : baseEnd_4293880 < baseStart_4293880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293964 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_4293964 : Nat := 118140960795 + 4293964 * 2 ^ 59
def prefixEnd_4293964 : Nat := 4983230072969 + 3 ^ 40 * 4293964 * 2
def baseEnd_4293964 : Nat := 734955815034247693267475

theorem tailTrace_4293964 : CollatzResearch.WordTrace tailWord_4293964 prefixEnd_4293964 734955815034247693267475 := by
  unfold tailWord_4293964
  simp only [CollatzResearch.WordTrace]
  refine ⟨78306866707854626755640473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104409155610472835674187297 78306866707854626755640473)
  ·
    refine ⟨58730150030890970066730355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78306866707854626755640473 58730150030890970066730355)
    ·
      refine ⟨88095225046336455100095533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58730150030890970066730355 88095225046336455100095533)
      ·
        refine ⟨33035709392376170662535825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88095225046336455100095533 33035709392376170662535825)
        ·
          refine ⟨24776782044282127996901869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33035709392376170662535825 24776782044282127996901869)
          ·
            refine ⟨9291293266605797998838201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24776782044282127996901869 9291293266605797998838201)
            ·
              refine ⟨6968469949954348499128651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9291293266605797998838201 6968469949954348499128651)
              ·
                refine ⟨10452704924931522748692977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968469949954348499128651 10452704924931522748692977)
                ·
                  refine ⟨7839528693698642061519733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10452704924931522748692977 7839528693698642061519733)
                  ·
                    refine ⟨734955815034247693267475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7839528693698642061519733 734955815034247693267475)
                    ·
                      rfl

theorem cell23_4293964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_4293964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293964 prefixEnd_4293964 := by exact prefixLift 4293964
  have htrace : WordTrace (prefixWord ++ tailWord_4293964) baseStart_4293964 baseEnd_4293964 := by
    simpa [prefixWord, tailWord_4293964, baseEnd_4293964] using wordTrace_append hprefix tailTrace_4293964
  have hstable : (prefixWord ++ tailWord_4293964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293964).length < 2 ^ (prefixWord ++ tailWord_4293964).sum := by decide
  have hdescent : baseEnd_4293964 < baseStart_4293964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4293984 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_4293984 : Nat := 118140960795 + 4293984 * 2 ^ 59
def prefixEnd_4293984 : Nat := 4983230072969 + 3 ^ 40 * 4293984 * 2
def baseEnd_4293984 : Nat := 2204877714715833001552333

theorem tailTrace_4293984 : CollatzResearch.WordTrace tailWord_4293984 prefixEnd_4293984 2204877714715833001552333 := by
  unfold tailWord_4293984
  simp only [CollatzResearch.WordTrace]
  refine ⟨78307231437818398463504503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104409641917091197951339337 78307231437818398463504503)
  ·
    refine ⟨117460847156727597695256755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78307231437818398463504503 117460847156727597695256755)
    ·
      refine ⟨176191270735091396542885133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117460847156727597695256755 176191270735091396542885133)
      ·
        refine ⟨66071726525659273703581925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176191270735091396542885133 66071726525659273703581925)
        ·
          refine ⟨12388448723561113819421611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66071726525659273703581925 12388448723561113819421611)
          ·
            refine ⟨18582673085341670729132417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12388448723561113819421611 18582673085341670729132417)
            ·
              refine ⟨13937004814006253046849313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18582673085341670729132417 13937004814006253046849313)
              ·
                refine ⟨10452753610504689785136985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13937004814006253046849313 10452753610504689785136985)
                ·
                  refine ⟨7839565207878517338852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10452753610504689785136985 7839565207878517338852739)
                  ·
                    refine ⟨11759347811817776008279109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7839565207878517338852739 11759347811817776008279109)
                    ·
                      refine ⟨2204877714715833001552333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11759347811817776008279109 2204877714715833001552333)
                      ·
                        rfl

theorem cell23_4293984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_4293984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4293984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4293984 prefixEnd_4293984 := by exact prefixLift 4293984
  have htrace : WordTrace (prefixWord ++ tailWord_4293984) baseStart_4293984 baseEnd_4293984 := by
    simpa [prefixWord, tailWord_4293984, baseEnd_4293984] using wordTrace_append hprefix tailTrace_4293984
  have hstable : (prefixWord ++ tailWord_4293984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4293984).length < 2 ^ (prefixWord ++ tailWord_4293984).sum := by decide
  have hdescent : baseEnd_4293984 < baseStart_4293984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4293984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294007 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 6]
def baseStart_4294007 : Nat := 118140960795 + 4294007 * 2 ^ 59
def prefixEnd_4294007 : Nat := 4983230072969 + 3 ^ 40 * 4294007 * 2
def baseEnd_4294007 : Nat := 244987724974542934618303

theorem tailTrace_4294007 : CollatzResearch.WordTrace tailWord_4294007 prefixEnd_4294007 244987724974542934618303 := by
  unfold tailWord_4294007
  simp only [CollatzResearch.WordTrace]
  refine ⟨156615301754553471855096275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104410201169702314570064183 156615301754553471855096275)
  ·
    refine ⟨234922952631830207782644413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156615301754553471855096275 234922952631830207782644413)
    ·
      refine ⟨88096107236936327918491655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234922952631830207782644413 88096107236936327918491655)
      ·
        refine ⟨132144160855404491877737483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88096107236936327918491655 132144160855404491877737483)
        ·
          refine ⟨198216241283106737816606225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132144160855404491877737483 198216241283106737816606225)
          ·
            refine ⟨148662180962330053362454669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198216241283106737816606225 148662180962330053362454669)
            ·
              refine ⟨55748317860873770010920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148662180962330053362454669 55748317860873770010920501)
              ·
                refine ⟨5226404799456915938523797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55748317860873770010920501 5226404799456915938523797)
                ·
                  refine ⟨244987724974542934618303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5226404799456915938523797 244987724974542934618303)
                  ·
                    rfl

theorem cell23_4294007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 6].length) (baseStart_4294007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294007 prefixEnd_4294007 := by exact prefixLift 4294007
  have htrace : WordTrace (prefixWord ++ tailWord_4294007) baseStart_4294007 baseEnd_4294007 := by
    simpa [prefixWord, tailWord_4294007, baseEnd_4294007] using wordTrace_append hprefix tailTrace_4294007
  have hstable : (prefixWord ++ tailWord_4294007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294007).length < 2 ^ (prefixWord ++ tailWord_4294007).sum := by decide
  have hdescent : baseEnd_4294007 < baseStart_4294007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294018 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4294018 : Nat := 118140960795 + 4294018 * 2 ^ 59
def prefixEnd_4294018 : Nat := 4983230072969 + 3 ^ 40 * 4294018 * 2
def baseEnd_4294018 : Nat := 2204895173058085868527177

theorem tailTrace_4294018 : CollatzResearch.WordTrace tailWord_4294018 prefixEnd_4294018 2204895173058085868527177 := by
  unfold tailWord_4294018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39153925739378405183436677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104410468638342413822497805 39153925739378405183436677)
  ·
    refine ⟨7341361076133450971894377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39153925739378405183436677 7341361076133450971894377)
    ·
      refine ⟨5506020807100088228920783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7341361076133450971894377 5506020807100088228920783)
      ·
        refine ⟨8259031210650132343381175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506020807100088228920783 8259031210650132343381175)
        ·
          refine ⟨12388546815975198515071763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259031210650132343381175 12388546815975198515071763)
          ·
            refine ⟨18582820223962797772607645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12388546815975198515071763 18582820223962797772607645)
            ·
              refine ⟨6968557583986049164727867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18582820223962797772607645 6968557583986049164727867)
              ·
                refine ⟨10452836375979073747091801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968557583986049164727867 10452836375979073747091801)
                ·
                  refine ⟨7839627281984305310318851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10452836375979073747091801 7839627281984305310318851)
                  ·
                    refine ⟨11759440922976457965478277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7839627281984305310318851 11759440922976457965478277)
                    ·
                      refine ⟨2204895173058085868527177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11759440922976457965478277 2204895173058085868527177)
                      ·
                        rfl

theorem cell23_4294018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4294018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294018 prefixEnd_4294018 := by exact prefixLift 4294018
  have htrace : WordTrace (prefixWord ++ tailWord_4294018) baseStart_4294018 baseEnd_4294018 := by
    simpa [prefixWord, tailWord_4294018, baseEnd_4294018] using wordTrace_append hprefix tailTrace_4294018
  have hstable : (prefixWord ++ tailWord_4294018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294018).length < 2 ^ (prefixWord ++ tailWord_4294018).sum := by decide
  have hdescent : baseEnd_4294018 < baseStart_4294018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294051 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 3]
def baseStart_4294051 : Nat := 118140960795 + 4294051 * 2 ^ 59
def prefixEnd_4294051 : Nat := 4983230072969 + 3 ^ 40 * 4294051 * 2
def baseEnd_4294051 : Nat := 2204912117919684239414525

theorem tailTrace_4294051 : CollatzResearch.WordTrace tailWord_4294051 prefixEnd_4294051 2204912117919684239414525 := by
  unfold tailWord_4294051
  simp only [CollatzResearch.WordTrace]
  refine ⟨156616906566394067369698007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104411271044262711579798671 156616906566394067369698007)
  ·
    refine ⟨234925359849591101054547011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156616906566394067369698007 234925359849591101054547011)
    ·
      refine ⟨352388039774386651581820517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234925359849591101054547011 352388039774386651581820517)
      ·
        refine ⟨66072757457697497171591347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 352388039774386651581820517 66072757457697497171591347)
        ·
          refine ⟨99109136186546245757387021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66072757457697497171591347 99109136186546245757387021)
          ·
            refine ⟨37165926069954842159020133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99109136186546245757387021 37165926069954842159020133)
            ·
              refine ⟨6968611138116532904816275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37165926069954842159020133 6968611138116532904816275)
              ·
                refine ⟨10452916707174799357224413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968611138116532904816275 10452916707174799357224413)
                ·
                  refine ⟨3919843765190549758959155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10452916707174799357224413 3919843765190549758959155)
                  ·
                    refine ⟨5879765647785824638438733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919843765190549758959155 5879765647785824638438733)
                    ·
                      refine ⟨2204912117919684239414525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879765647785824638438733 2204912117919684239414525)
                      ·
                        rfl

theorem cell23_4294051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_4294051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294051 prefixEnd_4294051 := by exact prefixLift 4294051
  have htrace : WordTrace (prefixWord ++ tailWord_4294051) baseStart_4294051 baseEnd_4294051 := by
    simpa [prefixWord, tailWord_4294051, baseEnd_4294051] using wordTrace_append hprefix tailTrace_4294051
  have hstable : (prefixWord ++ tailWord_4294051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294051).length < 2 ^ (prefixWord ++ tailWord_4294051).sum := by decide
  have hdescent : baseEnd_4294051 < baseStart_4294051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294091 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 5, 2, 2]
def baseStart_4294091 : Nat := 118140960795 + 4294091 * 2 ^ 59
def prefixEnd_4294091 : Nat := 4983230072969 + 3 ^ 40 * 4294091 * 2
def baseEnd_4294091 : Nat := 2204932657145864082914341

theorem tailTrace_4294091 : CollatzResearch.WordTrace tailWord_4294091 prefixEnd_4294091 2204932657145864082914341 := by
  unfold tailWord_4294091
  simp only [CollatzResearch.WordTrace]
  refine ⟨156618365486249154201154127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104412243657499436134102751 156618365486249154201154127)
  ·
    refine ⟨234927548229373731301731191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156618365486249154201154127 234927548229373731301731191)
    ·
      refine ⟨352391322344060596952596787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234927548229373731301731191 352391322344060596952596787)
      ·
        refine ⟨528586983516090895428895181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352391322344060596952596787 528586983516090895428895181)
        ·
          refine ⟨198220118818534085785835693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528586983516090895428895181 198220118818534085785835693)
          ·
            refine ⟨74332544556950282169688385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198220118818534085785835693 74332544556950282169688385)
            ·
              refine ⟨55749408417712711627266289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74332544556950282169688385 55749408417712711627266289)
              ·
                refine ⟨41812056313284533720449717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55749408417712711627266289 41812056313284533720449717)
                ·
                  refine ⟨3919880279370425036292161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41812056313284533720449717 3919880279370425036292161)
                  ·
                    refine ⟨2939910209527818777219121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3919880279370425036292161 2939910209527818777219121)
                    ·
                      refine ⟨2204932657145864082914341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939910209527818777219121 2204932657145864082914341)
                      ·
                        rfl

theorem cell23_4294091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2, 2].length) (baseStart_4294091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294091 prefixEnd_4294091 := by exact prefixLift 4294091
  have htrace : WordTrace (prefixWord ++ tailWord_4294091) baseStart_4294091 baseEnd_4294091 := by
    simpa [prefixWord, tailWord_4294091, baseEnd_4294091] using wordTrace_append hprefix tailTrace_4294091
  have hstable : (prefixWord ++ tailWord_4294091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294091).length < 2 ^ (prefixWord ++ tailWord_4294091).sum := by decide
  have hdescent : baseEnd_4294091 < baseStart_4294091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294094 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_4294094 : Nat := 118140960795 + 4294094 * 2 ^ 59
def prefixEnd_4294094 : Nat := 4983230072969 + 3 ^ 40 * 4294094 * 2
def baseEnd_4294094 : Nat := 2204934197587827571176827

theorem tailTrace_4294094 : CollatzResearch.WordTrace tailWord_4294094 prefixEnd_4294094 2204934197587827571176827 := by
  unfold tailWord_4294094
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577309363154785714189167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104412316603492190475675557 19577309363154785714189167)
  ·
    refine ⟨29365964044732178571283751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19577309363154785714189167 29365964044732178571283751)
    ·
      refine ⟨44048946067098267856925627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29365964044732178571283751 44048946067098267856925627)
      ·
        refine ⟨66073419100647401785388441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44048946067098267856925627 66073419100647401785388441)
        ·
          refine ⟨49555064325485551339041331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66073419100647401785388441 49555064325485551339041331)
          ·
            refine ⟨74332596488228327008561997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49555064325485551339041331 74332596488228327008561997)
            ·
              refine ⟨27874723683085622628210749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74332596488228327008561997 27874723683085622628210749)
              ·
                refine ⟨10453021381157108485579031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27874723683085622628210749 10453021381157108485579031)
                ·
                  refine ⟨15679532071735662728368547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10453021381157108485579031 15679532071735662728368547)
                  ·
                    refine ⟨23519298107603494092552821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15679532071735662728368547 23519298107603494092552821)
                    ·
                      refine ⟨2204934197587827571176827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23519298107603494092552821 2204934197587827571176827)
                      ·
                        rfl

theorem cell23_4294094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_4294094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294094 prefixEnd_4294094 := by exact prefixLift 4294094
  have htrace : WordTrace (prefixWord ++ tailWord_4294094) baseStart_4294094 baseEnd_4294094 := by
    simpa [prefixWord, tailWord_4294094, baseEnd_4294094] using wordTrace_append hprefix tailTrace_4294094
  have hstable : (prefixWord ++ tailWord_4294094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294094).length < 2 ^ (prefixWord ++ tailWord_4294094).sum := by decide
  have hdescent : baseEnd_4294094 < baseStart_4294094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294101 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_4294101 : Nat := 118140960795 + 4294101 * 2 ^ 59
def prefixEnd_4294101 : Nat := 4983230072969 + 3 ^ 40 * 4294101 * 2
def baseEnd_4294101 : Nat := 734979263984136347929765

theorem tailTrace_4294101 : CollatzResearch.WordTrace tailWord_4294101 prefixEnd_4294101 734979263984136347929765 := by
  unfold tailWord_4294101
  simp only [CollatzResearch.WordTrace]
  refine ⟨156618730216212925909018157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104412486810808617272678771 156618730216212925909018157)
  ·
    refine ⟨58732023831079847215881809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156618730216212925909018157 58732023831079847215881809)
    ·
      refine ⟨44049017873309885411911357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58732023831079847215881809 44049017873309885411911357)
      ·
        refine ⟨16518381702491207029466759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44049017873309885411911357 16518381702491207029466759)
        ·
          refine ⟨24777572553736810544200139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16518381702491207029466759 24777572553736810544200139)
          ·
            refine ⟨37166358830605215816300209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24777572553736810544200139 37166358830605215816300209)
            ·
              refine ⟨27874769122953911862225157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37166358830605215816300209 27874769122953911862225157)
              ·
                refine ⟨5226519210553858474167217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27874769122953911862225157 5226519210553858474167217)
                ·
                  refine ⟨3919889407915393855625413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5226519210553858474167217 3919889407915393855625413)
                  ·
                    refine ⟨734979263984136347929765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919889407915393855625413 734979263984136347929765)
                    ·
                      rfl

theorem cell23_4294101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_4294101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294101 prefixEnd_4294101 := by exact prefixLift 4294101
  have htrace : WordTrace (prefixWord ++ tailWord_4294101) baseStart_4294101 baseEnd_4294101 := by
    simpa [prefixWord, tailWord_4294101, baseEnd_4294101] using wordTrace_append hprefix tailTrace_4294101
  have hstable : (prefixWord ++ tailWord_4294101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294101).length < 2 ^ (prefixWord ++ tailWord_4294101).sum := by decide
  have hdescent : baseEnd_4294101 < baseStart_4294101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294125 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4294125 : Nat := 118140960795 + 4294125 * 2 ^ 59
def prefixEnd_4294125 : Nat := 4983230072969 + 3 ^ 40 * 4294125 * 2
def baseEnd_4294125 : Nat := 2204950115488116949889185

theorem tailTrace_4294125 : CollatzResearch.WordTrace tailWord_4294125 prefixEnd_4294125 2204950115488116949889185 := by
  unfold tailWord_4294125
  simp only [CollatzResearch.WordTrace]
  refine ⟨156619605568125978007891829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104413070378750652005261219 156619605568125978007891829)
  ·
    refine ⟨14683088022011810438239859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156619605568125978007891829 14683088022011810438239859)
    ·
      refine ⟨22024632033017715657359789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14683088022011810438239859 22024632033017715657359789)
      ·
        refine ⟨8259237012381643371509921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22024632033017715657359789 8259237012381643371509921)
        ·
          refine ⟨6194427759286232528632441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8259237012381643371509921 6194427759286232528632441)
          ·
            refine ⟨4645820819464674396474331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6194427759286232528632441 4645820819464674396474331)
            ·
              refine ⟨6968731229197011594711497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645820819464674396474331 6968731229197011594711497)
              ·
                refine ⟨5226548421897758696033623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6968731229197011594711497 5226548421897758696033623)
                ·
                  refine ⟨7839822632846638044050435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226548421897758696033623 7839822632846638044050435)
                  ·
                    refine ⟨11759733949269957066075653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7839822632846638044050435 11759733949269957066075653)
                    ·
                      refine ⟨2204950115488116949889185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11759733949269957066075653 2204950115488116949889185)
                      ·
                        rfl

theorem cell23_4294125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4294125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294125 prefixEnd_4294125 := by exact prefixLift 4294125
  have htrace : WordTrace (prefixWord ++ tailWord_4294125) baseStart_4294125 baseEnd_4294125 := by
    simpa [prefixWord, tailWord_4294125, baseEnd_4294125] using wordTrace_append hprefix tailTrace_4294125
  have hstable : (prefixWord ++ tailWord_4294125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294125).length < 2 ^ (prefixWord ++ tailWord_4294125).sum := by decide
  have hdescent : baseEnd_4294125 < baseStart_4294125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294128 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_4294128 : Nat := 118140960795 + 4294128 * 2 ^ 59
def prefixEnd_4294128 : Nat := 4983230072969 + 3 ^ 40 * 4294128 * 2
def baseEnd_4294128 : Nat := 2204951655930080438151671

theorem tailTrace_4294128 : CollatzResearch.WordTrace tailWord_4294128 prefixEnd_4294128 2204951655930080438151671 := by
  unfold tailWord_4294128
  simp only [CollatzResearch.WordTrace]
  refine ⟨78309857493557554760125519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104413143324743406346834025 78309857493557554760125519)
  ·
    refine ⟨117464786240336332140188279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78309857493557554760125519 117464786240336332140188279)
    ·
      refine ⟨176197179360504498210282419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117464786240336332140188279 176197179360504498210282419)
      ·
        refine ⟨264295769040756747315423629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176197179360504498210282419 264295769040756747315423629)
        ·
          refine ⟨99110913390283780243283861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264295769040756747315423629 99110913390283780243283861)
          ·
            refine ⟨4645824065169552198903931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99110913390283780243283861 4645824065169552198903931)
            ·
              refine ⟨6968736097754328298355897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645824065169552198903931 6968736097754328298355897)
              ·
                refine ⟨5226552073315746223766923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6968736097754328298355897 5226552073315746223766923)
                ·
                  refine ⟨7839828109973619335650385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226552073315746223766923 7839828109973619335650385)
                  ·
                    refine ⟨5879871082480214501737789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7839828109973619335650385 5879871082480214501737789)
                    ·
                      refine ⟨2204951655930080438151671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879871082480214501737789 2204951655930080438151671)
                      ·
                        rfl

theorem cell23_4294128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_4294128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294128 prefixEnd_4294128 := by exact prefixLift 4294128
  have htrace : WordTrace (prefixWord ++ tailWord_4294128) baseStart_4294128 baseEnd_4294128 := by
    simpa [prefixWord, tailWord_4294128, baseEnd_4294128] using wordTrace_append hprefix tailTrace_4294128
  have hstable : (prefixWord ++ tailWord_4294128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294128).length < 2 ^ (prefixWord ++ tailWord_4294128).sum := by decide
  have hdescent : baseEnd_4294128 < baseStart_4294128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294141 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_4294141 : Nat := 118140960795 + 4294141 * 2 ^ 59
def prefixEnd_4294141 : Nat := 4983230072969 + 3 ^ 40 * 4294141 * 2
def baseEnd_4294141 : Nat := 2204958331178588887289111

theorem tailTrace_4294141 : CollatzResearch.WordTrace tailWord_4294141 prefixEnd_4294141 2204958331178588887289111 := by
  unfold tailWord_4294141
  simp only [CollatzResearch.WordTrace]
  refine ⟨156620189136068012740474277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104413459424045341826982851 156620189136068012740474277)
  ·
    refine ⟨29366285463012752388838927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156620189136068012740474277 29366285463012752388838927)
    ·
      refine ⟨44049428194519128583258391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29366285463012752388838927 44049428194519128583258391)
      ·
        refine ⟨66074142291778692874887587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44049428194519128583258391 66074142291778692874887587)
        ·
          refine ⟨99111213437668039312331381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66074142291778692874887587 99111213437668039312331381)
          ·
            refine ⟨9291676259781378685531067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99111213437668039312331381 9291676259781378685531067)
            ·
              refine ⟨13937514389672068028296601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291676259781378685531067 13937514389672068028296601)
              ·
                refine ⟨10453135792254051021222451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13937514389672068028296601 10453135792254051021222451)
                ·
                  refine ⟨15679703688381076531833677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10453135792254051021222451 15679703688381076531833677)
                  ·
                    refine ⟨5879888883142903699437629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15679703688381076531833677 5879888883142903699437629)
                    ·
                      refine ⟨2204958331178588887289111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879888883142903699437629 2204958331178588887289111)
                      ·
                        rfl

theorem cell23_4294141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_4294141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294141 prefixEnd_4294141 := by exact prefixLift 4294141
  have htrace : WordTrace (prefixWord ++ tailWord_4294141) baseStart_4294141 baseEnd_4294141 := by
    simpa [prefixWord, tailWord_4294141, baseEnd_4294141] using wordTrace_append hprefix tailTrace_4294141
  have hstable : (prefixWord ++ tailWord_4294141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294141).length < 2 ^ (prefixWord ++ tailWord_4294141).sum := by decide
  have hdescent : baseEnd_4294141 < baseStart_4294141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294142 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4294142 : Nat := 118140960795 + 4294142 * 2 ^ 59
def prefixEnd_4294142 : Nat := 4983230072969 + 3 ^ 40 * 4294142 * 2
def baseEnd_4294142 : Nat := 2204958844659243383376607

theorem tailTrace_4294142 : CollatzResearch.WordTrace tailWord_4294142 prefixEnd_4294142 2204958844659243383376607 := by
  unfold tailWord_4294142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577528201133048738907585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104413483739376259940840453 19577528201133048738907585)
  ·
    refine ⟨14683146150849786554180689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19577528201133048738907585 14683146150849786554180689)
    ·
      refine ⟨11012359613137339915635517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14683146150849786554180689 11012359613137339915635517)
      ·
        refine ⟨4129634854926502468363319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11012359613137339915635517 4129634854926502468363319)
        ·
          refine ⟨6194452282389753702544979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129634854926502468363319 6194452282389753702544979)
          ·
            refine ⟨9291678423584630553817469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194452282389753702544979 9291678423584630553817469)
            ·
              refine ⟨3484379408844236457681551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9291678423584630553817469 3484379408844236457681551)
              ·
                refine ⟨5226569113266354686522327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484379408844236457681551 5226569113266354686522327)
                ·
                  refine ⟨7839853669899532029783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226569113266354686522327 7839853669899532029783491)
                  ·
                    refine ⟨11759780504849298044675237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7839853669899532029783491 11759780504849298044675237)
                    ·
                      refine ⟨2204958844659243383376607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11759780504849298044675237 2204958844659243383376607)
                      ·
                        rfl

theorem cell23_4294142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4294142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294142 prefixEnd_4294142 := by exact prefixLift 4294142
  have htrace : WordTrace (prefixWord ++ tailWord_4294142) baseStart_4294142 baseEnd_4294142 := by
    simpa [prefixWord, tailWord_4294142, baseEnd_4294142] using wordTrace_append hprefix tailTrace_4294142
  have hstable : (prefixWord ++ tailWord_4294142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294142).length < 2 ^ (prefixWord ++ tailWord_4294142).sum := by decide
  have hdescent : baseEnd_4294142 < baseStart_4294142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294145 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_4294145 : Nat := 118140960795 + 4294145 * 2 ^ 59
def prefixEnd_4294145 : Nat := 4983230072969 + 3 ^ 40 * 4294145 * 2
def baseEnd_4294145 : Nat := 2204960385101206871639093

theorem tailTrace_4294145 : CollatzResearch.WordTrace tailWord_4294145 prefixEnd_4294145 2204960385101206871639093 := by
  unfold tailWord_4294145
  simp only [CollatzResearch.WordTrace]
  refine ⟨156620335028053521423619889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104413556685369014282413259 156620335028053521423619889)
  ·
    refine ⟨117465251271040141067714917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156620335028053521423619889 117465251271040141067714917)
    ·
      refine ⟨22024734613320026450196547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117465251271040141067714917 22024734613320026450196547)
      ·
        refine ⟨33037101919980039675294821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22024734613320026450196547 33037101919980039675294821)
        ·
          refine ⟨6194456609996257439117779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33037101919980039675294821 6194456609996257439117779)
          ·
            refine ⟨9291684914994386158676669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194456609996257439117779 9291684914994386158676669)
            ·
              refine ⟨3484381843122894809503751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9291684914994386158676669 3484381843122894809503751)
              ·
                refine ⟨5226572764684342214255627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484381843122894809503751 5226572764684342214255627)
                ·
                  refine ⟨7839859147026513321383441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226572764684342214255627 7839859147026513321383441)
                  ·
                    refine ⟨5879894360269884991037581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7839859147026513321383441 5879894360269884991037581)
                    ·
                      refine ⟨2204960385101206871639093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5879894360269884991037581 2204960385101206871639093)
                      ·
                        rfl

theorem cell23_4294145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_4294145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294145 prefixEnd_4294145 := by exact prefixLift 4294145
  have htrace : WordTrace (prefixWord ++ tailWord_4294145) baseStart_4294145 baseEnd_4294145 := by
    simpa [prefixWord, tailWord_4294145, baseEnd_4294145] using wordTrace_append hprefix tailTrace_4294145
  have hstable : (prefixWord ++ tailWord_4294145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294145).length < 2 ^ (prefixWord ++ tailWord_4294145).sum := by decide
  have hdescent : baseEnd_4294145 < baseStart_4294145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294194 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4294194 : Nat := 118140960795 + 4294194 * 2 ^ 59
def prefixEnd_4294194 : Nat := 4983230072969 + 3 ^ 40 * 4294194 * 2
def baseEnd_4294194 : Nat := 2204985545653277179926367

theorem tailTrace_4294194 : CollatzResearch.WordTrace tailWord_4294194 prefixEnd_4294194 2204985545653277179926367 := by
  unfold tailWord_4294194
  simp only [CollatzResearch.WordTrace]
  refine ⟨39155530551219000698038409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104414748136584001861435757 39155530551219000698038409)
  ·
    refine ⟨29366647913414250523528807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39155530551219000698038409 29366647913414250523528807)
    ·
      refine ⟨44049971870121375785293211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29366647913414250523528807 44049971870121375785293211)
      ·
        refine ⟨66074957805182063677939817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44049971870121375785293211 66074957805182063677939817)
        ·
          refine ⟨49556218353886547758454863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66074957805182063677939817 49556218353886547758454863)
          ·
            refine ⟨74334327530829821637682295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49556218353886547758454863 74334327530829821637682295)
            ·
              refine ⟨111501491296244732456523443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74334327530829821637682295 111501491296244732456523443)
              ·
                refine ⟨167252236944367098684785165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111501491296244732456523443 167252236944367098684785165)
                ·
                  refine ⟨62719588854137662006794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167252236944367098684785165 62719588854137662006794437)
                  ·
                    refine ⟨11759922910150811626273957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62719588854137662006794437 11759922910150811626273957)
                    ·
                      refine ⟨2204985545653277179926367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11759922910150811626273957 2204985545653277179926367)
                      ·
                        rfl

theorem cell23_4294194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4294194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294194 prefixEnd_4294194 := by exact prefixLift 4294194
  have htrace : WordTrace (prefixWord ++ tailWord_4294194) baseStart_4294194 baseEnd_4294194 := by
    simpa [prefixWord, tailWord_4294194, baseEnd_4294194] using wordTrace_append hprefix tailTrace_4294194
  have hstable : (prefixWord ++ tailWord_4294194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294194).length < 2 ^ (prefixWord ++ tailWord_4294194).sum := by decide
  have hdescent : baseEnd_4294194 < baseStart_4294194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294215 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_4294215 : Nat := 118140960795 + 4294215 * 2 ^ 59
def prefixEnd_4294215 : Nat := 4983230072969 + 3 ^ 40 * 4294215 * 2
def baseEnd_4294215 : Nat := 2204996328747021597763771

theorem tailTrace_4294215 : CollatzResearch.WordTrace tailWord_4294215 prefixEnd_4294215 2204996328747021597763771 := by
  unfold tailWord_4294215
  simp only [CollatzResearch.WordTrace]
  refine ⟨156622888137799923378668099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104415258758533282252445399 156622888137799923378668099)
  ·
    refine ⟨234934332206699885068002149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156622888137799923378668099 234934332206699885068002149)
    ·
      refine ⟨44050187288756228450250403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 234934332206699885068002149 44050187288756228450250403)
      ·
        refine ⟨66075280933134342675375605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44050187288756228450250403 66075280933134342675375605)
        ·
          refine ⟨6194557587481344625816463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66075280933134342675375605 6194557587481344625816463)
          ·
            refine ⟨9291836381222016938724695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194557587481344625816463 9291836381222016938724695)
            ·
              refine ⟨13937754571833025408087043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291836381222016938724695 13937754571833025408087043)
              ·
                refine ⟨20906631857749538112130565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13937754571833025408087043 20906631857749538112130565)
                ·
                  refine ⟨3919993473328038396024481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20906631857749538112130565 3919993473328038396024481)
                  ·
                    refine ⟨2939995104996028797018361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3919993473328038396024481 2939995104996028797018361)
                    ·
                      refine ⟨2204996328747021597763771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2939995104996028797018361 2204996328747021597763771)
                      ·
                        rfl

theorem cell23_4294215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_4294215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294215 prefixEnd_4294215 := by exact prefixLift 4294215
  have htrace : WordTrace (prefixWord ++ tailWord_4294215) baseStart_4294215 baseEnd_4294215 := by
    simpa [prefixWord, tailWord_4294215, baseEnd_4294215] using wordTrace_append hprefix tailTrace_4294215
  have hstable : (prefixWord ++ tailWord_4294215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294215).length < 2 ^ (prefixWord ++ tailWord_4294215).sum := by decide
  have hdescent : baseEnd_4294215 < baseStart_4294215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294231 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_4294231 : Nat := 118140960795 + 4294231 * 2 ^ 59
def prefixEnd_4294231 : Nat := 4983230072969 + 3 ^ 40 * 4294231 * 2
def baseEnd_4294231 : Nat := 2205004544437493535163697

theorem tailTrace_4294231 : CollatzResearch.WordTrace tailWord_4294231 prefixEnd_4294231 2205004544437493535163697 := by
  unfold tailWord_4294231
  simp only [CollatzResearch.WordTrace]
  refine ⟨156623471705741958111250547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104415647803827972074167031 156623471705741958111250547)
  ·
    refine ⟨234935207558612937166875821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156623471705741958111250547 234935207558612937166875821)
    ·
      refine ⟨88100702834479851437578433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234935207558612937166875821 88100702834479851437578433)
      ·
        refine ⟨66075527125859888578183825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88100702834479851437578433 66075527125859888578183825)
        ·
          refine ⟨49556645344394916433637869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66075527125859888578183825 49556645344394916433637869)
          ·
            refine ⟨18583742004148093662614201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49556645344394916433637869 18583742004148093662614201)
            ·
              refine ⟨13937806503111070246960651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18583742004148093662614201 13937806503111070246960651)
              ·
                refine ⟨20906709754666605370440977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13937806503111070246960651 20906709754666605370440977)
                ·
                  refine ⟨15680032315999954027830733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20906709754666605370440977 15680032315999954027830733)
                  ·
                    refine ⟨5880012118499982760436525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15680032315999954027830733 5880012118499982760436525)
                    ·
                      refine ⟨2205004544437493535163697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880012118499982760436525 2205004544437493535163697)
                      ·
                        rfl

theorem cell23_4294231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_4294231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294231 prefixEnd_4294231 := by exact prefixLift 4294231
  have htrace : WordTrace (prefixWord ++ tailWord_4294231) baseStart_4294231 baseEnd_4294231 := by
    simpa [prefixWord, tailWord_4294231, baseEnd_4294231] using wordTrace_append hprefix tailTrace_4294231
  have hstable : (prefixWord ++ tailWord_4294231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294231).length < 2 ^ (prefixWord ++ tailWord_4294231).sum := by decide
  have hdescent : baseEnd_4294231 < baseStart_4294231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294308 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_4294308 : Nat := 118140960795 + 4294308 * 2 ^ 59
def prefixEnd_4294308 : Nat := 4983230072969 + 3 ^ 40 * 4294308 * 2
def baseEnd_4294308 : Nat := 2205044082447889733900843

theorem tailTrace_4294308 : CollatzResearch.WordTrace tailWord_4294308 prefixEnd_4294308 2205044082447889733900843 := by
  unfold tailWord_4294308
  simp only [CollatzResearch.WordTrace]
  refine ⟨78313140063231500130901789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104417520084308666841202385 78313140063231500130901789)
  ·
    refine ⟨29367427523711812549088171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78313140063231500130901789 29367427523711812549088171)
    ·
      refine ⟨44051141285567718823632257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29367427523711812549088171 44051141285567718823632257)
      ·
        refine ⟨33038355964175789117724193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44051141285567718823632257 33038355964175789117724193)
        ·
          refine ⟨24778766973131841838293145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33038355964175789117724193 24778766973131841838293145)
          ·
            refine ⟨18584075229848881378719859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24778766973131841838293145 18584075229848881378719859)
            ·
              refine ⟨27876112844773322068079789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18584075229848881378719859 27876112844773322068079789)
              ·
                refine ⟨10453542316789995775529921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27876112844773322068079789 10453542316789995775529921)
                ·
                  refine ⟨7840156737592496831647441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10453542316789995775529921 7840156737592496831647441)
                  ·
                    refine ⟨5880117553194372623735581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7840156737592496831647441 5880117553194372623735581)
                    ·
                      refine ⟨2205044082447889733900843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880117553194372623735581 2205044082447889733900843)
                      ·
                        rfl

theorem cell23_4294308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_4294308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294308 prefixEnd_4294308 := by exact prefixLift 4294308
  have htrace : WordTrace (prefixWord ++ tailWord_4294308) baseStart_4294308 baseEnd_4294308 := by
    simpa [prefixWord, tailWord_4294308, baseEnd_4294308] using wordTrace_append hprefix tailTrace_4294308
  have hstable : (prefixWord ++ tailWord_4294308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294308).length < 2 ^ (prefixWord ++ tailWord_4294308).sum := by decide
  have hdescent : baseEnd_4294308 < baseStart_4294308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294332 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_4294332 : Nat := 118140960795 + 4294332 * 2 ^ 59
def prefixEnd_4294332 : Nat := 4983230072969 + 3 ^ 40 * 4294332 * 2
def baseEnd_4294332 : Nat := 735018801994532546666911

theorem tailTrace_4294332 : CollatzResearch.WordTrace tailWord_4294332 prefixEnd_4294332 735018801994532546666911 := by
  unfold tailWord_4294332
  simp only [CollatzResearch.WordTrace]
  refine ⟨78313577739188026180338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104418103652250701573784833 78313577739188026180338625)
  ·
    refine ⟨58735183304391019635253969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78313577739188026180338625 58735183304391019635253969)
    ·
      refine ⟨44051387478293264726440477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58735183304391019635253969 44051387478293264726440477)
      ·
        refine ⟨16519270304359974272415179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44051387478293264726440477 16519270304359974272415179)
        ·
          refine ⟨24778905456539961408622769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16519270304359974272415179 24778905456539961408622769)
          ·
            refine ⟨18584179092404971056467077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24778905456539961408622769 18584179092404971056467077)
            ·
              refine ⟨3484533579825932073087577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18584179092404971056467077 3484533579825932073087577)
              ·
                refine ⟨2613400184869449054815683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484533579825932073087577 2613400184869449054815683)
                ·
                  refine ⟨3920100277304173582223525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613400184869449054815683 3920100277304173582223525)
                  ·
                    refine ⟨735018801994532546666911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920100277304173582223525 735018801994532546666911)
                    ·
                      rfl

theorem cell23_4294332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_4294332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294332 prefixEnd_4294332 := by exact prefixLift 4294332
  have htrace : WordTrace (prefixWord ++ tailWord_4294332) baseStart_4294332 baseEnd_4294332 := by
    simpa [prefixWord, tailWord_4294332, baseEnd_4294332] using wordTrace_append hprefix tailTrace_4294332
  have hstable : (prefixWord ++ tailWord_4294332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294332).length < 2 ^ (prefixWord ++ tailWord_4294332).sum := by decide
  have hdescent : baseEnd_4294332 < baseStart_4294332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294372 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_4294372 : Nat := 118140960795 + 4294372 * 2 ^ 59
def prefixEnd_4294372 : Nat := 4983230072969 + 3 ^ 40 * 4294372 * 2
def baseEnd_4294372 : Nat := 2205076945209777483500549

theorem tailTrace_4294372 : CollatzResearch.WordTrace tailWord_4294372 prefixEnd_4294372 2205076945209777483500549 := by
  unfold tailWord_4294372
  simp only [CollatzResearch.WordTrace]
  refine ⟨78314307199115569596066685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104419076265487426128088913 78314307199115569596066685)
  ·
    refine ⟨29367865199668338598525007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78314307199115569596066685 29367865199668338598525007)
    ·
      refine ⟨44051797799502507897787511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29367865199668338598525007 44051797799502507897787511)
      ·
        refine ⟨66077696699253761846681267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44051797799502507897787511 66077696699253761846681267)
        ·
          refine ⟨99116545048880642770021901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66077696699253761846681267 99116545048880642770021901)
          ·
            refine ⟨37168704393330241038758213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99116545048880642770021901 37168704393330241038758213)
            ·
              refine ⟨6969132073749420194767165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37168704393330241038758213 6969132073749420194767165)
              ·
                refine ⟨2613424527656032573037687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6969132073749420194767165 2613424527656032573037687)
                ·
                  refine ⟨3920136791484048859556531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613424527656032573037687 3920136791484048859556531)
                  ·
                    refine ⟨5880205187226073289334797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3920136791484048859556531 5880205187226073289334797)
                    ·
                      refine ⟨2205076945209777483500549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880205187226073289334797 2205076945209777483500549)
                      ·
                        rfl

theorem cell23_4294372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_4294372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294372 prefixEnd_4294372 := by exact prefixLift 4294372
  have htrace : WordTrace (prefixWord ++ tailWord_4294372) baseStart_4294372 baseEnd_4294372 := by
    simpa [prefixWord, tailWord_4294372, baseEnd_4294372] using wordTrace_append hprefix tailTrace_4294372
  have hstable : (prefixWord ++ tailWord_4294372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294372).length < 2 ^ (prefixWord ++ tailWord_4294372).sum := by decide
  have hdescent : baseEnd_4294372 < baseStart_4294372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294391 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_4294391 : Nat := 118140960795 + 4294391 * 2 ^ 59
def prefixEnd_4294391 : Nat := 4983230072969 + 3 ^ 40 * 4294391 * 2
def baseEnd_4294391 : Nat := 2205086701342212909162961

theorem tailTrace_4294391 : CollatzResearch.WordTrace tailWord_4294391 prefixEnd_4294391 2205086701342212909162961 := by
  unfold tailWord_4294391
  simp only [CollatzResearch.WordTrace]
  refine ⟨156629307385162305437075027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104419538256774870291383351 156629307385162305437075027)
  ·
    refine ⟨234943961077743458155612541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156629307385162305437075027 234943961077743458155612541)
    ·
      refine ⟨88103985404153796808354703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 234943961077743458155612541 88103985404153796808354703)
      ·
        refine ⟨132155978106230695212532055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88103985404153796808354703 132155978106230695212532055)
        ·
          refine ⟨198233967159346042818798083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132155978106230695212532055 198233967159346042818798083)
          ·
            refine ⟨297350950739019064228197125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198233967159346042818798083 297350950739019064228197125)
            ·
              refine ⟨55753303263566074542786961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297350950739019064228197125 55753303263566074542786961)
              ·
                refine ⟨41814977447674555907090221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55753303263566074542786961 41814977447674555907090221)
                ·
                  refine ⟨15680616542877958465158833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41814977447674555907090221 15680616542877958465158833)
                  ·
                    refine ⟨11760462407158468848869125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15680616542877958465158833 11760462407158468848869125)
                    ·
                      refine ⟨2205086701342212909162961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11760462407158468848869125 2205086701342212909162961)
                      ·
                        rfl

theorem cell23_4294391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_4294391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294391 prefixEnd_4294391 := by exact prefixLift 4294391
  have htrace : WordTrace (prefixWord ++ tailWord_4294391) baseStart_4294391 baseEnd_4294391 := by
    simpa [prefixWord, tailWord_4294391, baseEnd_4294391] using wordTrace_append hprefix tailTrace_4294391
  have hstable : (prefixWord ++ tailWord_4294391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294391).length < 2 ^ (prefixWord ++ tailWord_4294391).sum := by decide
  have hdescent : baseEnd_4294391 < baseStart_4294391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294428 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4294428 : Nat := 118140960795 + 4294428 * 2 ^ 59
def prefixEnd_4294428 : Nat := 4983230072969 + 3 ^ 40 * 4294428 * 2
def baseEnd_4294428 : Nat := 2205105700126429264400291

theorem tailTrace_4294428 : CollatzResearch.WordTrace tailWord_4294428 prefixEnd_4294428 2205105700126429264400291 := by
  unfold tailWord_4294428
  simp only [CollatzResearch.WordTrace]
  refine ⟨78315328443014130378085969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104420437924018840504114625 78315328443014130378085969)
  ·
    refine ⟨58736496332260597783564477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78315328443014130378085969 58736496332260597783564477)
    ·
      refine ⟨22026186124597724168836679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58736496332260597783564477 22026186124597724168836679)
      ·
        refine ⟨33039279186896586253255019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22026186124597724168836679 33039279186896586253255019)
        ·
          refine ⟨49558918780344879379882529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33039279186896586253255019 49558918780344879379882529)
          ·
            refine ⟨37169189085258659534911897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49558918780344879379882529 37169189085258659534911897)
            ·
              refine ⟨27876891813943994651183923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37169189085258659534911897 27876891813943994651183923)
              ·
                refine ⟨41815337720915991976775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27876891813943994651183923 41815337720915991976775885)
                ·
                  refine ⟨15680751645343496991290957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41815337720915991976775885 15680751645343496991290957)
                  ·
                    refine ⟨5880281867003811371734109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15680751645343496991290957 5880281867003811371734109)
                    ·
                      refine ⟨2205105700126429264400291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5880281867003811371734109 2205105700126429264400291)
                      ·
                        rfl

theorem cell23_4294428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4294428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294428 prefixEnd_4294428 := by exact prefixLift 4294428
  have htrace : WordTrace (prefixWord ++ tailWord_4294428) baseStart_4294428 baseEnd_4294428 := by
    simpa [prefixWord, tailWord_4294428, baseEnd_4294428] using wordTrace_append hprefix tailTrace_4294428
  have hstable : (prefixWord ++ tailWord_4294428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294428).length < 2 ^ (prefixWord ++ tailWord_4294428).sum := by decide
  have hdescent : baseEnd_4294428 < baseStart_4294428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294446 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4294446 : Nat := 118140960795 + 4294446 * 2 ^ 59
def prefixEnd_4294446 : Nat := 4983230072969 + 3 ^ 40 * 4294446 * 2
def baseEnd_4294446 : Nat := 2205114942778210193975209

theorem tailTrace_4294446 : CollatzResearch.WordTrace tailWord_4294446 prefixEnd_4294446 2205114942778210193975209 := by
  unfold tailWord_4294446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578914174995381228790899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104420875599975366553551461 19578914174995381228790899)
  ·
    refine ⟨29368371262493071843186349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19578914174995381228790899 29368371262493071843186349)
    ·
      refine ⟨11013139223434901941194881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29368371262493071843186349 11013139223434901941194881)
      ·
        refine ⟨8259854417576176455896161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11013139223434901941194881 8259854417576176455896161)
        ·
          refine ⟨6194890813182132341922121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8259854417576176455896161 6194890813182132341922121)
          ·
            refine ⟨4646168109886599256441591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6194890813182132341922121 4646168109886599256441591)
            ·
              refine ⟨6969252164829898884662387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646168109886599256441591 6969252164829898884662387)
              ·
                refine ⟨10453878247244848326993581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6969252164829898884662387 10453878247244848326993581)
                ·
                  refine ⟨3920204342716818122622593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10453878247244848326993581 3920204342716818122622593)
                  ·
                    refine ⟨2940153257037613591966945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3920204342716818122622593 2940153257037613591966945)
                    ·
                      refine ⟨2205114942778210193975209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940153257037613591966945 2205114942778210193975209)
                      ·
                        rfl

theorem cell23_4294446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4294446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294446 prefixEnd_4294446 := by exact prefixLift 4294446
  have htrace : WordTrace (prefixWord ++ tailWord_4294446) baseStart_4294446 baseEnd_4294446 := by
    simpa [prefixWord, tailWord_4294446, baseEnd_4294446] using wordTrace_append hprefix tailTrace_4294446
  have hstable : (prefixWord ++ tailWord_4294446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294446).length < 2 ^ (prefixWord ++ tailWord_4294446).sum := by decide
  have hdescent : baseEnd_4294446 < baseStart_4294446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294472 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_4294472 : Nat := 118140960795 + 4294472 * 2 ^ 59
def prefixEnd_4294472 : Nat := 4983230072969 + 3 ^ 40 * 4294472 * 2
def baseEnd_4294472 : Nat := 2205128293275227092250089

theorem tailTrace_4294472 : CollatzResearch.WordTrace tailWord_4294472 prefixEnd_4294472 2205128293275227092250089 := by
  unfold tailWord_4294472
  simp only [CollatzResearch.WordTrace]
  refine ⟨78316130848934428135386835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104421507798579237513849113 78316130848934428135386835)
  ·
    refine ⟨117474196273401642203080253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78316130848934428135386835 117474196273401642203080253)
    ·
      refine ⟨44052823602525615826155095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117474196273401642203080253 44052823602525615826155095)
      ·
        refine ⟨66079235403788423739232643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44052823602525615826155095 66079235403788423739232643)
        ·
          refine ⟨99118853105682635608848965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66079235403788423739232643 99118853105682635608848965)
          ·
            refine ⟨18584784957315494176659181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99118853105682635608848965 18584784957315494176659181)
            ·
              refine ⟨6969294358993310316247193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18584784957315494176659181 6969294358993310316247193)
              ·
                refine ⟨5226970769244982737185395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6969294358993310316247193 5226970769244982737185395)
                ·
                  refine ⟨7840456153867474105778093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226970769244982737185395 7840456153867474105778093)
                  ·
                    refine ⟨2940171057700302789666785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7840456153867474105778093 2940171057700302789666785)
                    ·
                      refine ⟨2205128293275227092250089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940171057700302789666785 2205128293275227092250089)
                      ·
                        rfl

theorem cell23_4294472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_4294472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294472 prefixEnd_4294472 := by exact prefixLift 4294472
  have htrace : WordTrace (prefixWord ++ tailWord_4294472) baseStart_4294472 baseEnd_4294472 := by
    simpa [prefixWord, tailWord_4294472, baseEnd_4294472] using wordTrace_append hprefix tailTrace_4294472
  have hstable : (prefixWord ++ tailWord_4294472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294472).length < 2 ^ (prefixWord ++ tailWord_4294472).sum := by decide
  have hdescent : baseEnd_4294472 < baseStart_4294472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294485 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4294485 : Nat := 118140960795 + 4294485 * 2 ^ 59
def prefixEnd_4294485 : Nat := 4983230072969 + 3 ^ 40 * 4294485 * 2
def baseEnd_4294485 : Nat := 2205134968523735541387529

theorem tailTrace_4294485 : CollatzResearch.WordTrace tailWord_4294485 prefixEnd_4294485 2205134968523735541387529 := by
  unfold tailWord_4294485
  simp only [CollatzResearch.WordTrace]
  refine ⟨156632735846821759490996909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104421823897881172993997939 156632735846821759490996909)
  ·
    refine ⟨58737275942558159809123841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156632735846821759490996909 58737275942558159809123841)
    ·
      refine ⟨44052956956918619856842881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58737275942558159809123841 44052956956918619856842881)
      ·
        refine ⟨33039717717688964892632161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44052956956918619856842881 33039717717688964892632161)
        ·
          refine ⟨24779788288266723669474121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33039717717688964892632161 24779788288266723669474121)
          ·
            refine ⟨18584841216200042752105591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24779788288266723669474121 18584841216200042752105591)
            ·
              refine ⟨27877261824300064128158387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18584841216200042752105591 27877261824300064128158387)
              ·
                refine ⟨41815892736450096192237581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27877261824300064128158387 41815892736450096192237581)
                ·
                  refine ⟨15680959776168786072089093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41815892736450096192237581 15680959776168786072089093)
                  ·
                    refine ⟨2940179958031647388516705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15680959776168786072089093 2940179958031647388516705)
                    ·
                      refine ⟨2205134968523735541387529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940179958031647388516705 2205134968523735541387529)
                      ·
                        rfl

theorem cell23_4294485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4294485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294485 prefixEnd_4294485 := by exact prefixLift 4294485
  have htrace : WordTrace (prefixWord ++ tailWord_4294485) baseStart_4294485 baseEnd_4294485 := by
    simpa [prefixWord, tailWord_4294485, baseEnd_4294485] using wordTrace_append hprefix tailTrace_4294485
  have hstable : (prefixWord ++ tailWord_4294485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294485).length < 2 ^ (prefixWord ++ tailWord_4294485).sum := by decide
  have hdescent : baseEnd_4294485 < baseStart_4294485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294511 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_4294511 : Nat := 118140960795 + 4294511 * 2 ^ 59
def prefixEnd_4294511 : Nat := 4983230072969 + 3 ^ 40 * 4294511 * 2
def baseEnd_4294511 : Nat := 2205148319020752439662409

theorem tailTrace_4294511 : CollatzResearch.WordTrace tailWord_4294511 prefixEnd_4294511 2205148319020752439662409 := by
  unfold tailWord_4294511
  simp only [CollatzResearch.WordTrace]
  refine ⟨156633684144727565931443387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104422456096485043954295591 156633684144727565931443387)
  ·
    refine ⟨234950526217091348897165081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156633684144727565931443387 234950526217091348897165081)
    ·
      refine ⟨176212894662818511672873811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234950526217091348897165081 176212894662818511672873811)
      ·
        refine ⟨264319341994227767509310717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176212894662818511672873811 264319341994227767509310717)
        ·
          refine ⟨99119753247835412815991519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264319341994227767509310717 99119753247835412815991519)
          ·
            refine ⟨148679629871753119223987279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99119753247835412815991519 148679629871753119223987279)
            ·
              refine ⟨223019444807629678835980919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148679629871753119223987279 223019444807629678835980919)
              ·
                refine ⟨334529167211444518253971379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223019444807629678835980919 334529167211444518253971379)
                ·
                  refine ⟨501793750817166777380957069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334529167211444518253971379 501793750817166777380957069)
                  ·
                    refine ⟨188172656556437541517858901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501793750817166777380957069 188172656556437541517858901)
                    ·
                      refine ⟨2205148319020752439662409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 188172656556437541517858901 2205148319020752439662409)
                      ·
                        rfl

theorem cell23_4294511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_4294511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294511 prefixEnd_4294511 := by exact prefixLift 4294511
  have htrace : WordTrace (prefixWord ++ tailWord_4294511) baseStart_4294511 baseEnd_4294511 := by
    simpa [prefixWord, tailWord_4294511, baseEnd_4294511] using wordTrace_append hprefix tailTrace_4294511
  have hstable : (prefixWord ++ tailWord_4294511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294511).length < 2 ^ (prefixWord ++ tailWord_4294511).sum := by decide
  have hdescent : baseEnd_4294511 < baseStart_4294511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294575 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 4, 2]
def baseStart_4294575 : Nat := 118140960795 + 4294575 * 2 ^ 59
def prefixEnd_4294575 : Nat := 4983230072969 + 3 ^ 40 * 4294575 * 2
def baseEnd_4294575 : Nat := 2205181181782640189262115

theorem tailTrace_4294575 : CollatzResearch.WordTrace tailWord_4294575 prefixEnd_4294575 2205181181782640189262115 := by
  unfold tailWord_4294575
  simp only [CollatzResearch.WordTrace]
  refine ⟨156636018416495704861773179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104424012277663803241182119 156636018416495704861773179)
  ·
    refine ⟨234954027624743557292659769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156636018416495704861773179 234954027624743557292659769)
    ·
      refine ⟨176215520718557667969494827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234954027624743557292659769 176215520718557667969494827)
      ·
        refine ⟨264323281077836501954242241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176215520718557667969494827 264323281077836501954242241)
        ·
          refine ⟨198242460808377376465681681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264323281077836501954242241 198242460808377376465681681)
          ·
            refine ⟨148681845606283032349261261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198242460808377376465681681 148681845606283032349261261)
            ·
              refine ⟨55755692102356137130972973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148681845606283032349261261 55755692102356137130972973)
              ·
                refine ⟨20908384538383551424114865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55755692102356137130972973 20908384538383551424114865)
                ·
                  refine ⟨15681288403787663568086149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20908384538383551424114865 15681288403787663568086149)
                  ·
                    refine ⟨2940241575710186919016153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15681288403787663568086149 2940241575710186919016153)
                    ·
                      refine ⟨2205181181782640189262115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2940241575710186919016153 2205181181782640189262115)
                      ·
                        rfl

theorem cell23_4294575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4, 2].length) (baseStart_4294575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294575 prefixEnd_4294575 := by exact prefixLift 4294575
  have htrace : WordTrace (prefixWord ++ tailWord_4294575) baseStart_4294575 baseEnd_4294575 := by
    simpa [prefixWord, tailWord_4294575, baseEnd_4294575] using wordTrace_append hprefix tailTrace_4294575
  have hstable : (prefixWord ++ tailWord_4294575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294575).length < 2 ^ (prefixWord ++ tailWord_4294575).sum := by decide
  have hdescent : baseEnd_4294575 < baseStart_4294575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294585 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_4294585 : Nat := 118140960795 + 4294585 * 2 ^ 59
def prefixEnd_4294585 : Nat := 4983230072969 + 3 ^ 40 * 4294585 * 2
def baseEnd_4294585 : Nat := 735062105529728383379023

theorem tailTrace_4294585 : CollatzResearch.WordTrace tailWord_4294585 prefixEnd_4294585 735062105529728383379023 := by
  unfold tailWord_4294585
  simp only [CollatzResearch.WordTrace]
  refine ⟨156636383146459476569637209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104424255430972984379758139 156636383146459476569637209)
  ·
    refine ⟨117477287359844607427227907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156636383146459476569637209 117477287359844607427227907)
    ·
      refine ⟨176215931039766911140841861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117477287359844607427227907 176215931039766911140841861)
      ·
        refine ⟨33040487069956295838907849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176215931039766911140841861 33040487069956295838907849)
        ·
          refine ⟨24780365302467221879180887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33040487069956295838907849 24780365302467221879180887)
          ·
            refine ⟨37170547953700832818771331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24780365302467221879180887 37170547953700832818771331)
            ·
              refine ⟨55755821930551249228156997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37170547953700832818771331 55755821930551249228156997)
              ·
                refine ⟨10454216611978359230279437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55755821930551249228156997 10454216611978359230279437)
                ·
                  refine ⟨3920331229491884711354789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10454216611978359230279437 3920331229491884711354789)
                  ·
                    refine ⟨735062105529728383379023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920331229491884711354789 735062105529728383379023)
                    ·
                      rfl

theorem cell23_4294585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_4294585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4294585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4294585 prefixEnd_4294585 := by exact prefixLift 4294585
  have htrace : WordTrace (prefixWord ++ tailWord_4294585) baseStart_4294585 baseEnd_4294585 := by
    simpa [prefixWord, tailWord_4294585, baseEnd_4294585] using wordTrace_append hprefix tailTrace_4294585
  have hstable : (prefixWord ++ tailWord_4294585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294585).length < 2 ^ (prefixWord ++ tailWord_4294585).sum := by decide
  have hdescent : baseEnd_4294585 < baseStart_4294585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
