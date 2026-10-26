import V185TrunkScan23Chunk0671

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3972948 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3972948 : Nat := 118140960795 + 3972948 * 2 ^ 59
def prefixEnd_3972948 : Nat := 4983230072969 + 3 ^ 40 * 3972948 * 2
def baseEnd_3972948 : Nat := 2040031939319027056378751

theorem tailTrace_3972948 : CollatzResearch.WordTrace tailWord_3972948 prefixEnd_3972948 2040031939319027056378751 := by
  unfold tailWord_3972948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72452659005347698171667749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96603545340463597562223665 72452659005347698171667749)
  ·
    refine ⟨13584873563502693407187703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72452659005347698171667749 13584873563502693407187703)
    ·
      refine ⟨20377310345254040110781555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13584873563502693407187703 20377310345254040110781555)
      ·
        refine ⟨30565965517881060166172333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20377310345254040110781555 30565965517881060166172333)
        ·
          refine ⟨11462237069205397562314625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30565965517881060166172333 11462237069205397562314625)
          ·
            refine ⟨8596677801904048171735969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462237069205397562314625 8596677801904048171735969)
            ·
              refine ⟨6447508351428036128801977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596677801904048171735969 6447508351428036128801977)
              ·
                refine ⟨4835631263571027096601483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447508351428036128801977 4835631263571027096601483)
                ·
                  refine ⟨7253446895356540644902225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835631263571027096601483 7253446895356540644902225)
                  ·
                    refine ⟨5440085171517405483676669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7253446895356540644902225 5440085171517405483676669)
                    ·
                      refine ⟨2040031939319027056378751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440085171517405483676669 2040031939319027056378751)
                      ·
                        rfl

theorem cell23_3972948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3972948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972948 prefixEnd_3972948 := by exact prefixLift 3972948
  have htrace : WordTrace (prefixWord ++ tailWord_3972948) baseStart_3972948 baseEnd_3972948 := by
    simpa [prefixWord, tailWord_3972948, baseEnd_3972948] using wordTrace_append hprefix tailTrace_3972948
  have hstable : (prefixWord ++ tailWord_3972948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972948).length < 2 ^ (prefixWord ++ tailWord_3972948).sum := by decide
  have hdescent : baseEnd_3972948 < baseStart_3972948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972951 : List Nat := [1, 1, 3, 2, 5, 2, 2, 7]
def baseStart_3972951 : Nat := 118140960795 + 3972951 * 2 ^ 59
def prefixEnd_3972951 : Nat := 4983230072969 + 3 ^ 40 * 3972951 * 2
def baseEnd_3972951 : Nat := 75556795546703353505231

theorem tailTrace_3972951 : CollatzResearch.WordTrace tailWord_3972951 prefixEnd_3972951 75556795546703353505231 := by
  unfold tailWord_3972951
  simp only [CollatzResearch.WordTrace]
  refine ⟨144905427429684527855694707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96603618286456351903796471 144905427429684527855694707)
  ·
    refine ⟨217358141144526791783542061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144905427429684527855694707 217358141144526791783542061)
    ·
      refine ⟨81509302929197546918828273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217358141144526791783542061 81509302929197546918828273)
      ·
        refine ⟨61131977196898160189121205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81509302929197546918828273 61131977196898160189121205)
        ·
          refine ⟨5731122862209202517730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61131977196898160189121205 5731122862209202517730113)
          ·
            refine ⟨4298342146656901888297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731122862209202517730113 4298342146656901888297585)
            ·
              refine ⟨3223756609992676416223189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298342146656901888297585 3223756609992676416223189)
              ·
                refine ⟨75556795546703353505231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3223756609992676416223189 75556795546703353505231)
                ·
                  rfl

theorem cell23_3972951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 7].length) (baseStart_3972951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972951 prefixEnd_3972951 := by exact prefixLift 3972951
  have htrace : WordTrace (prefixWord ++ tailWord_3972951) baseStart_3972951 baseEnd_3972951 := by
    simpa [prefixWord, tailWord_3972951, baseEnd_3972951] using wordTrace_append hprefix tailTrace_3972951
  have hstable : (prefixWord ++ tailWord_3972951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972951).length < 2 ^ (prefixWord ++ tailWord_3972951).sum := by decide
  have hdescent : baseEnd_3972951 < baseStart_3972951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972962 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3972962 : Nat := 118140960795 + 3972962 * 2 ^ 59
def prefixEnd_3972962 : Nat := 4983230072969 + 3 ^ 40 * 3972962 * 2
def baseEnd_3972962 : Nat := 2040039128048190001603687

theorem tailTrace_3972962 : CollatzResearch.WordTrace tailWord_3972962 prefixEnd_3972962 2040039128048190001603687 := by
  unfold tailWord_3972962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36226457158161169183586285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96603885755096451156230093 36226457158161169183586285)
  ·
    refine ⟨13584921434310438443844857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36226457158161169183586285 13584921434310438443844857)
    ·
      refine ⟨10188691075732828832883643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13584921434310438443844857 10188691075732828832883643)
      ·
        refine ⟨15283036613599243249325465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188691075732828832883643 15283036613599243249325465)
        ·
          refine ⟨11462277460199432436994099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15283036613599243249325465 11462277460199432436994099)
          ·
            refine ⟨17193416190299148655491149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462277460199432436994099 17193416190299148655491149)
            ·
              refine ⟨6447531071362180745809181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17193416190299148655491149 6447531071362180745809181)
              ·
                refine ⟨2417824151760817779678443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6447531071362180745809181 2417824151760817779678443)
                ·
                  refine ⟨3626736227641226669517665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417824151760817779678443 3626736227641226669517665)
                  ·
                    refine ⟨2720052170730920002138249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626736227641226669517665 2720052170730920002138249)
                    ·
                      refine ⟨2040039128048190001603687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720052170730920002138249 2040039128048190001603687)
                      ·
                        rfl

theorem cell23_3972962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3972962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972962 prefixEnd_3972962 := by exact prefixLift 3972962
  have htrace : WordTrace (prefixWord ++ tailWord_3972962) baseStart_3972962 baseEnd_3972962 := by
    simpa [prefixWord, tailWord_3972962, baseEnd_3972962] using wordTrace_append hprefix tailTrace_3972962
  have hstable : (prefixWord ++ tailWord_3972962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972962).length < 2 ^ (prefixWord ++ tailWord_3972962).sum := by decide
  have hdescent : baseEnd_3972962 < baseStart_3972962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972987 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_3972987 : Nat := 118140960795 + 3972987 * 2 ^ 59
def prefixEnd_3972987 : Nat := 4983230072969 + 3 ^ 40 * 3972987 * 2
def baseEnd_3972987 : Nat := 2040051965064552403791071

theorem tailTrace_3972987 : CollatzResearch.WordTrace tailWord_3972987 prefixEnd_3972987 2040051965064552403791071 := by
  unfold tailWord_3972987
  simp only [CollatzResearch.WordTrace]
  refine ⟨144906740457554106004005215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96604493638369404002670143 144906740457554106004005215)
  ·
    refine ⟨217360110686331159006007823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144906740457554106004005215 217360110686331159006007823)
    ·
      refine ⟨326040166029496738509011735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217360110686331159006007823 326040166029496738509011735)
      ·
        refine ⟨489060249044245107763517603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326040166029496738509011735 489060249044245107763517603)
        ·
          refine ⟨733590373566367661645276405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489060249044245107763517603 733590373566367661645276405)
          ·
            refine ⟨68774097521846968279244663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 733590373566367661645276405 68774097521846968279244663)
            ·
              refine ⟨103161146282770452418866995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68774097521846968279244663 103161146282770452418866995)
              ·
                refine ⟨154741719424155678628300493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103161146282770452418866995 154741719424155678628300493)
                ·
                  refine ⟨58028144784058379485612685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154741719424155678628300493 58028144784058379485612685)
                  ·
                    refine ⟨21760554294021892307104757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58028144784058379485612685 21760554294021892307104757)
                    ·
                      refine ⟨2040051965064552403791071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21760554294021892307104757 2040051965064552403791071)
                      ·
                        rfl

theorem cell23_3972987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_3972987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972987 prefixEnd_3972987 := by exact prefixLift 3972987
  have htrace : WordTrace (prefixWord ++ tailWord_3972987) baseStart_3972987 baseEnd_3972987 := by
    simpa [prefixWord, tailWord_3972987, baseEnd_3972987] using wordTrace_append hprefix tailTrace_3972987
  have hstable : (prefixWord ++ tailWord_3972987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972987).length < 2 ^ (prefixWord ++ tailWord_3972987).sum := by decide
  have hdescent : baseEnd_3972987 < baseStart_3972987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972995 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 2, 1, 3]
def baseStart_3972995 : Nat := 118140960795 + 3972995 * 2 ^ 59
def prefixEnd_3972995 : Nat := 4983230072969 + 3 ^ 40 * 3972995 * 2
def baseEnd_3972995 : Nat := 2040056072909788372491035

theorem tailTrace_3972995 : CollatzResearch.WordTrace tailWord_3972995 prefixEnd_3972995 2040056072909788372491035 := by
  unfold tailWord_3972995
  simp only [CollatzResearch.WordTrace]
  refine ⟨144907032241525123370296439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96604688161016748913530959 144907032241525123370296439)
  ·
    refine ⟨217360548362287685055444659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144907032241525123370296439 217360548362287685055444659)
    ·
      refine ⟨326040822543431527583166989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217360548362287685055444659 326040822543431527583166989)
      ·
        refine ⟨122265308453786822843687621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326040822543431527583166989 122265308453786822843687621)
        ·
          refine ⟨22924745335085029283191429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122265308453786822843687621 22924745335085029283191429)
          ·
            refine ⟨4298389750328442990598393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22924745335085029283191429 4298389750328442990598393)
            ·
              refine ⟨3223792312746332242948795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298389750328442990598393 3223792312746332242948795)
              ·
                refine ⟨4835688469119498364423193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223792312746332242948795 4835688469119498364423193)
                ·
                  refine ⟨3626766351839623773317395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835688469119498364423193 3626766351839623773317395)
                  ·
                    refine ⟨5440149527759435659976093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626766351839623773317395 5440149527759435659976093)
                    ·
                      refine ⟨2040056072909788372491035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440149527759435659976093 2040056072909788372491035)
                      ·
                        rfl

theorem cell23_3972995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_3972995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972995 prefixEnd_3972995 := by exact prefixLift 3972995
  have htrace : WordTrace (prefixWord ++ tailWord_3972995) baseStart_3972995 baseEnd_3972995 := by
    simpa [prefixWord, tailWord_3972995, baseEnd_3972995] using wordTrace_append hprefix tailTrace_3972995
  have hstable : (prefixWord ++ tailWord_3972995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972995).length < 2 ^ (prefixWord ++ tailWord_3972995).sum := by decide
  have hdescent : baseEnd_3972995 < baseStart_3972995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973001 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 4, 2]
def baseStart_3973001 : Nat := 118140960795 + 3973001 * 2 ^ 59
def prefixEnd_3973001 : Nat := 4983230072969 + 3 ^ 40 * 3973001 * 2
def baseEnd_3973001 : Nat := 2040059153793715349016007

theorem tailTrace_3973001 : CollatzResearch.WordTrace tailWord_3973001 prefixEnd_3973001 2040059153793715349016007 := by
  unfold tailWord_3973001
  simp only [CollatzResearch.WordTrace]
  refine ⟨144907251079503386395014857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96604834053002257596676571 144907251079503386395014857)
  ·
    refine ⟨108680438309627539796261143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144907251079503386395014857 108680438309627539796261143)
    ·
      refine ⟨163020657464441309694391715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108680438309627539796261143 163020657464441309694391715)
      ·
        refine ⟨244530986196661964541587573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163020657464441309694391715 244530986196661964541587573)
        ·
          refine ⟨22924779955937059175773835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244530986196661964541587573 22924779955937059175773835)
          ·
            refine ⟨34387169933905588763660753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22924779955937059175773835 34387169933905588763660753)
            ·
              refine ⟨25790377450429191572745565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34387169933905588763660753 25790377450429191572745565)
              ·
                refine ⟨9671391543910946839779587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25790377450429191572745565 9671391543910946839779587)
                ·
                  refine ⟨14507087315866420259669381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671391543910946839779587 14507087315866420259669381)
                  ·
                    refine ⟨2720078871724953798688009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14507087315866420259669381 2720078871724953798688009)
                    ·
                      refine ⟨2040059153793715349016007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720078871724953798688009 2040059153793715349016007)
                      ·
                        rfl

theorem cell23_3973001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4, 2].length) (baseStart_3973001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973001 prefixEnd_3973001 := by exact prefixLift 3973001
  have htrace : WordTrace (prefixWord ++ tailWord_3973001) baseStart_3973001 baseEnd_3973001 := by
    simpa [prefixWord, tailWord_3973001, baseEnd_3973001] using wordTrace_append hprefix tailTrace_3973001
  have hstable : (prefixWord ++ tailWord_3973001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973001).length < 2 ^ (prefixWord ++ tailWord_3973001).sum := by decide
  have hdescent : baseEnd_3973001 < baseStart_3973001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973018 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_3973018 : Nat := 118140960795 + 3973018 * 2 ^ 59
def prefixEnd_3973018 : Nat := 4983230072969 + 3 ^ 40 * 3973018 * 2
def baseEnd_3973018 : Nat := 2040067882964841782503429

theorem tailTrace_3973018 : CollatzResearch.WordTrace tailWord_3973018 prefixEnd_3973018 2040067882964841782503429 := by
  unfold tailWord_3973018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36226967780110449574595927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96605247413627865532255805 36226967780110449574595927)
  ·
    refine ⟨54340451670165674361893891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36226967780110449574595927 54340451670165674361893891)
    ·
      refine ⟨81510677505248511542840837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54340451670165674361893891 81510677505248511542840837)
      ·
        refine ⟨15283252032234095914282657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81510677505248511542840837 15283252032234095914282657)
        ·
          refine ⟨11462439024175571935711993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15283252032234095914282657 11462439024175571935711993)
          ·
            refine ⟨8596829268131678951783995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462439024175571935711993 8596829268131678951783995)
            ·
              refine ⟨12895243902197518427675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596829268131678951783995 12895243902197518427675993)
              ·
                refine ⟨9671432926648138820756995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12895243902197518427675993 9671432926648138820756995)
                ·
                  refine ⟨14507149389972208231135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671432926648138820756995 14507149389972208231135493)
                  ·
                    refine ⟨2720090510619789043337905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14507149389972208231135493 2720090510619789043337905)
                    ·
                      refine ⟨2040067882964841782503429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720090510619789043337905 2040067882964841782503429)
                      ·
                        rfl

theorem cell23_3973018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_3973018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973018 prefixEnd_3973018 := by exact prefixLift 3973018
  have htrace : WordTrace (prefixWord ++ tailWord_3973018) baseStart_3973018 baseEnd_3973018 := by
    simpa [prefixWord, tailWord_3973018, baseEnd_3973018] using wordTrace_append hprefix tailTrace_3973018
  have hstable : (prefixWord ++ tailWord_3973018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973018).length < 2 ^ (prefixWord ++ tailWord_3973018).sum := by decide
  have hdescent : baseEnd_3973018 < baseStart_3973018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973126 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3973126 : Nat := 118140960795 + 3973126 * 2 ^ 59
def prefixEnd_3973126 : Nat := 4983230072969 + 3 ^ 40 * 3973126 * 2
def baseEnd_3973126 : Nat := 226680370986169706661437

theorem tailTrace_3973126 : CollatzResearch.WordTrace tailWord_3973126 prefixEnd_3973126 226680370986169706661437 := by
  unfold tailWord_3973126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528494068876579148228601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96607873469367021828876821 4528494068876579148228601)
  ·
    refine ⟨3396370551657434361171451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4528494068876579148228601 3396370551657434361171451)
    ·
      refine ⟨5094555827486151541757177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396370551657434361171451 5094555827486151541757177)
      ·
        refine ⟨3820916870614613656317883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094555827486151541757177 3820916870614613656317883)
        ·
          refine ⟨5731375305921920484476825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820916870614613656317883 5731375305921920484476825)
          ·
            refine ⟨4298531479441440363357619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731375305921920484476825 4298531479441440363357619)
            ·
              refine ⟨6447797219162160545036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298531479441440363357619 6447797219162160545036429)
              ·
                refine ⟨2417923957185810204388661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6447797219162160545036429 2417923957185810204388661)
                ·
                  refine ⟨226680370986169706661437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417923957185810204388661 226680370986169706661437)
                  ·
                    rfl

theorem cell23_3973126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3973126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973126 prefixEnd_3973126 := by exact prefixLift 3973126
  have htrace : WordTrace (prefixWord ++ tailWord_3973126) baseStart_3973126 baseEnd_3973126 := by
    simpa [prefixWord, tailWord_3973126, baseEnd_3973126] using wordTrace_append hprefix tailTrace_3973126
  have hstable : (prefixWord ++ tailWord_3973126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973126).length < 2 ^ (prefixWord ++ tailWord_3973126).sum := by decide
  have hdescent : baseEnd_3973126 < baseStart_3973126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973185 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3973185 : Nat := 118140960795 + 3973185 * 2 ^ 59
def prefixEnd_3973185 : Nat := 4983230072969 + 3 ^ 40 * 3973185 * 2
def baseEnd_3973185 : Nat := 2040153634234142629115161

theorem tailTrace_3973185 : CollatzResearch.WordTrace tailWord_3973185 prefixEnd_3973185 2040153634234142629115161 := by
  unfold tailWord_3973185
  simp only [CollatzResearch.WordTrace]
  refine ⟨144913962110836785819713009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96609308073891190546475339 144913962110836785819713009)
  ·
    refine ⟨108685471583127589364784757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144913962110836785819713009 108685471583127589364784757)
    ·
      refine ⟨10189262960918211502948571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108685471583127589364784757 10189262960918211502948571)
      ·
        refine ⟨15283894441377317254422857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189262960918211502948571 15283894441377317254422857)
        ·
          refine ⟨11462920831032987940817143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15283894441377317254422857 11462920831032987940817143)
          ·
            refine ⟨17194381246549481911225715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462920831032987940817143 17194381246549481911225715)
            ·
              refine ⟨25791571869824222866838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17194381246549481911225715 25791571869824222866838573)
              ·
                refine ⟨9671839451184083575064465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25791571869824222866838573 9671839451184083575064465)
                ·
                  refine ⟨7253879588388062681298349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9671839451184083575064465 7253879588388062681298349)
                  ·
                    refine ⟨2720204845645523505486881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7253879588388062681298349 2720204845645523505486881)
                    ·
                      refine ⟨2040153634234142629115161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720204845645523505486881 2040153634234142629115161)
                      ·
                        rfl

theorem cell23_3973185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3973185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973185 prefixEnd_3973185 := by exact prefixLift 3973185
  have htrace : WordTrace (prefixWord ++ tailWord_3973185) baseStart_3973185 baseEnd_3973185 := by
    simpa [prefixWord, tailWord_3973185, baseEnd_3973185] using wordTrace_append hprefix tailTrace_3973185
  have hstable : (prefixWord ++ tailWord_3973185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973185).length < 2 ^ (prefixWord ++ tailWord_3973185).sum := by decide
  have hdescent : baseEnd_3973185 < baseStart_3973185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973191 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 6]
def baseStart_3973191 : Nat := 118140960795 + 3973191 * 2 ^ 59
def prefixEnd_3973191 : Nat := 4983230072969 + 3 ^ 40 * 3973191 * 2
def baseEnd_3973191 : Nat := 680052238372689868546711

theorem tailTrace_3973191 : CollatzResearch.WordTrace tailWord_3973191 prefixEnd_3973191 680052238372689868546711 := by
  unfold tailWord_3973191
  simp only [CollatzResearch.WordTrace]
  refine ⟨144914180948815048844431427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96609453965876699229620951 144914180948815048844431427)
  ·
    refine ⟨217371271423222573266647141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144914180948815048844431427 217371271423222573266647141)
    ·
      refine ⟨40757113391854232487496339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217371271423222573266647141 40757113391854232487496339)
      ·
        refine ⟨61135670087781348731244509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40757113391854232487496339 61135670087781348731244509)
        ·
          refine ⟨22925876282918005774216691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61135670087781348731244509 22925876282918005774216691)
          ·
            refine ⟨34388814424377008661325037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22925876282918005774216691 34388814424377008661325037)
            ·
              refine ⟨12895805409141378247996889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34388814424377008661325037 12895805409141378247996889)
              ·
                refine ⟨9671854056856033685997667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12895805409141378247996889 9671854056856033685997667)
                ·
                  refine ⟨14507781085284050528996501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671854056856033685997667 14507781085284050528996501)
                  ·
                    refine ⟨680052238372689868546711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14507781085284050528996501 680052238372689868546711)
                    ·
                      rfl

theorem cell23_3973191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_3973191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973191 prefixEnd_3973191 := by exact prefixLift 3973191
  have htrace : WordTrace (prefixWord ++ tailWord_3973191) baseStart_3973191 baseEnd_3973191 := by
    simpa [prefixWord, tailWord_3973191, baseEnd_3973191] using wordTrace_append hprefix tailTrace_3973191
  have hstable : (prefixWord ++ tailWord_3973191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973191).length < 2 ^ (prefixWord ++ tailWord_3973191).sum := by decide
  have hdescent : baseEnd_3973191 < baseStart_3973191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973208 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_3973208 : Nat := 118140960795 + 3973208 * 2 ^ 59
def prefixEnd_3973208 : Nat := 4983230072969 + 3 ^ 40 * 3973208 * 2
def baseEnd_3973208 : Nat := 680055148096398679709185

theorem tailTrace_3973208 : CollatzResearch.WordTrace tailWord_3973208 prefixEnd_3973208 680055148096398679709185 := by
  unfold tailWord_3973208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72457400494876730373900139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96609867326502307165200185 72457400494876730373900139)
  ·
    refine ⟨108686100742315095560850209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72457400494876730373900139 108686100742315095560850209)
    ·
      refine ⟨81514575556736321670637657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108686100742315095560850209 81514575556736321670637657)
      ·
        refine ⟨61135931667552241252978243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81514575556736321670637657 61135931667552241252978243)
        ·
          refine ⟨91703897501328361879467365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61135931667552241252978243 91703897501328361879467365)
          ·
            refine ⟨17194480781499067852400131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91703897501328361879467365 17194480781499067852400131)
            ·
              refine ⟨25791721172248601778600197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17194480781499067852400131 25791721172248601778600197)
              ·
                refine ⟨4835947719796612833487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25791721172248601778600197 4835947719796612833487537)
                ·
                  refine ⟨3626960789847459625115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835947719796612833487537 3626960789847459625115653)
                  ·
                    refine ⟨680055148096398679709185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3626960789847459625115653 680055148096398679709185)
                    ·
                      rfl

theorem cell23_3973208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_3973208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973208 prefixEnd_3973208 := by exact prefixLift 3973208
  have htrace : WordTrace (prefixWord ++ tailWord_3973208) baseStart_3973208 baseEnd_3973208 := by
    simpa [prefixWord, tailWord_3973208, baseEnd_3973208] using wordTrace_append hprefix tailTrace_3973208
  have hstable : (prefixWord ++ tailWord_3973208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973208).length < 2 ^ (prefixWord ++ tailWord_3973208).sum := by decide
  have hdescent : baseEnd_3973208 < baseStart_3973208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973221 : List Nat := [1, 3, 1, 3, 2, 2, 3, 8]
def baseStart_3973221 : Nat := 118140960795 + 3973221 * 2 ^ 59
def prefixEnd_3973221 : Nat := 4983230072969 + 3 ^ 40 * 3973221 * 2
def baseEnd_3973221 : Nat := 75561930353248314380185

theorem tailTrace_3973221 : CollatzResearch.WordTrace tailWord_3973221 prefixEnd_3973221 75561930353248314380185 := by
  unfold tailWord_3973221
  simp only [CollatzResearch.WordTrace]
  refine ⟨144915275138706363968023517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96610183425804242645349011 144915275138706363968023517)
  ·
    refine ⟨54343228177014886488008819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144915275138706363968023517 54343228177014886488008819)
    ·
      refine ⟨81514842265522329732013229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54343228177014886488008819 81514842265522329732013229)
      ·
        refine ⟨30568065849570873649504961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81514842265522329732013229 30568065849570873649504961)
        ·
          refine ⟨22926049387178155237128721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30568065849570873649504961 22926049387178155237128721)
          ·
            refine ⟨17194537040383616427846541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22926049387178155237128721 17194537040383616427846541)
            ·
              refine ⟨6447951390143856160442453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17194537040383616427846541 6447951390143856160442453)
              ·
                refine ⟨75561930353248314380185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6447951390143856160442453 75561930353248314380185)
                ·
                  rfl

theorem cell23_3973221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 8].length) (baseStart_3973221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973221 prefixEnd_3973221 := by exact prefixLift 3973221
  have htrace : WordTrace (prefixWord ++ tailWord_3973221) baseStart_3973221 baseEnd_3973221 := by
    simpa [prefixWord, tailWord_3973221, baseEnd_3973221] using wordTrace_append hprefix tailTrace_3973221
  have hstable : (prefixWord ++ tailWord_3973221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973221).length < 2 ^ (prefixWord ++ tailWord_3973221).sum := by decide
  have hdescent : baseEnd_3973221 < baseStart_3973221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973228 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_3973228 : Nat := 118140960795 + 3973228 * 2 ^ 59
def prefixEnd_3973228 : Nat := 4983230072969 + 3 ^ 40 * 3973228 * 2
def baseEnd_3973228 : Nat := 2040175713902285960877463

theorem tailTrace_3973228 : CollatzResearch.WordTrace tailWord_3973228 prefixEnd_3973228 2040175713902285960877463 := by
  unfold tailWord_3973228
  simp only [CollatzResearch.WordTrace]
  refine ⟨72457765224840502081764169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96610353633120669442352225 72457765224840502081764169)
  ·
    refine ⟨54343323918630376561323127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72457765224840502081764169 54343323918630376561323127)
    ·
      refine ⟨81514985877945564841984691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54343323918630376561323127 81514985877945564841984691)
      ·
        refine ⟨122272478816918347262977037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81514985877945564841984691 122272478816918347262977037)
        ·
          refine ⟨45852179556344380223616389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122272478816918347262977037 45852179556344380223616389)
          ·
            refine ⟨8597283666814571291928073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45852179556344380223616389 8597283666814571291928073)
            ·
              refine ⟨6447962750110928468946055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597283666814571291928073 6447962750110928468946055)
              ·
                refine ⟨9671944125166392703419083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447962750110928468946055 9671944125166392703419083)
                ·
                  refine ⟨14507916187749589055128625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671944125166392703419083 14507916187749589055128625)
                  ·
                    refine ⟨10880937140812191791346469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14507916187749589055128625 10880937140812191791346469)
                    ·
                      refine ⟨2040175713902285960877463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10880937140812191791346469 2040175713902285960877463)
                      ·
                        rfl

theorem cell23_3973228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_3973228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973228 prefixEnd_3973228 := by exact prefixLift 3973228
  have htrace : WordTrace (prefixWord ++ tailWord_3973228) baseStart_3973228 baseEnd_3973228 := by
    simpa [prefixWord, tailWord_3973228, baseEnd_3973228] using wordTrace_append hprefix tailTrace_3973228
  have hstable : (prefixWord ++ tailWord_3973228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973228).length < 2 ^ (prefixWord ++ tailWord_3973228).sum := by decide
  have hdescent : baseEnd_3973228 < baseStart_3973228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973248 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_3973248 : Nat := 118140960795 + 3973248 * 2 ^ 59
def prefixEnd_3973248 : Nat := 4983230072969 + 3 ^ 40 * 3973248 * 2
def baseEnd_3973248 : Nat := 2040185983515375882627371

theorem tailTrace_3973248 : CollatzResearch.WordTrace tailWord_3973248 prefixEnd_3973248 2040185983515375882627371 := by
  unfold tailWord_3973248
  simp only [CollatzResearch.WordTrace]
  refine ⟨72458129954804273789628199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96610839939739031719504265 72458129954804273789628199)
  ·
    refine ⟨108687194932206410684442299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72458129954804273789628199 108687194932206410684442299)
    ·
      refine ⟨163030792398309616026663449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108687194932206410684442299 163030792398309616026663449)
      ·
        refine ⟨122273094298732212019997587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163030792398309616026663449 122273094298732212019997587)
        ·
          refine ⟨183409641448098318029996381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122273094298732212019997587 183409641448098318029996381)
          ·
            refine ⟨68778615543036869261248643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183409641448098318029996381 68778615543036869261248643)
            ·
              refine ⟨103167923314555303891872965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68778615543036869261248643 103167923314555303891872965)
              ·
                refine ⟨19343985621479119479726181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103167923314555303891872965 19343985621479119479726181)
                ·
                  refine ⟨3626997304027334902448659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19343985621479119479726181 3626997304027334902448659)
                  ·
                    refine ⟨5440495956041002353672989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626997304027334902448659 5440495956041002353672989)
                    ·
                      refine ⟨2040185983515375882627371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440495956041002353672989 2040185983515375882627371)
                      ·
                        rfl

theorem cell23_3973248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_3973248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973248 prefixEnd_3973248 := by exact prefixLift 3973248
  have htrace : WordTrace (prefixWord ++ tailWord_3973248) baseStart_3973248 baseEnd_3973248 := by
    simpa [prefixWord, tailWord_3973248, baseEnd_3973248] using wordTrace_append hprefix tailTrace_3973248
  have hstable : (prefixWord ++ tailWord_3973248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973248).length < 2 ^ (prefixWord ++ tailWord_3973248).sum := by decide
  have hdescent : baseEnd_3973248 < baseStart_3973248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973249 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3973249 : Nat := 118140960795 + 3973249 * 2 ^ 59
def prefixEnd_3973249 : Nat := 4983230072969 + 3 ^ 40 * 3973249 * 2
def baseEnd_3973249 : Nat := 2040186496996030378714867

theorem tailTrace_3973249 : CollatzResearch.WordTrace tailWord_3973249 prefixEnd_3973249 2040186496996030378714867 := by
  unfold tailWord_3973249
  simp only [CollatzResearch.WordTrace]
  refine ⟨144916296382604924750042801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96610864255069949833361867 144916296382604924750042801)
  ·
    refine ⟨108687222286953693562532101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144916296382604924750042801 108687222286953693562532101)
    ·
      refine ⟨20378854178803817542974769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108687222286953693562532101 20378854178803817542974769)
      ·
        refine ⟨15284140634102863157231077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20378854178803817542974769 15284140634102863157231077)
        ·
          refine ⟨2865776368894286841980827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15284140634102863157231077 2865776368894286841980827)
          ·
            refine ⟨4298664553341430262971241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865776368894286841980827 4298664553341430262971241)
            ·
              refine ⟨3223998415006072697228431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298664553341430262971241 3223998415006072697228431)
              ·
                refine ⟨4835997622509109045842647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223998415006072697228431 4835997622509109045842647)
                ·
                  refine ⟨7253996433763663568763971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835997622509109045842647 7253996433763663568763971)
                  ·
                    refine ⟨10880994650645495353145957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7253996433763663568763971 10880994650645495353145957)
                    ·
                      refine ⟨2040186496996030378714867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10880994650645495353145957 2040186496996030378714867)
                      ·
                        rfl

theorem cell23_3973249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3973249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973249 prefixEnd_3973249 := by exact prefixLift 3973249
  have htrace : WordTrace (prefixWord ++ tailWord_3973249) baseStart_3973249 baseEnd_3973249 := by
    simpa [prefixWord, tailWord_3973249, baseEnd_3973249] using wordTrace_append hprefix tailTrace_3973249
  have hstable : (prefixWord ++ tailWord_3973249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973249).length < 2 ^ (prefixWord ++ tailWord_3973249).sum := by decide
  have hdescent : baseEnd_3973249 < baseStart_3973249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973282 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3973282 : Nat := 118140960795 + 3973282 * 2 ^ 59
def prefixEnd_3973282 : Nat := 4983230072969 + 3 ^ 40 * 3973282 * 2
def baseEnd_3973282 : Nat := 2040203441857628749602215

theorem tailTrace_3973282 : CollatzResearch.WordTrace tailWord_3973282 prefixEnd_3973282 2040203441857628749602215 := by
  unfold tailWord_3973282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36229374997871342846498525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96611666660990247590662733 36229374997871342846498525)
  ·
    refine ⟨13586015624201753567436947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36229374997871342846498525 13586015624201753567436947)
    ·
      refine ⟨20379023436302630351155421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13586015624201753567436947 20379023436302630351155421)
      ·
        refine ⟨7642133788613486381683283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20379023436302630351155421 7642133788613486381683283)
        ·
          refine ⟨11463200682920229572524925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642133788613486381683283 11463200682920229572524925)
          ·
            refine ⟨4298700256095086089696847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11463200682920229572524925 4298700256095086089696847)
            ·
              refine ⟨6448050384142629134545271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298700256095086089696847 6448050384142629134545271)
              ·
                refine ⟨9672075576213943701817907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448050384142629134545271 9672075576213943701817907)
                ·
                  refine ⟨14508113364320915552726861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9672075576213943701817907 14508113364320915552726861)
                  ·
                    refine ⟨5440542511620343332272573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14508113364320915552726861 5440542511620343332272573)
                    ·
                      refine ⟨2040203441857628749602215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440542511620343332272573 2040203441857628749602215)
                      ·
                        rfl

theorem cell23_3973282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3973282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973282 prefixEnd_3973282 := by exact prefixLift 3973282
  have htrace : WordTrace (prefixWord ++ tailWord_3973282) baseStart_3973282 baseEnd_3973282 := by
    simpa [prefixWord, tailWord_3973282, baseEnd_3973282] using wordTrace_append hprefix tailTrace_3973282
  have hstable : (prefixWord ++ tailWord_3973282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973282).length < 2 ^ (prefixWord ++ tailWord_3973282).sum := by decide
  have hdescent : baseEnd_3973282 < baseStart_3973282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973291 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3]
def baseStart_3973291 : Nat := 118140960795 + 3973291 * 2 ^ 59
def prefixEnd_3973291 : Nat := 4983230072969 + 3 ^ 40 * 3973291 * 2
def baseEnd_3973291 : Nat := 2040208063183519214389673

theorem tailTrace_3973291 : CollatzResearch.WordTrace tailWord_3973291 prefixEnd_3973291 2040208063183519214389673 := by
  unfold tailWord_3973291
  simp only [CollatzResearch.WordTrace]
  refine ⟨144917828248452765923071727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96611885498968510615381151 144917828248452765923071727)
  ·
    refine ⟨217376742372679148884607591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144917828248452765923071727 217376742372679148884607591)
    ·
      refine ⟨326065113559018723326911387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217376742372679148884607591 326065113559018723326911387)
      ·
        refine ⟨489097670338528084990367081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326065113559018723326911387 489097670338528084990367081)
        ·
          refine ⟨366823252753896063742775311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489097670338528084990367081 366823252753896063742775311)
          ·
            refine ⟨550234879130844095614162967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366823252753896063742775311 550234879130844095614162967)
            ·
              refine ⟨825352318696266143421244451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550234879130844095614162967 825352318696266143421244451)
              ·
                refine ⟨1238028478044399215131866677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825352318696266143421244451 1238028478044399215131866677)
                ·
                  refine ⟨116065169816662426418612501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1238028478044399215131866677 116065169816662426418612501)
                  ·
                    refine ⟨5440554835156051238372461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116065169816662426418612501 5440554835156051238372461)
                    ·
                      refine ⟨2040208063183519214389673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440554835156051238372461 2040208063183519214389673)
                      ·
                        rfl

theorem cell23_3973291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].length) (baseStart_3973291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973291 prefixEnd_3973291 := by exact prefixLift 3973291
  have htrace : WordTrace (prefixWord ++ tailWord_3973291) baseStart_3973291 baseEnd_3973291 := by
    simpa [prefixWord, tailWord_3973291, baseEnd_3973291] using wordTrace_append hprefix tailTrace_3973291
  have hstable : (prefixWord ++ tailWord_3973291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973291).length < 2 ^ (prefixWord ++ tailWord_3973291).sum := by decide
  have hdescent : baseEnd_3973291 < baseStart_3973291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973305 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3973305 : Nat := 118140960795 + 3973305 * 2 ^ 59
def prefixEnd_3973305 : Nat := 4983230072969 + 3 ^ 40 * 3973305 * 2
def baseEnd_3973305 : Nat := 2040215251912682159614609

theorem tailTrace_3973305 : CollatzResearch.WordTrace tailWord_3973305 prefixEnd_3973305 2040215251912682159614609 := by
  unfold tailWord_3973305
  simp only [CollatzResearch.WordTrace]
  refine ⟨144918338870402046314081369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96612225913601364209387579 144918338870402046314081369)
  ·
    refine ⟨108688754152801534735561027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144918338870402046314081369 108688754152801534735561027)
    ·
      refine ⟨163033131229202302103341541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108688754152801534735561027 163033131229202302103341541)
      ·
        refine ⟨30568712105475431644376539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163033131229202302103341541 30568712105475431644376539)
        ·
          refine ⟨45853068158213147466564809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30568712105475431644376539 45853068158213147466564809)
          ·
            refine ⟨34389801118659860599923607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45853068158213147466564809 34389801118659860599923607)
            ·
              refine ⟨51584701677989790899885411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34389801118659860599923607 51584701677989790899885411)
              ·
                refine ⟨77377052516984686349828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51584701677989790899885411 77377052516984686349828117)
                ·
                  refine ⟨3627049336733657172648193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77377052516984686349828117 3627049336733657172648193)
                  ·
                    refine ⟨2720287002550242879486145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627049336733657172648193 2720287002550242879486145)
                    ·
                      refine ⟨2040215251912682159614609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720287002550242879486145 2040215251912682159614609)
                      ·
                        rfl

theorem cell23_3973305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3973305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973305 prefixEnd_3973305 := by exact prefixLift 3973305
  have htrace : WordTrace (prefixWord ++ tailWord_3973305) baseStart_3973305 baseEnd_3973305 := by
    simpa [prefixWord, tailWord_3973305, baseEnd_3973305] using wordTrace_append hprefix tailTrace_3973305
  have hstable : (prefixWord ++ tailWord_3973305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973305).length < 2 ^ (prefixWord ++ tailWord_3973305).sum := by decide
  have hdescent : baseEnd_3973305 < baseStart_3973305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973322 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_3973322 : Nat := 118140960795 + 3973322 * 2 ^ 59
def prefixEnd_3973322 : Nat := 4983230072969 + 3 ^ 40 * 3973322 * 2
def baseEnd_3973322 : Nat := 2040223981083808593102031

theorem tailTrace_3973322 : CollatzResearch.WordTrace tailWord_3973322 prefixEnd_3973322 2040223981083808593102031 := by
  unfold tailWord_3973322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36229739727835114554362555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96612639274226972144966813 36229739727835114554362555)
  ·
    refine ⟨54344609591752671831543833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36229739727835114554362555 54344609591752671831543833)
    ·
      refine ⟨40758457193814503873657875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54344609591752671831543833 40758457193814503873657875)
      ·
        refine ⟨61137685790721755810486813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40758457193814503873657875 61137685790721755810486813)
        ·
          refine ⟨22926632171520658428932555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61137685790721755810486813 22926632171520658428932555)
          ·
            refine ⟨34389948257280987643398833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22926632171520658428932555 34389948257280987643398833)
            ·
              refine ⟨25792461192960740732549125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34389948257280987643398833 25792461192960740732549125)
              ·
                refine ⟨4836086473680138887352961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25792461192960740732549125 4836086473680138887352961)
                ·
                  refine ⟨3627064855260104165514721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836086473680138887352961 3627064855260104165514721)
                  ·
                    refine ⟨2720298641445078124136041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627064855260104165514721 2720298641445078124136041)
                    ·
                      refine ⟨2040223981083808593102031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720298641445078124136041 2040223981083808593102031)
                      ·
                        rfl

theorem cell23_3973322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_3973322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973322 prefixEnd_3973322 := by exact prefixLift 3973322
  have htrace : WordTrace (prefixWord ++ tailWord_3973322) baseStart_3973322 baseEnd_3973322 := by
    simpa [prefixWord, tailWord_3973322, baseEnd_3973322] using wordTrace_append hprefix tailTrace_3973322
  have hstable : (prefixWord ++ tailWord_3973322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973322).length < 2 ^ (prefixWord ++ tailWord_3973322).sum := by decide
  have hdescent : baseEnd_3973322 < baseStart_3973322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973338 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_3973338 : Nat := 118140960795 + 3973338 * 2 ^ 59
def prefixEnd_3973338 : Nat := 4983230072969 + 3 ^ 40 * 3973338 * 2
def baseEnd_3973338 : Nat := 2040232196774280530501957

theorem tailTrace_3973338 : CollatzResearch.WordTrace tailWord_3973338 prefixEnd_3973338 2040232196774280530501957 := by
  unfold tailWord_3973338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36229885619820623237508167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96613028319521661966688445 36229885619820623237508167)
  ·
    refine ⟨54344828429730934856262251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36229885619820623237508167 54344828429730934856262251)
    ·
      refine ⟨81517242644596402284393377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54344828429730934856262251 81517242644596402284393377)
      ·
        refine ⟨61137931983447301713295033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81517242644596402284393377 61137931983447301713295033)
        ·
          refine ⟨45853448987585476284971275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61137931983447301713295033 45853448987585476284971275)
          ·
            refine ⟨68780173481378214427456913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45853448987585476284971275 68780173481378214427456913)
            ·
              refine ⟨51585130111033660820592685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68780173481378214427456913 51585130111033660820592685)
              ·
                refine ⟨19344423791637622807722257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51585130111033660820592685 19344423791637622807722257)
                ·
                  refine ⟨14508317843728217105791693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19344423791637622807722257 14508317843728217105791693)
                  ·
                    refine ⟨5440619191398081414671885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14508317843728217105791693 5440619191398081414671885)
                    ·
                      refine ⟨2040232196774280530501957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440619191398081414671885 2040232196774280530501957)
                      ·
                        rfl

theorem cell23_3973338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_3973338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973338 prefixEnd_3973338 := by exact prefixLift 3973338
  have htrace : WordTrace (prefixWord ++ tailWord_3973338) baseStart_3973338 baseEnd_3973338 := by
    simpa [prefixWord, tailWord_3973338, baseEnd_3973338] using wordTrace_append hprefix tailTrace_3973338
  have hstable : (prefixWord ++ tailWord_3973338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973338).length < 2 ^ (prefixWord ++ tailWord_3973338).sum := by decide
  have hdescent : baseEnd_3973338 < baseStart_3973338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973412 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3973412 : Nat := 118140960795 + 3973412 * 2 ^ 59
def prefixEnd_3973412 : Nat := 4983230072969 + 3 ^ 40 * 3973412 * 2
def baseEnd_3973412 : Nat := 2040270194342713240976617

theorem tailTrace_3973412 : CollatzResearch.WordTrace tailWord_3973412 prefixEnd_3973412 2040270194342713240976617 := by
  unfold tailWord_3973412
  simp only [CollatzResearch.WordTrace]
  refine ⟨72461120740507201794113245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96614827654009602392150993 72461120740507201794113245)
  ·
    refine ⟨27172920277690200672792467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72461120740507201794113245 27172920277690200672792467)
    ·
      refine ⟨40759380416535301009188701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27172920277690200672792467 40759380416535301009188701)
      ·
        refine ⟨15284767656200737878445763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40759380416535301009188701 15284767656200737878445763)
        ·
          refine ⟨22927151484301106817668645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284767656200737878445763 22927151484301106817668645)
          ·
            refine ⟨4298840903306457528312871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22927151484301106817668645 4298840903306457528312871)
            ·
              refine ⟨6448261354959686292469307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298840903306457528312871 6448261354959686292469307)
              ·
                refine ⟨9672392032439529438703961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448261354959686292469307 9672392032439529438703961)
                ·
                  refine ⟨7254294024329647079027971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9672392032439529438703961 7254294024329647079027971)
                  ·
                    refine ⟨10881441036494470618541957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7254294024329647079027971 10881441036494470618541957)
                    ·
                      refine ⟨2040270194342713240976617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10881441036494470618541957 2040270194342713240976617)
                      ·
                        rfl

theorem cell23_3973412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3973412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973412 prefixEnd_3973412 := by exact prefixLift 3973412
  have htrace : WordTrace (prefixWord ++ tailWord_3973412) baseStart_3973412 baseEnd_3973412 := by
    simpa [prefixWord, tailWord_3973412, baseEnd_3973412] using wordTrace_append hprefix tailTrace_3973412
  have hstable : (prefixWord ++ tailWord_3973412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973412).length < 2 ^ (prefixWord ++ tailWord_3973412).sum := by decide
  have hdescent : baseEnd_3973412 < baseStart_3973412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973448 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_3973448 : Nat := 118140960795 + 3973448 * 2 ^ 59
def prefixEnd_3973448 : Nat := 4983230072969 + 3 ^ 40 * 3973448 * 2
def baseEnd_3973448 : Nat := 680096226548758366708817

theorem tailTrace_3973448 : CollatzResearch.WordTrace tailWord_3973448 prefixEnd_3973448 680096226548758366708817 := by
  unfold tailWord_3973448
  simp only [CollatzResearch.WordTrace]
  refine ⟨72461777254441990868268499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96615703005922654491024665 72461777254441990868268499)
  ·
    refine ⟨108692665881662986302402749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72461777254441990868268499 108692665881662986302402749)
    ·
      refine ⟨40759749705623619863401031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108692665881662986302402749 40759749705623619863401031)
      ·
        refine ⟨61139624558435429795101547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40759749705623619863401031 61139624558435429795101547)
        ·
          refine ⟨91709436837653144692652321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61139624558435429795101547 91709436837653144692652321)
          ·
            refine ⟨68782077628239858519489241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91709436837653144692652321 68782077628239858519489241)
            ·
              refine ⟨51586558221179893889616931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68782077628239858519489241 51586558221179893889616931)
              ·
                refine ⟨77379837331769840834425397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51586558221179893889616931 77379837331769840834425397)
                ·
                  refine ⟨7254359749853422578227381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77379837331769840834425397 7254359749853422578227381)
                  ·
                    refine ⟨680096226548758366708817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7254359749853422578227381 680096226548758366708817)
                    ·
                      rfl

theorem cell23_3973448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_3973448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973448 prefixEnd_3973448 := by exact prefixLift 3973448
  have htrace : WordTrace (prefixWord ++ tailWord_3973448) baseStart_3973448 baseEnd_3973448 := by
    simpa [prefixWord, tailWord_3973448, baseEnd_3973448] using wordTrace_append hprefix tailTrace_3973448
  have hstable : (prefixWord ++ tailWord_3973448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973448).length < 2 ^ (prefixWord ++ tailWord_3973448).sum := by decide
  have hdescent : baseEnd_3973448 < baseStart_3973448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973455 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 6, 3, 2]
def baseStart_3973455 : Nat := 118140960795 + 3973455 * 2 ^ 59
def prefixEnd_3973455 : Nat := 4983230072969 + 3 ^ 40 * 3973455 * 2
def baseEnd_3973455 : Nat := 2040292274010856572738919

theorem tailTrace_3973455 : CollatzResearch.WordTrace tailWord_3973455 prefixEnd_3973455 2040292274010856572738919 := by
  unfold tailWord_3973455
  simp only [CollatzResearch.WordTrace]
  refine ⟨144923809819858621932041819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96615873213239081288027879 144923809819858621932041819)
  ·
    refine ⟨217385714729787932898062729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144923809819858621932041819 217385714729787932898062729)
    ·
      refine ⟨163039286047340949673547047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217385714729787932898062729 163039286047340949673547047)
      ·
        refine ⟨244558929071011424510320571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163039286047340949673547047 244558929071011424510320571)
        ·
          refine ⟨366838393606517136765480857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244558929071011424510320571 366838393606517136765480857)
          ·
            refine ⟨275128795204887852574110643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366838393606517136765480857 275128795204887852574110643)
            ·
              refine ⟨412693192807331778861165965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275128795204887852574110643 412693192807331778861165965)
              ·
                refine ⟨154759947302749417072937237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412693192807331778861165965 154759947302749417072937237)
                ·
                  refine ⟨7254372529816378925293933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154759947302749417072937237 7254372529816378925293933)
                  ·
                    refine ⟨2720389698681142096985225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7254372529816378925293933 2720389698681142096985225)
                    ·
                      refine ⟨2040292274010856572738919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720389698681142096985225 2040292274010856572738919)
                      ·
                        rfl

theorem cell23_3973455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3, 2].length) (baseStart_3973455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973455 prefixEnd_3973455 := by exact prefixLift 3973455
  have htrace : WordTrace (prefixWord ++ tailWord_3973455) baseStart_3973455 baseEnd_3973455 := by
    simpa [prefixWord, tailWord_3973455, baseEnd_3973455] using wordTrace_append hprefix tailTrace_3973455
  have hstable : (prefixWord ++ tailWord_3973455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973455).length < 2 ^ (prefixWord ++ tailWord_3973455).sum := by decide
  have hdescent : baseEnd_3973455 < baseStart_3973455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973458 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3973458 : Nat := 118140960795 + 3973458 * 2 ^ 59
def prefixEnd_3973458 : Nat := 4983230072969 + 3 ^ 40 * 3973458 * 2
def baseEnd_3973458 : Nat := 2040293814452820061001405

theorem tailTrace_3973458 : CollatzResearch.WordTrace tailWord_3973458 prefixEnd_3973458 2040293814452820061001405 := by
  unfold tailWord_3973458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36230979809711938361100257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96615946159231835629600685 36230979809711938361100257)
  ·
    refine ⟨27173234857283953770825193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36230979809711938361100257 27173234857283953770825193)
    ·
      refine ⟨20379926142962965328118895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27173234857283953770825193 20379926142962965328118895)
      ·
        refine ⟨30569889214444447992178343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20379926142962965328118895 30569889214444447992178343)
        ·
          refine ⟨45854833821666671988267515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30569889214444447992178343 45854833821666671988267515)
          ·
            refine ⟨68782250732500007982401273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45854833821666671988267515 68782250732500007982401273)
            ·
              refine ⟨51586688049375005986800955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68782250732500007982401273 51586688049375005986800955)
              ·
                refine ⟨77380032074062508980201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51586688049375005986800955 77380032074062508980201433)
                ·
                  refine ⟨58035024055546881735151075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77380032074062508980201433 58035024055546881735151075)
                  ·
                    refine ⟨87052536083320322602726613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58035024055546881735151075 87052536083320322602726613)
                    ·
                      refine ⟨2040293814452820061001405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87052536083320322602726613 2040293814452820061001405)
                      ·
                        rfl

theorem cell23_3973458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3973458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973458 prefixEnd_3973458 := by exact prefixLift 3973458
  have htrace : WordTrace (prefixWord ++ tailWord_3973458) baseStart_3973458 baseEnd_3973458 := by
    simpa [prefixWord, tailWord_3973458, baseEnd_3973458] using wordTrace_append hprefix tailTrace_3973458
  have hstable : (prefixWord ++ tailWord_3973458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973458).length < 2 ^ (prefixWord ++ tailWord_3973458).sum := by decide
  have hdescent : baseEnd_3973458 < baseStart_3973458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973482 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3973482 : Nat := 118140960795 + 3973482 * 2 ^ 59
def prefixEnd_3973482 : Nat := 4983230072969 + 3 ^ 40 * 3973482 * 2
def baseEnd_3973482 : Nat := 680102045996175989033765

theorem tailTrace_3973482 : CollatzResearch.WordTrace tailWord_3973482 prefixEnd_3973482 680102045996175989033765 := by
  unfold tailWord_3973482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231198647690201385818675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96616529727173870362183133 36231198647690201385818675)
  ·
    refine ⟨54346797971535302078728013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36231198647690201385818675 54346797971535302078728013)
    ·
      refine ⟨20380049239325738279523005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54346797971535302078728013 20380049239325738279523005)
      ·
        refine ⟨7642518464747151854821127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20380049239325738279523005 7642518464747151854821127)
        ·
          refine ⟨11463777697120727782231691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642518464747151854821127 11463777697120727782231691)
          ·
            refine ⟨17195666545681091673347537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463777697120727782231691 17195666545681091673347537)
            ·
              refine ⟨12896749909260818755010653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17195666545681091673347537 12896749909260818755010653)
              ·
                refine ⟨4836281215972807033128995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12896749909260818755010653 4836281215972807033128995)
                ·
                  refine ⟨7254421823959210549693493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836281215972807033128995 7254421823959210549693493)
                  ·
                    refine ⟨680102045996175989033765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7254421823959210549693493 680102045996175989033765)
                    ·
                      rfl

theorem cell23_3973482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3973482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973482 prefixEnd_3973482 := by exact prefixLift 3973482
  have htrace : WordTrace (prefixWord ++ tailWord_3973482) baseStart_3973482 baseEnd_3973482 := by
    simpa [prefixWord, tailWord_3973482, baseEnd_3973482] using wordTrace_append hprefix tailTrace_3973482
  have hstable : (prefixWord ++ tailWord_3973482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973482).length < 2 ^ (prefixWord ++ tailWord_3973482).sum := by decide
  have hdescent : baseEnd_3973482 < baseStart_3973482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973498 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_3973498 : Nat := 118140960795 + 3973498 * 2 ^ 59
def prefixEnd_3973498 : Nat := 4983230072969 + 3 ^ 40 * 3973498 * 2
def baseEnd_3973498 : Nat := 2040314353678999904501221

theorem tailTrace_3973498 : CollatzResearch.WordTrace tailWord_3973498 prefixEnd_3973498 2040314353678999904501221 := by
  unfold tailWord_3973498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231344539675710068964287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96616918772468560183904765 36231344539675710068964287)
  ·
    refine ⟨54347016809513565103446431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36231344539675710068964287 54347016809513565103446431)
    ·
      refine ⟨81520525214270347655169647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54347016809513565103446431 81520525214270347655169647)
      ·
        refine ⟨122280787821405521482754471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81520525214270347655169647 122280787821405521482754471)
        ·
          refine ⟨183421181732108282224131707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122280787821405521482754471 183421181732108282224131707)
          ·
            refine ⟨275131772598162423336197561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183421181732108282224131707 275131772598162423336197561)
            ·
              refine ⟨206348829448621817502148171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275131772598162423336197561 206348829448621817502148171)
              ·
                refine ⟨309523244172932726253222257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206348829448621817502148171 309523244172932726253222257)
                ·
                  refine ⟨232142433129699544689916693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309523244172932726253222257 232142433129699544689916693)
                  ·
                    refine ⟨10881676552954666157339845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232142433129699544689916693 10881676552954666157339845)
                    ·
                      refine ⟨2040314353678999904501221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10881676552954666157339845 2040314353678999904501221)
                      ·
                        rfl

theorem cell23_3973498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_3973498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973498 prefixEnd_3973498 := by exact prefixLift 3973498
  have htrace : WordTrace (prefixWord ++ tailWord_3973498) baseStart_3973498 baseEnd_3973498 := by
    simpa [prefixWord, tailWord_3973498, baseEnd_3973498] using wordTrace_append hprefix tailTrace_3973498
  have hstable : (prefixWord ++ tailWord_3973498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973498).length < 2 ^ (prefixWord ++ tailWord_3973498).sum := by decide
  have hdescent : baseEnd_3973498 < baseStart_3973498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973512 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_3973512 : Nat := 118140960795 + 3973512 * 2 ^ 59
def prefixEnd_3973512 : Nat := 4983230072969 + 3 ^ 40 * 3973512 * 2
def baseEnd_3973512 : Nat := 680107180802720949908719

theorem tailTrace_3973512 : CollatzResearch.WordTrace tailWord_3973512 prefixEnd_3973512 680107180802720949908719 := by
  unfold tailWord_3973512
  simp only [CollatzResearch.WordTrace]
  refine ⟨72462944390326060333433395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96617259187101413777911193 72462944390326060333433395)
  ·
    refine ⟨108694416585489090500150093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72462944390326060333433395 108694416585489090500150093)
    ·
      refine ⟨40760406219558408937556285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108694416585489090500150093 40760406219558408937556285)
      ·
        refine ⟨15285152332334403351583607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40760406219558408937556285 15285152332334403351583607)
        ·
          refine ⟨22927728498501605027375411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285152332334403351583607 22927728498501605027375411)
          ·
            refine ⟨34391592747752407541063117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22927728498501605027375411 34391592747752407541063117)
            ·
              refine ⟨12896847280407152827898669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34391592747752407541063117 12896847280407152827898669)
              ·
                refine ⟨4836317730152682310462001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12896847280407152827898669 4836317730152682310462001)
                ·
                  refine ⟨3627238297614511732846501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836317730152682310462001 3627238297614511732846501)
                  ·
                    refine ⟨680107180802720949908719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627238297614511732846501 680107180802720949908719)
                    ·
                      rfl

theorem cell23_3973512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_3973512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973512 prefixEnd_3973512 := by exact prefixLift 3973512
  have htrace : WordTrace (prefixWord ++ tailWord_3973512) baseStart_3973512 baseEnd_3973512 := by
    simpa [prefixWord, tailWord_3973512, baseEnd_3973512] using wordTrace_append hprefix tailTrace_3973512
  have hstable : (prefixWord ++ tailWord_3973512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973512).length < 2 ^ (prefixWord ++ tailWord_3973512).sum := by decide
  have hdescent : baseEnd_3973512 < baseStart_3973512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973539 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 1, 2, 3]
def baseStart_3973539 : Nat := 118140960795 + 3973539 * 2 ^ 59
def prefixEnd_3973539 : Nat := 4983230072969 + 3 ^ 40 * 3973539 * 2
def baseEnd_3973539 : Nat := 2040335406385834244088533

theorem tailTrace_3973539 : CollatzResearch.WordTrace tailWord_3973539 prefixEnd_3973539 2040335406385834244088533 := by
  unfold tailWord_3973539
  simp only [CollatzResearch.WordTrace]
  refine ⟨144926873551554304278099671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96617915701036202852066447 144926873551554304278099671)
  ·
    refine ⟨217390310327331456417149507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144926873551554304278099671 217390310327331456417149507)
    ·
      refine ⟨326085465490997184625724261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217390310327331456417149507 326085465490997184625724261)
      ·
        refine ⟨61141024779561972117323299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326085465490997184625724261 61141024779561972117323299)
        ·
          refine ⟨91711537169342958175984949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61141024779561972117323299 91711537169342958175984949)
          ·
            refine ⟨8597956609625902328998589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91711537169342958175984949 8597956609625902328998589)
            ·
              refine ⟨3224233728609713373374471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8597956609625902328998589 3224233728609713373374471)
              ·
                refine ⟨4836350592914570060061707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224233728609713373374471 4836350592914570060061707)
                ·
                  refine ⟨7254525889371855090092561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836350592914570060061707 7254525889371855090092561)
                  ·
                    refine ⟨5440894417028891317569421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7254525889371855090092561 5440894417028891317569421)
                    ·
                      refine ⟨2040335406385834244088533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440894417028891317569421 2040335406385834244088533)
                      ·
                        rfl

theorem cell23_3973539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_3973539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973539 prefixEnd_3973539 := by exact prefixLift 3973539
  have htrace : WordTrace (prefixWord ++ tailWord_3973539) baseStart_3973539 baseEnd_3973539 := by
    simpa [prefixWord, tailWord_3973539, baseEnd_3973539] using wordTrace_append hprefix tailTrace_3973539
  have hstable : (prefixWord ++ tailWord_3973539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973539).length < 2 ^ (prefixWord ++ tailWord_3973539).sum := by decide
  have hdescent : baseEnd_3973539 < baseStart_3973539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973553 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_3973553 : Nat := 118140960795 + 3973553 * 2 ^ 59
def prefixEnd_3973553 : Nat := 4983230072969 + 3 ^ 40 * 3973553 * 2
def baseEnd_3973553 : Nat := 2040342595114997189313469

theorem tailTrace_3973553 : CollatzResearch.WordTrace tailWord_3973553 prefixEnd_3973553 2040342595114997189313469 := by
  unfold tailWord_3973553
  simp only [CollatzResearch.WordTrace]
  refine ⟨144927384173503584669109313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96618256115669056446072875 144927384173503584669109313)
  ·
    refine ⟨108695538130127688501831985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144927384173503584669109313 108695538130127688501831985)
    ·
      refine ⟨81521653597595766376373989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108695538130127688501831985 81521653597595766376373989)
      ·
        refine ⟨15285310049549206195570123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81521653597595766376373989 15285310049549206195570123)
        ·
          refine ⟨22927965074323809293355185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285310049549206195570123 22927965074323809293355185)
          ·
            refine ⟨17195973805742856970016389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22927965074323809293355185 17195973805742856970016389)
            ·
              refine ⟨3224245088576785681878073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17195973805742856970016389 3224245088576785681878073)
              ·
                refine ⟨2418183816432589261408555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224245088576785681878073 2418183816432589261408555)
                ·
                  refine ⟨3627275724648883892112833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418183816432589261408555 3627275724648883892112833)
                  ·
                    refine ⟨2720456793486662919084625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627275724648883892112833 2720456793486662919084625)
                    ·
                      refine ⟨2040342595114997189313469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720456793486662919084625 2040342595114997189313469)
                      ·
                        rfl

theorem cell23_3973553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_3973553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973553 prefixEnd_3973553 := by exact prefixLift 3973553
  have htrace : WordTrace (prefixWord ++ tailWord_3973553) baseStart_3973553 baseEnd_3973553 := by
    simpa [prefixWord, tailWord_3973553, baseEnd_3973553] using wordTrace_append hprefix tailTrace_3973553
  have hstable : (prefixWord ++ tailWord_3973553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973553).length < 2 ^ (prefixWord ++ tailWord_3973553).sum := by decide
  have hdescent : baseEnd_3973553 < baseStart_3973553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973603 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3973603 : Nat := 118140960795 + 3973603 * 2 ^ 59
def prefixEnd_3973603 : Nat := 4983230072969 + 3 ^ 40 * 3973603 * 2
def baseEnd_3973603 : Nat := 2040368269147721993688239

theorem tailTrace_3973603 : CollatzResearch.WordTrace tailWord_3973603 prefixEnd_3973603 2040368269147721993688239 := by
  unfold tailWord_3973603
  simp only [CollatzResearch.WordTrace]
  refine ⟨144929207823322443208429463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96619471882214962138952975 144929207823322443208429463)
  ·
    refine ⟨217393811734983664812644195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144929207823322443208429463 217393811734983664812644195)
    ·
      refine ⟨326090717602475497218966293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217393811734983664812644195 326090717602475497218966293)
      ·
        refine ⟨15285502387616038932139045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326090717602475497218966293 15285502387616038932139045)
        ·
          refine ⟨2866031697678007299776071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15285502387616038932139045 2866031697678007299776071)
          ·
            refine ⟨4299047546517010949664107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866031697678007299776071 4299047546517010949664107)
            ·
              refine ⟨6448571319775516424496161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299047546517010949664107 6448571319775516424496161)
              ·
                refine ⟨4836428489831637318372121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6448571319775516424496161 4836428489831637318372121)
                ·
                  refine ⟨3627321367373727988779091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836428489831637318372121 3627321367373727988779091)
                  ·
                    refine ⟨5440982051060591983168637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3627321367373727988779091 5440982051060591983168637)
                    ·
                      refine ⟨2040368269147721993688239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5440982051060591983168637 2040368269147721993688239)
                      ·
                        rfl

theorem cell23_3973603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3973603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973603 prefixEnd_3973603 := by exact prefixLift 3973603
  have htrace : WordTrace (prefixWord ++ tailWord_3973603) baseStart_3973603 baseEnd_3973603 := by
    simpa [prefixWord, tailWord_3973603, baseEnd_3973603] using wordTrace_append hprefix tailTrace_3973603
  have hstable : (prefixWord ++ tailWord_3973603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973603).length < 2 ^ (prefixWord ++ tailWord_3973603).sum := by decide
  have hdescent : baseEnd_3973603 < baseStart_3973603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973609 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 2, 2, 2]
def baseStart_3973609 : Nat := 118140960795 + 3973609 * 2 ^ 59
def prefixEnd_3973609 : Nat := 4983230072969 + 3 ^ 40 * 3973609 * 2
def baseEnd_3973609 : Nat := 2040371350031648970213211

theorem tailTrace_3973609 : CollatzResearch.WordTrace tailWord_3973609 prefixEnd_3973609 2040371350031648970213211 := by
  unfold tailWord_3973609
  simp only [CollatzResearch.WordTrace]
  refine ⟨144929426661300706233147881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96619617774200470822098587 144929426661300706233147881)
  ·
    refine ⟨108697069995975529674860911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144929426661300706233147881 108697069995975529674860911)
    ·
      refine ⟨163045604993963294512291367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108697069995975529674860911 163045604993963294512291367)
      ·
        refine ⟨244568407490944941768437051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163045604993963294512291367 244568407490944941768437051)
        ·
          refine ⟨366852611236417412652655577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244568407490944941768437051 366852611236417412652655577)
          ·
            refine ⟨275139458427313059489491683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366852611236417412652655577 275139458427313059489491683)
            ·
              refine ⟨412709187640969589234237525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275139458427313059489491683 412709187640969589234237525)
              ·
                refine ⟨4836435792667612373838721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 412709187640969589234237525 4836435792667612373838721)
                ·
                  refine ⟨3627326844500709280379041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836435792667612373838721 3627326844500709280379041)
                  ·
                    refine ⟨2720495133375531960284281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627326844500709280379041 2720495133375531960284281)
                    ·
                      refine ⟨2040371350031648970213211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720495133375531960284281 2040371350031648970213211)
                      ·
                        rfl

theorem cell23_3973609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2, 2].length) (baseStart_3973609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973609 prefixEnd_3973609 := by exact prefixLift 3973609
  have htrace : WordTrace (prefixWord ++ tailWord_3973609) baseStart_3973609 baseEnd_3973609 := by
    simpa [prefixWord, tailWord_3973609, baseEnd_3973609] using wordTrace_append hprefix tailTrace_3973609
  have hstable : (prefixWord ++ tailWord_3973609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973609).length < 2 ^ (prefixWord ++ tailWord_3973609).sum := by decide
  have hdescent : baseEnd_3973609 < baseStart_3973609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973622 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3973622 : Nat := 118140960795 + 3973622 * 2 ^ 59
def prefixEnd_3973622 : Nat := 4983230072969 + 3 ^ 40 * 3973622 * 2
def baseEnd_3973622 : Nat := 2040378025280157419350651

theorem tailTrace_3973622 : CollatzResearch.WordTrace tailWord_3973622 prefixEnd_3973622 2040378025280157419350651 := by
  unfold tailWord_3973622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058118800640850590835695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96619933873502406302247413 9058118800640850590835695)
  ·
    refine ⟨13587178200961275886253543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058118800640850590835695 13587178200961275886253543)
    ·
      refine ⟨20380767301441913829380315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587178200961275886253543 20380767301441913829380315)
      ·
        refine ⟨30571150952162870744070473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380767301441913829380315 30571150952162870744070473)
        ·
          refine ⟨22928363214122153058052855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30571150952162870744070473 22928363214122153058052855)
          ·
            refine ⟨34392544821183229587079283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22928363214122153058052855 34392544821183229587079283)
            ·
              refine ⟨51588817231774844380618925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34392544821183229587079283 51588817231774844380618925)
              ·
                refine ⟨19345806461915566642732097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51588817231774844380618925 19345806461915566642732097)
                ·
                  refine ⟨14509354846436674982049073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19345806461915566642732097 14509354846436674982049073)
                  ·
                    refine ⟨10882016134827506236536805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14509354846436674982049073 10882016134827506236536805)
                    ·
                      refine ⟨2040378025280157419350651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10882016134827506236536805 2040378025280157419350651)
                      ·
                        rfl

theorem cell23_3973622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3973622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973622 prefixEnd_3973622 := by exact prefixLift 3973622
  have htrace : WordTrace (prefixWord ++ tailWord_3973622) baseStart_3973622 baseEnd_3973622 := by
    simpa [prefixWord, tailWord_3973622, baseEnd_3973622] using wordTrace_append hprefix tailTrace_3973622
  have hstable : (prefixWord ++ tailWord_3973622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973622).length < 2 ^ (prefixWord ++ tailWord_3973622).sum := by decide
  have hdescent : baseEnd_3973622 < baseStart_3973622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973672 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3973672 : Nat := 118140960795 + 3973672 * 2 ^ 59
def prefixEnd_3973672 : Nat := 4983230072969 + 3 ^ 40 * 3973672 * 2
def baseEnd_3973672 : Nat := 2040403699312882223725421

theorem tailTrace_3973672 : CollatzResearch.WordTrace tailWord_3973672 prefixEnd_3973672 2040403699312882223725421 := by
  unfold tailWord_3973672
  simp only [CollatzResearch.WordTrace]
  refine ⟨72465862230036233996345635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96621149640048311995127513 72465862230036233996345635)
  ·
    refine ⟨108698793345054350994518453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72465862230036233996345635 108698793345054350994518453)
    ·
      refine ⟨10190511876098845405736105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108698793345054350994518453 10190511876098845405736105)
      ·
        refine ⟨7642883907074134054302079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10190511876098845405736105 7642883907074134054302079)
        ·
          refine ⟨11464325860611201081453119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642883907074134054302079 11464325860611201081453119)
          ·
            refine ⟨17196488790916801622179679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464325860611201081453119 17196488790916801622179679)
            ·
              refine ⟨25794733186375202433269519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17196488790916801622179679 25794733186375202433269519)
              ·
                refine ⟨38692099779562803649904279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25794733186375202433269519 38692099779562803649904279)
                ·
                  refine ⟨58038149669344205474856419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38692099779562803649904279 58038149669344205474856419)
                  ·
                    refine ⟨87057224504016308212284629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58038149669344205474856419 87057224504016308212284629)
                    ·
                      refine ⟨2040403699312882223725421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87057224504016308212284629 2040403699312882223725421)
                      ·
                        rfl

theorem cell23_3973672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3973672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973672 prefixEnd_3973672 := by exact prefixLift 3973672
  have htrace : WordTrace (prefixWord ++ tailWord_3973672) baseStart_3973672 baseEnd_3973672 := by
    simpa [prefixWord, tailWord_3973672, baseEnd_3973672] using wordTrace_append hprefix tailTrace_3973672
  have hstable : (prefixWord ++ tailWord_3973672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973672).length < 2 ^ (prefixWord ++ tailWord_3973672).sum := by decide
  have hdescent : baseEnd_3973672 < baseStart_3973672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973677 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3973677 : Nat := 118140960795 + 3973677 * 2 ^ 59
def prefixEnd_3973677 : Nat := 4983230072969 + 3 ^ 40 * 3973677 * 2
def baseEnd_3973677 : Nat := 2040406266716154704162899

theorem tailTrace_3973677 : CollatzResearch.WordTrace tailWord_3973677 prefixEnd_3973677 2040406266716154704162899 := by
  unfold tailWord_3973677
  simp only [CollatzResearch.WordTrace]
  refine ⟨144931906825054353846623285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96621271216702902564415523 144931906825054353846623285)
  ·
    refine ⟨13587366264848845673120933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144931906825054353846623285 13587366264848845673120933)
    ·
      refine ⟨2547631174659158563710175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13587366264848845673120933 2547631174659158563710175)
      ·
        refine ⟨3821446761988737845565263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547631174659158563710175 3821446761988737845565263)
        ·
          refine ⟨5732170142983106768347895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821446761988737845565263 5732170142983106768347895)
          ·
            refine ⟨8598255214474660152521843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732170142983106768347895 8598255214474660152521843)
            ·
              refine ⟨12897382821711990228782765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598255214474660152521843 12897382821711990228782765)
              ·
                refine ⟨4836518558141996335793537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12897382821711990228782765 4836518558141996335793537)
                ·
                  refine ⟨3627388918606497251845153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836518558141996335793537 3627388918606497251845153)
                  ·
                    refine ⟨2720541688954872938883865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627388918606497251845153 2720541688954872938883865)
                    ·
                      refine ⟨2040406266716154704162899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720541688954872938883865 2040406266716154704162899)
                      ·
                        rfl

theorem cell23_3973677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3973677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973677 prefixEnd_3973677 := by exact prefixLift 3973677
  have htrace : WordTrace (prefixWord ++ tailWord_3973677) baseStart_3973677 baseEnd_3973677 := by
    simpa [prefixWord, tailWord_3973677, baseEnd_3973677] using wordTrace_append hprefix tailTrace_3973677
  have hstable : (prefixWord ++ tailWord_3973677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973677).length < 2 ^ (prefixWord ++ tailWord_3973677).sum := by decide
  have hdescent : baseEnd_3973677 < baseStart_3973677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973759 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 2, 3, 2]
def baseStart_3973759 : Nat := 118140960795 + 3973759 * 2 ^ 59
def prefixEnd_3973759 : Nat := 4983230072969 + 3 ^ 40 * 3973759 * 2
def baseEnd_3973759 : Nat := 2040448372129823383337521

theorem tailTrace_3973759 : CollatzResearch.WordTrace tailWord_3973759 prefixEnd_3973759 2040448372129823383337521 := by
  unfold tailWord_3973759
  simp only [CollatzResearch.WordTrace]
  refine ⟨144934897610757281851108331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96623265073838187900738887 144934897610757281851108331)
  ·
    refine ⟨217402346416135922776662497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144934897610757281851108331 217402346416135922776662497)
    ·
      refine ⟨163051759812101942082496873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217402346416135922776662497 163051759812101942082496873)
      ·
        refine ⟨122288819859076456561872655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163051759812101942082496873 122288819859076456561872655)
        ·
          refine ⟨183433229788614684842808983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122288819859076456561872655 183433229788614684842808983)
          ·
            refine ⟨275149844682922027264213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183433229788614684842808983 275149844682922027264213475)
            ·
              refine ⟨412724767024383040896320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275149844682922027264213475 412724767024383040896320213)
              ·
                refine ⟨9673236727133977521007505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 412724767024383040896320213 9673236727133977521007505)
                ·
                  refine ⟨7254927545350483140755629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9673236727133977521007505 7254927545350483140755629)
                  ·
                    refine ⟨2720597829506431177783361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7254927545350483140755629 2720597829506431177783361)
                    ·
                      refine ⟨2040448372129823383337521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720597829506431177783361 2040448372129823383337521)
                      ·
                        rfl

theorem cell23_3973759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_3973759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973759 prefixEnd_3973759 := by exact prefixLift 3973759
  have htrace : WordTrace (prefixWord ++ tailWord_3973759) baseStart_3973759 baseEnd_3973759 := by
    simpa [prefixWord, tailWord_3973759, baseEnd_3973759] using wordTrace_append hprefix tailTrace_3973759
  have hstable : (prefixWord ++ tailWord_3973759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973759).length < 2 ^ (prefixWord ++ tailWord_3973759).sum := by decide
  have hdescent : baseEnd_3973759 < baseStart_3973759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973772 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3973772 : Nat := 118140960795 + 3973772 * 2 ^ 59
def prefixEnd_3973772 : Nat := 4983230072969 + 3 ^ 40 * 3973772 * 2
def baseEnd_3973772 : Nat := 2040455047378331832474961

theorem tailTrace_3973772 : CollatzResearch.WordTrace tailWord_3973772 prefixEnd_3973772 2040455047378331832474961 := by
  unfold tailWord_3973772
  simp only [CollatzResearch.WordTrace]
  refine ⟨72467685879855092535665785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96623581173140123380887713 72467685879855092535665785)
  ·
    refine ⟨54350764409891319401749339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72467685879855092535665785 54350764409891319401749339)
    ·
      refine ⟨81526146614836979102624009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54350764409891319401749339 81526146614836979102624009)
      ·
        refine ⟨61144609961127734326968007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81526146614836979102624009 61144609961127734326968007)
        ·
          refine ⟨91716914941691601490452011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61144609961127734326968007 91716914941691601490452011)
          ·
            refine ⟨137575372412537402235678017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91716914941691601490452011 137575372412537402235678017)
            ·
              refine ⟨103181529309403051676758513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137575372412537402235678017 103181529309403051676758513)
              ·
                refine ⟨77386146982052288757568885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103181529309403051676758513 77386146982052288757568885)
                ·
                  refine ⟨7254951279567402071022083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77386146982052288757568885 7254951279567402071022083)
                  ·
                    refine ⟨10882426919351103106533125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7254951279567402071022083 10882426919351103106533125)
                    ·
                      refine ⟨2040455047378331832474961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10882426919351103106533125 2040455047378331832474961)
                      ·
                        rfl

theorem cell23_3973772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3973772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973772 prefixEnd_3973772 := by exact prefixLift 3973772
  have htrace : WordTrace (prefixWord ++ tailWord_3973772) baseStart_3973772 baseEnd_3973772 := by
    simpa [prefixWord, tailWord_3973772, baseEnd_3973772] using wordTrace_append hprefix tailTrace_3973772
  have hstable : (prefixWord ++ tailWord_3973772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973772).length < 2 ^ (prefixWord ++ tailWord_3973772).sum := by decide
  have hdescent : baseEnd_3973772 < baseStart_3973772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973877 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3973877 : Nat := 118140960795 + 3973877 * 2 ^ 59
def prefixEnd_3973877 : Nat := 4983230072969 + 3 ^ 40 * 3973877 * 2
def baseEnd_3973877 : Nat := 2040508962847053921661979

theorem tailTrace_3973877 : CollatzResearch.WordTrace tailWord_3973877 prefixEnd_3973877 2040508962847053921661979 := by
  unfold tailWord_3973877
  simp only [CollatzResearch.WordTrace]
  refine ⟨144939201424329788003903885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96626134282886525335935923 144939201424329788003903885)
  ·
    refine ⟨54352200534123670501463957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144939201424329788003903885 54352200534123670501463957)
    ·
      refine ⟨2547759400037047054756123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54352200534123670501463957 2547759400037047054756123)
      ·
        refine ⟨3821639100055570582134185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547759400037047054756123 3821639100055570582134185)
        ·
          refine ⟨2866229325041677936600639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821639100055570582134185 2866229325041677936600639)
          ·
            refine ⟨4299343987562516904900959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866229325041677936600639 4299343987562516904900959)
            ·
              refine ⟨6449015981343775357351439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299343987562516904900959 6449015981343775357351439)
              ·
                refine ⟨9673523972015663036027159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449015981343775357351439 9673523972015663036027159)
                ·
                  refine ⟨14510285958023494554040739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9673523972015663036027159 14510285958023494554040739)
                  ·
                    refine ⟨21765428937035241831061109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14510285958023494554040739 21765428937035241831061109)
                    ·
                      refine ⟨2040508962847053921661979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21765428937035241831061109 2040508962847053921661979)
                      ·
                        rfl

theorem cell23_3973877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3973877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973877 prefixEnd_3973877 := by exact prefixLift 3973877
  have htrace : WordTrace (prefixWord ++ tailWord_3973877) baseStart_3973877 baseEnd_3973877 := by
    simpa [prefixWord, tailWord_3973877, baseEnd_3973877] using wordTrace_append hprefix tailTrace_3973877
  have hstable : (prefixWord ++ tailWord_3973877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973877).length < 2 ^ (prefixWord ++ tailWord_3973877).sum := by decide
  have hdescent : baseEnd_3973877 < baseStart_3973877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973890 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3973890 : Nat := 118140960795 + 3973890 * 2 ^ 59
def prefixEnd_3973890 : Nat := 4983230072969 + 3 ^ 40 * 3973890 * 2
def baseEnd_3973890 : Nat := 2040515638095562370799419

theorem tailTrace_3973890 : CollatzResearch.WordTrace tailWord_3973890 prefixEnd_3973890 2040515638095562370799419 := by
  unfold tailWord_3973890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36234918893320672806031781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96626450382188460816084749 36234918893320672806031781)
  ·
    refine ⟨6794047292497626151130959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36234918893320672806031781 6794047292497626151130959)
    ·
      refine ⟨10191070938746439226696439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794047292497626151130959 10191070938746439226696439)
      ·
        refine ⟨15286606408119658840044659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191070938746439226696439 15286606408119658840044659)
        ·
          refine ⟨22929909612179488260066989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286606408119658840044659 22929909612179488260066989)
          ·
            refine ⟨8598716104567308097525121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22929909612179488260066989 8598716104567308097525121)
            ·
              refine ⟨6449037078425481073143841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8598716104567308097525121 6449037078425481073143841)
              ·
                refine ⟨4836777808819110804857881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449037078425481073143841 4836777808819110804857881)
                ·
                  refine ⟨3627583356614333103643411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836777808819110804857881 3627583356614333103643411)
                  ·
                    refine ⟨5441375034921499655465117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3627583356614333103643411 5441375034921499655465117)
                    ·
                      refine ⟨2040515638095562370799419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5441375034921499655465117 2040515638095562370799419)
                      ·
                        rfl

theorem cell23_3973890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3973890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973890 prefixEnd_3973890 := by exact prefixLift 3973890
  have htrace : WordTrace (prefixWord ++ tailWord_3973890) baseStart_3973890 baseEnd_3973890 := by
    simpa [prefixWord, tailWord_3973890, baseEnd_3973890] using wordTrace_append hprefix tailTrace_3973890
  have hstable : (prefixWord ++ tailWord_3973890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973890).length < 2 ^ (prefixWord ++ tailWord_3973890).sum := by decide
  have hdescent : baseEnd_3973890 < baseStart_3973890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973909 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3973909 : Nat := 118140960795 + 3973909 * 2 ^ 59
def prefixEnd_3973909 : Nat := 4983230072969 + 3 ^ 40 * 3973909 * 2
def baseEnd_3973909 : Nat := 2040525394227997796461831

theorem tailTrace_3973909 : CollatzResearch.WordTrace tailWord_3973909 prefixEnd_3973909 2040525394227997796461831 := by
  unfold tailWord_3973909
  simp only [CollatzResearch.WordTrace]
  refine ⟨144940368560213857469068781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96626912373475904979379187 144940368560213857469068781)
  ·
    refine ⟨54352638210080196550900793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144940368560213857469068781 54352638210080196550900793)
    ·
      refine ⟨40764478657560147413175595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54352638210080196550900793 40764478657560147413175595)
      ·
        refine ⟨61146717986340221119763393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40764478657560147413175595 61146717986340221119763393)
        ·
          refine ⟨45860038489755165839822545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61146717986340221119763393 45860038489755165839822545)
          ·
            refine ⟨34395028867316374379866909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45860038489755165839822545 34395028867316374379866909)
            ·
              refine ⟨12898135825243640392450091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34395028867316374379866909 12898135825243640392450091)
              ·
                refine ⟨19347203737865460588675137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12898135825243640392450091 19347203737865460588675137)
                ·
                  refine ⟨14510402803399095441506353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19347203737865460588675137 14510402803399095441506353)
                  ·
                    refine ⟨10882802102549321581129765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14510402803399095441506353 10882802102549321581129765)
                    ·
                      refine ⟨2040525394227997796461831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10882802102549321581129765 2040525394227997796461831)
                      ·
                        rfl

theorem cell23_3973909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3973909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973909 prefixEnd_3973909 := by exact prefixLift 3973909
  have htrace : WordTrace (prefixWord ++ tailWord_3973909) baseStart_3973909 baseEnd_3973909 := by
    simpa [prefixWord, tailWord_3973909, baseEnd_3973909] using wordTrace_append hprefix tailTrace_3973909
  have hstable : (prefixWord ++ tailWord_3973909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973909).length < 2 ^ (prefixWord ++ tailWord_3973909).sum := by decide
  have hdescent : baseEnd_3973909 < baseStart_3973909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973919 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 7]
def baseStart_3973919 : Nat := 118140960795 + 3973919 * 2 ^ 59
def prefixEnd_3973919 : Nat := 4983230072969 + 3 ^ 40 * 3973919 * 2
def baseEnd_3973919 : Nat := 226725614337171417481865

theorem tailTrace_3973919 : CollatzResearch.WordTrace tailWord_3973919 prefixEnd_3973919 226725614337171417481865 := by
  unfold tailWord_3973919
  simp only [CollatzResearch.WordTrace]
  refine ⟨144940733290177629176932811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96627155526785086117955207 144940733290177629176932811)
  ·
    refine ⟨217411099935266443765399217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144940733290177629176932811 217411099935266443765399217)
    ·
      refine ⟨163058324951449832824049413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217411099935266443765399217 163058324951449832824049413)
      ·
        refine ⟨30573435928396843654509265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163058324951449832824049413 30573435928396843654509265)
        ·
          refine ⟨22930076946297632740881949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30573435928396843654509265 22930076946297632740881949)
          ·
            refine ⟨8598778854861612277830731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22930076946297632740881949 8598778854861612277830731)
            ·
              refine ⟨12898168282292418416746097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598778854861612277830731 12898168282292418416746097)
              ·
                refine ⟨9673626211719313812559573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12898168282292418416746097 9673626211719313812559573)
                ·
                  refine ⟨226725614337171417481865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9673626211719313812559573 226725614337171417481865)
                  ·
                    rfl

theorem cell23_3973919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 7].length) (baseStart_3973919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973919 prefixEnd_3973919 := by exact prefixLift 3973919
  have htrace : WordTrace (prefixWord ++ tailWord_3973919) baseStart_3973919 baseEnd_3973919 := by
    simpa [prefixWord, tailWord_3973919, baseEnd_3973919] using wordTrace_append hprefix tailTrace_3973919
  have hstable : (prefixWord ++ tailWord_3973919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973919).length < 2 ^ (prefixWord ++ tailWord_3973919).sum := by decide
  have hdescent : baseEnd_3973919 < baseStart_3973919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973953 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 7]
def baseStart_3973953 : Nat := 118140960795 + 3973953 * 2 ^ 59
def prefixEnd_3973953 : Nat := 4983230072969 + 3 ^ 40 * 3973953 * 2
def baseEnd_3973953 : Nat := 226727554152977291590181

theorem tailTrace_3973953 : CollatzResearch.WordTrace tailWord_3973953 prefixEnd_3973953 226727554152977291590181 := by
  unfold tailWord_3973953
  simp only [CollatzResearch.WordTrace]
  refine ⟨144941973372054452983670513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96627982248036301989113675 144941973372054452983670513)
  ·
    refine ⟨108706480029040839737752885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144941973372054452983670513 108706480029040839737752885)
    ·
      refine ⟨10191232502722578725414333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108706480029040839737752885 10191232502722578725414333)
      ·
        refine ⟨3821712188520967022030375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10191232502722578725414333 3821712188520967022030375)
        ·
          refine ⟨5732568282781450533045563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821712188520967022030375 5732568282781450533045563)
          ·
            refine ⟨8598852424172175799568345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732568282781450533045563 8598852424172175799568345)
            ·
              refine ⟨6449139318129131849676259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8598852424172175799568345 6449139318129131849676259)
              ·
                refine ⟨9673708977193697774514389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449139318129131849676259 9673708977193697774514389)
                ·
                  refine ⟨226727554152977291590181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9673708977193697774514389 226727554152977291590181)
                  ·
                    rfl

theorem cell23_3973953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_3973953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973953 prefixEnd_3973953 := by exact prefixLift 3973953
  have htrace : WordTrace (prefixWord ++ tailWord_3973953) baseStart_3973953 baseEnd_3973953 := by
    simpa [prefixWord, tailWord_3973953, baseEnd_3973953] using wordTrace_append hprefix tailTrace_3973953
  have hstable : (prefixWord ++ tailWord_3973953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973953).length < 2 ^ (prefixWord ++ tailWord_3973953).sum := by decide
  have hdescent : baseEnd_3973953 < baseStart_3973953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973979 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 11, 4]
def baseStart_3973979 : Nat := 118140960795 + 3973979 * 2 ^ 59
def prefixEnd_3973979 : Nat := 4983230072969 + 3 ^ 40 * 3973979 * 2
def baseEnd_3973979 : Nat := 680187112624604174195503

theorem tailTrace_3973979 : CollatzResearch.WordTrace tailWord_3973979 prefixEnd_3973979 680187112624604174195503 := by
  unfold tailWord_3973979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144942921669960259424116991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96628614446640172949411327 144942921669960259424116991)
  ·
    refine ⟨217414382504940389136175487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144942921669960259424116991 217414382504940389136175487)
    ·
      refine ⟨326121573757410583704263231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217414382504940389136175487 326121573757410583704263231)
      ·
        refine ⟨489182360636115875556394847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326121573757410583704263231 489182360636115875556394847)
        ·
          refine ⟨733773540954173813334592271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489182360636115875556394847 733773540954173813334592271)
          ·
            refine ⟨1100660311431260720001888407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733773540954173813334592271 1100660311431260720001888407)
            ·
              refine ⟨1650990467146891080002832611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100660311431260720001888407 1650990467146891080002832611)
              ·
                refine ⟨2476485700720336620004248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650990467146891080002832611 2476485700720336620004248917)
                ·
                  refine ⟨3627664600664555595709349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 2476485700720336620004248917 3627664600664555595709349)
                  ·
                    refine ⟨680187112624604174195503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627664600664555595709349 680187112624604174195503)
                    ·
                      rfl

theorem cell23_3973979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 4].length) (baseStart_3973979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3973979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3973979 prefixEnd_3973979 := by exact prefixLift 3973979
  have htrace : WordTrace (prefixWord ++ tailWord_3973979) baseStart_3973979 baseEnd_3973979 := by
    simpa [prefixWord, tailWord_3973979, baseEnd_3973979] using wordTrace_append hprefix tailTrace_3973979
  have hstable : (prefixWord ++ tailWord_3973979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973979).length < 2 ^ (prefixWord ++ tailWord_3973979).sum := by decide
  have hdescent : baseEnd_3973979 < baseStart_3973979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974009 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 8]
def baseStart_3974009 : Nat := 118140960795 + 3974009 * 2 ^ 59
def prefixEnd_3974009 : Nat := 4983230072969 + 3 ^ 40 * 3974009 * 2
def baseEnd_3974009 : Nat := 226730749143716378356819

theorem tailTrace_3974009 : CollatzResearch.WordTrace tailWord_3974009 prefixEnd_3974009 226730749143716378356819 := by
  unfold tailWord_3974009
  simp only [CollatzResearch.WordTrace]
  refine ⟨144944015859851574547709081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96629343906567716365139387 144944015859851574547709081)
  ·
    refine ⟨108708011894888680910781811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144944015859851574547709081 108708011894888680910781811)
    ·
      refine ⟨163062017842333021366172717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108708011894888680910781811 163062017842333021366172717)
      ·
        refine ⟨61148256690874883012314769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163062017842333021366172717 61148256690874883012314769)
        ·
          refine ⟨45861192518156162259236077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61148256690874883012314769 45861192518156162259236077)
          ·
            refine ⟨17197947194308560847213529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45861192518156162259236077 17197947194308560847213529)
            ·
              refine ⟨12898460395731420635410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17197947194308560847213529 12898460395731420635410147)
              ·
                refine ⟨19347690593597130953115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12898460395731420635410147 19347690593597130953115221)
                ·
                  refine ⟨226730749143716378356819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19347690593597130953115221 226730749143716378356819)
                  ·
                    rfl

theorem cell23_3974009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_3974009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974009 prefixEnd_3974009 := by exact prefixLift 3974009
  have htrace : WordTrace (prefixWord ++ tailWord_3974009) baseStart_3974009 baseEnd_3974009 := by
    simpa [prefixWord, tailWord_3974009, baseEnd_3974009] using wordTrace_append hprefix tailTrace_3974009
  have hstable : (prefixWord ++ tailWord_3974009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974009).length < 2 ^ (prefixWord ++ tailWord_3974009).sum := by decide
  have hdescent : baseEnd_3974009 < baseStart_3974009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974013 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3974013 : Nat := 118140960795 + 3974013 * 2 ^ 59
def prefixEnd_3974013 : Nat := 4983230072969 + 3 ^ 40 * 3974013 * 2
def baseEnd_3974013 : Nat := 680192932072021796520451

theorem tailTrace_3974013 : CollatzResearch.WordTrace tailWord_3974013 prefixEnd_3974013 680192932072021796520451 := by
  unfold tailWord_3974013
  simp only [CollatzResearch.WordTrace]
  refine ⟨144944161751837083230854693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96629441167891388820569795 144944161751837083230854693)
  ·
    refine ⟨27177030328469453105785255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144944161751837083230854693 27177030328469453105785255)
    ·
      refine ⟨40765545492704179658677883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177030328469453105785255 40765545492704179658677883)
      ·
        refine ⟨61148318239056269488016825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40765545492704179658677883 61148318239056269488016825)
        ·
          refine ⟨45861238679292202116012619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61148318239056269488016825 45861238679292202116012619)
          ·
            refine ⟨68791858018938303174018929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45861238679292202116012619 68791858018938303174018929)
            ·
              refine ⟨51593893514203727380514197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68791858018938303174018929 51593893514203727380514197)
              ·
                refine ⟨2418463758478299720961603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51593893514203727380514197 2418463758478299720961603)
                ·
                  refine ⟨3627695637717449581442405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418463758478299720961603 3627695637717449581442405)
                  ·
                    refine ⟨680192932072021796520451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627695637717449581442405 680192932072021796520451)
                    ·
                      rfl

theorem cell23_3974013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3974013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974013 prefixEnd_3974013 := by exact prefixLift 3974013
  have htrace : WordTrace (prefixWord ++ tailWord_3974013) baseStart_3974013 baseEnd_3974013 := by
    simpa [prefixWord, tailWord_3974013, baseEnd_3974013] using wordTrace_append hprefix tailTrace_3974013
  have hstable : (prefixWord ++ tailWord_3974013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974013).length < 2 ^ (prefixWord ++ tailWord_3974013).sum := by decide
  have hdescent : baseEnd_3974013 < baseStart_3974013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974127 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 1, 2, 2]
def baseStart_3974127 : Nat := 118140960795 + 3974127 * 2 ^ 59
def prefixEnd_3974127 : Nat := 4983230072969 + 3 ^ 40 * 3974127 * 2
def baseEnd_3974127 : Nat := 2040637333010677943535829

theorem tailTrace_3974127 : CollatzResearch.WordTrace tailWord_3974127 prefixEnd_3974127 2040637333010677943535829 := by
  unfold tailWord_3974127
  simp only [CollatzResearch.WordTrace]
  refine ⟨144948319673424080700504635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96632213115616053800336423 144948319673424080700504635)
  ·
    refine ⟨217422479510136121050756953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144948319673424080700504635 217422479510136121050756953)
    ·
      refine ⟨163066859632602090788067715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217422479510136121050756953 163066859632602090788067715)
      ·
        refine ⟨244600289448903136182101573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163066859632602090788067715 244600289448903136182101573)
        ·
          refine ⟨45862554271669338034144045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244600289448903136182101573 45862554271669338034144045)
          ·
            refine ⟨17198457851876001762804017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45862554271669338034144045 17198457851876001762804017)
            ·
              refine ⟨12898843388907001322103013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17198457851876001762804017 12898843388907001322103013)
              ·
                refine ⟨2418533135420062747894315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12898843388907001322103013 2418533135420062747894315)
                ·
                  refine ⟨3627799703130094121841473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418533135420062747894315 3627799703130094121841473)
                  ·
                    refine ⟨2720849777347570591381105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3627799703130094121841473 2720849777347570591381105)
                    ·
                      refine ⟨2040637333010677943535829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720849777347570591381105 2040637333010677943535829)
                      ·
                        rfl

theorem cell23_3974127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 2, 2].length) (baseStart_3974127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974127 prefixEnd_3974127 := by exact prefixLift 3974127
  have htrace : WordTrace (prefixWord ++ tailWord_3974127) baseStart_3974127 baseEnd_3974127 := by
    simpa [prefixWord, tailWord_3974127, baseEnd_3974127] using wordTrace_append hprefix tailTrace_3974127
  have hstable : (prefixWord ++ tailWord_3974127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974127).length < 2 ^ (prefixWord ++ tailWord_3974127).sum := by decide
  have hdescent : baseEnd_3974127 < baseStart_3974127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974130 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3974130 : Nat := 118140960795 + 3974130 * 2 ^ 59
def prefixEnd_3974130 : Nat := 4983230072969 + 3 ^ 40 * 3974130 * 2
def baseEnd_3974130 : Nat := 2040638873452641431798315

theorem tailTrace_3974130 : CollatzResearch.WordTrace tailWord_3974130 prefixEnd_3974130 2040638873452641431798315 := by
  unfold tailWord_3974130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36237107273103303053215961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96632286061608808141909229 36237107273103303053215961)
  ·
    refine ⟨27177830454827477289911971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36237107273103303053215961 27177830454827477289911971)
    ·
      refine ⟨40766745682241215934867957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177830454827477289911971 40766745682241215934867957)
      ·
        refine ⟨3821882407710113993893871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40766745682241215934867957 3821882407710113993893871)
        ·
          refine ⟨5732823611565170990840807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821882407710113993893871 5732823611565170990840807)
          ·
            refine ⟨8599235417347756486261211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732823611565170990840807 8599235417347756486261211)
            ·
              refine ⟨12898853126021634729391817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8599235417347756486261211 12898853126021634729391817)
              ·
                refine ⟨9674139844516226047043863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12898853126021634729391817 9674139844516226047043863)
                ·
                  refine ⟨14511209766774339070565795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674139844516226047043863 14511209766774339070565795)
                  ·
                    refine ⟨21766814650161508605848693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14511209766774339070565795 21766814650161508605848693)
                    ·
                      refine ⟨2040638873452641431798315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21766814650161508605848693 2040638873452641431798315)
                      ·
                        rfl

theorem cell23_3974130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3974130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974130 prefixEnd_3974130 := by exact prefixLift 3974130
  have htrace : WordTrace (prefixWord ++ tailWord_3974130) baseStart_3974130 baseEnd_3974130 := by
    simpa [prefixWord, tailWord_3974130, baseEnd_3974130] using wordTrace_append hprefix tailTrace_3974130
  have hstable : (prefixWord ++ tailWord_3974130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974130).length < 2 ^ (prefixWord ++ tailWord_3974130).sum := by decide
  have hdescent : baseEnd_3974130 < baseStart_3974130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974153 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 3, 3, 2]
def baseStart_3974153 : Nat := 118140960795 + 3974153 * 2 ^ 59
def prefixEnd_3974153 : Nat := 4983230072969 + 3 ^ 40 * 3974153 * 2
def baseEnd_3974153 : Nat := 2040650683507694841810709

theorem tailTrace_3974153 : CollatzResearch.WordTrace tailWord_3974153 prefixEnd_3974153 2040650683507694841810709 := by
  unfold tailWord_3974153
  simp only [CollatzResearch.WordTrace]
  refine ⟨144949267971329887140951113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96632845314219924760634075 144949267971329887140951113)
  ·
    refine ⟨108711950978497415355713335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144949267971329887140951113 108711950978497415355713335)
    ·
      refine ⟨163067926467746123033570003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108711950978497415355713335 163067926467746123033570003)
      ·
        refine ⟨244601889701619184550355005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163067926467746123033570003 244601889701619184550355005)
        ·
          refine ⟨91725708638107194206383127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244601889701619184550355005 91725708638107194206383127)
          ·
            refine ⟨137588562957160791309574691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91725708638107194206383127 137588562957160791309574691)
            ·
              refine ⟨206382844435741186964362037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137588562957160791309574691 206382844435741186964362037)
              ·
                refine ⟨19348391665850736277908941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206382844435741186964362037 19348391665850736277908941)
                ·
                  refine ⟨7255646874694026104215853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19348391665850736277908941 7255646874694026104215853)
                  ·
                    refine ⟨2720867578010259789080945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7255646874694026104215853 2720867578010259789080945)
                    ·
                      refine ⟨2040650683507694841810709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720867578010259789080945 2040650683507694841810709)
                      ·
                        rfl

theorem cell23_3974153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3, 2].length) (baseStart_3974153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974153 prefixEnd_3974153 := by exact prefixLift 3974153
  have htrace : WordTrace (prefixWord ++ tailWord_3974153) baseStart_3974153 baseEnd_3974153 := by
    simpa [prefixWord, tailWord_3974153, baseEnd_3974153] using wordTrace_append hprefix tailTrace_3974153
  have hstable : (prefixWord ++ tailWord_3974153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974153).length < 2 ^ (prefixWord ++ tailWord_3974153).sum := by decide
  have hdescent : baseEnd_3974153 < baseStart_3974153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974156 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3974156 : Nat := 118140960795 + 3974156 * 2 ^ 59
def prefixEnd_3974156 : Nat := 4983230072969 + 3 ^ 40 * 3974156 * 2
def baseEnd_3974156 : Nat := 2040652223949658330073195

theorem tailTrace_3974156 : CollatzResearch.WordTrace tailWord_3974156 prefixEnd_3974156 2040652223949658330073195 := by
  unfold tailWord_3974156
  simp only [CollatzResearch.WordTrace]
  refine ⟨72474688695159509326655161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96632918260212679102206881 72474688695159509326655161)
  ·
    refine ⟨54356016521369631994991371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72474688695159509326655161 54356016521369631994991371)
    ·
      refine ⟨81534024782054447992487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54356016521369631994991371 81534024782054447992487057)
      ·
        refine ⟨61150518586540835994365293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81534024782054447992487057 61150518586540835994365293)
        ·
          refine ⟨22931444469952813497886985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61150518586540835994365293 22931444469952813497886985)
          ·
            refine ⟨17198583352464610123415239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22931444469952813497886985 17198583352464610123415239)
            ·
              refine ⟨25797875028696915185122859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17198583352464610123415239 25797875028696915185122859)
              ·
                refine ⟨38696812543045372777684289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25797875028696915185122859 38696812543045372777684289)
                ·
                  refine ⟨29022609407284029583263217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38696812543045372777684289 29022609407284029583263217)
                  ·
                    refine ⟨21766957055463022187447413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29022609407284029583263217 21766957055463022187447413)
                    ·
                      refine ⟨2040652223949658330073195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21766957055463022187447413 2040652223949658330073195)
                      ·
                        rfl

theorem cell23_3974156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3974156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974156 prefixEnd_3974156 := by exact prefixLift 3974156
  have htrace : WordTrace (prefixWord ++ tailWord_3974156) baseStart_3974156 baseEnd_3974156 := by
    simpa [prefixWord, tailWord_3974156, baseEnd_3974156] using wordTrace_append hprefix tailTrace_3974156
  have hstable : (prefixWord ++ tailWord_3974156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974156).length < 2 ^ (prefixWord ++ tailWord_3974156).sum := by decide
  have hdescent : baseEnd_3974156 < baseStart_3974156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974170 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_3974170 : Nat := 118140960795 + 3974170 * 2 ^ 59
def prefixEnd_3974170 : Nat := 4983230072969 + 3 ^ 40 * 3974170 * 2
def baseEnd_3974170 : Nat := 2040659412678821275298131

theorem tailTrace_3974170 : CollatzResearch.WordTrace tailWord_3974170 prefixEnd_3974170 2040659412678821275298131 := by
  unfold tailWord_3974170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36237472003067074761079991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96633258674845532696213309 36237472003067074761079991)
  ·
    refine ⟨54356208004600612141619987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36237472003067074761079991 54356208004600612141619987)
    ·
      refine ⟨81534312006900918212429981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54356208004600612141619987 81534312006900918212429981)
      ·
        refine ⟨30575367002587844329661243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81534312006900918212429981 30575367002587844329661243)
        ·
          refine ⟨45863050503881766494491865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30575367002587844329661243 45863050503881766494491865)
          ·
            refine ⟨34397287877911324870868899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45863050503881766494491865 34397287877911324870868899)
            ·
              refine ⟨51595931816866987306303349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34397287877911324870868899 51595931816866987306303349)
              ·
                refine ⟨4837118607831280059965939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51595931816866987306303349 4837118607831280059965939)
                ·
                  refine ⟨7255677911746920089948909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837118607831280059965939 7255677911746920089948909)
                  ·
                    refine ⟨2720879216905095033730841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7255677911746920089948909 2720879216905095033730841)
                    ·
                      refine ⟨2040659412678821275298131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2720879216905095033730841 2040659412678821275298131)
                      ·
                        rfl

theorem cell23_3974170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_3974170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974170 prefixEnd_3974170 := by exact prefixLift 3974170
  have htrace : WordTrace (prefixWord ++ tailWord_3974170) baseStart_3974170 baseEnd_3974170 := by
    simpa [prefixWord, tailWord_3974170, baseEnd_3974170] using wordTrace_append hprefix tailTrace_3974170
  have hstable : (prefixWord ++ tailWord_3974170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974170).length < 2 ^ (prefixWord ++ tailWord_3974170).sum := by decide
  have hdescent : baseEnd_3974170 < baseStart_3974170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974250 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3974250 : Nat := 118140960795 + 3974250 * 2 ^ 59
def prefixEnd_3974250 : Nat := 4983230072969 + 3 ^ 40 * 3974250 * 2
def baseEnd_3974250 : Nat := 2040700491131180962297763

theorem tailTrace_3974250 : CollatzResearch.WordTrace tailWord_3974250 prefixEnd_3974250 2040700491131180962297763 := by
  unfold tailWord_3974250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238201462994618176808051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96635203901318981804821469 36238201462994618176808051)
  ·
    refine ⟨54357302194491927265212077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36238201462994618176808051 54357302194491927265212077)
    ·
      refine ⟨20383988322934472724454529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54357302194491927265212077 20383988322934472724454529)
      ·
        refine ⟨15287991242200854543340897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20383988322934472724454529 15287991242200854543340897)
        ·
          refine ⟨11465993431650640907505673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15287991242200854543340897 11465993431650640907505673)
          ·
            refine ⟨8599495073737980680629255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11465993431650640907505673 8599495073737980680629255)
            ·
              refine ⟨12899242610606971020943883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8599495073737980680629255 12899242610606971020943883)
              ·
                refine ⟨19348863915910456531415825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12899242610606971020943883 19348863915910456531415825)
                ·
                  refine ⟨14511647936932842398561869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19348863915910456531415825 14511647936932842398561869)
                  ·
                    refine ⟨5441867976349815899460701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14511647936932842398561869 5441867976349815899460701)
                    ·
                      refine ⟨2040700491131180962297763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5441867976349815899460701 2040700491131180962297763)
                      ·
                        rfl

theorem cell23_3974250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3974250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974250 prefixEnd_3974250 := by exact prefixLift 3974250
  have htrace : WordTrace (prefixWord ++ tailWord_3974250) baseStart_3974250 baseEnd_3974250 := by
    simpa [prefixWord, tailWord_3974250, baseEnd_3974250] using wordTrace_append hprefix tailTrace_3974250
  have hstable : (prefixWord ++ tailWord_3974250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974250).length < 2 ^ (prefixWord ++ tailWord_3974250).sum := by decide
  have hdescent : baseEnd_3974250 < baseStart_3974250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974300 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3974300 : Nat := 118140960795 + 3974300 * 2 ^ 59
def prefixEnd_3974300 : Nat := 4983230072969 + 3 ^ 40 * 3974300 * 2
def baseEnd_3974300 : Nat := 680242055054635255557511

theorem tailTrace_3974300 : CollatzResearch.WordTrace tailWord_3974300 prefixEnd_3974300 680242055054635255557511 := by
  unfold tailWord_3974300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72477314750898665623276177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96636419667864887497701569 72477314750898665623276177)
  ·
    refine ⟨54357986063173999217457133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72477314750898665623276177 54357986063173999217457133)
    ·
      refine ⟨20384244773690249706546425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54357986063173999217457133 20384244773690249706546425)
      ·
        refine ⟨15288183580267687279909819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20384244773690249706546425 15288183580267687279909819)
        ·
          refine ⟨22932275370401530919864729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288183580267687279909819 22932275370401530919864729)
          ·
            refine ⟨17199206527801148189898547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22932275370401530919864729 17199206527801148189898547)
            ·
              refine ⟨25798809791701722284847821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17199206527801148189898547 25798809791701722284847821)
              ·
                refine ⟨9674553671888145856817933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25798809791701722284847821 9674553671888145856817933)
                ·
                  refine ⟨3627957626958054696306725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9674553671888145856817933 3627957626958054696306725)
                  ·
                    refine ⟨680242055054635255557511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627957626958054696306725 680242055054635255557511)
                    ·
                      rfl

theorem cell23_3974300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3974300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974300 prefixEnd_3974300 := by exact prefixLift 3974300
  have htrace : WordTrace (prefixWord ++ tailWord_3974300) baseStart_3974300 baseEnd_3974300 := by
    simpa [prefixWord, tailWord_3974300, baseEnd_3974300] using wordTrace_append hprefix tailTrace_3974300
  have hstable : (prefixWord ++ tailWord_3974300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974300).length < 2 ^ (prefixWord ++ tailWord_3974300).sum := by decide
  have hdescent : baseEnd_3974300 < baseStart_3974300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974334 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3974334 : Nat := 118140960795 + 3974334 * 2 ^ 59
def prefixEnd_3974334 : Nat := 4983230072969 + 3 ^ 40 * 3974334 * 2
def baseEnd_3974334 : Nat := 680247874502052877882459

theorem tailTrace_3974334 : CollatzResearch.WordTrace tailWord_3974334 prefixEnd_3974334 680247874502052877882459 := by
  unfold tailWord_3974334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119483697959269381661257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96637246389116103368860037 18119483697959269381661257)
  ·
    refine ⟨13589612773469452036245943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18119483697959269381661257 13589612773469452036245943)
    ·
      refine ⟨20384419160204178054368915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13589612773469452036245943 20384419160204178054368915)
      ·
        refine ⟨30576628740306267081553373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20384419160204178054368915 30576628740306267081553373)
        ·
          refine ⟨11466235777614850155582515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30576628740306267081553373 11466235777614850155582515)
          ·
            refine ⟨17199353666422275233373773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466235777614850155582515 17199353666422275233373773)
            ·
              refine ⟨6449757624908353212515165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17199353666422275233373773 6449757624908353212515165)
              ·
                refine ⟨2418659109340632454693187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6449757624908353212515165 2418659109340632454693187)
                ·
                  refine ⟨3627988664010948682039781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418659109340632454693187 3627988664010948682039781)
                  ·
                    refine ⟨680247874502052877882459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627988664010948682039781 680247874502052877882459)
                    ·
                      rfl

theorem cell23_3974334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3974334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974334 prefixEnd_3974334 := by exact prefixLift 3974334
  have htrace : WordTrace (prefixWord ++ tailWord_3974334) baseStart_3974334 baseEnd_3974334 := by
    simpa [prefixWord, tailWord_3974334, baseEnd_3974334] using wordTrace_append hprefix tailTrace_3974334
  have hstable : (prefixWord ++ tailWord_3974334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974334).length < 2 ^ (prefixWord ++ tailWord_3974334).sum := by decide
  have hdescent : baseEnd_3974334 < baseStart_3974334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974380 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_3974380 : Nat := 118140960795 + 3974380 * 2 ^ 59
def prefixEnd_3974380 : Nat := 4983230072969 + 3 ^ 40 * 3974380 * 2
def baseEnd_3974380 : Nat := 2040767243616265453672165

theorem tailTrace_3974380 : CollatzResearch.WordTrace tailWord_3974380 prefixEnd_3974380 2040767243616265453672165 := by
  unfold tailWord_3974380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72478773670753752454732297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96638364894338336606309729 72478773670753752454732297)
  ·
    refine ⟨54359080253065314341049223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72478773670753752454732297 54359080253065314341049223)
    ·
      refine ⟨81538620379597971511573835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54359080253065314341049223 81538620379597971511573835)
      ·
        refine ⟨122307930569396957267360753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81538620379597971511573835 122307930569396957267360753)
        ·
          refine ⟨91730947927047717950520565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122307930569396957267360753 91730947927047717950520565)
          ·
            refine ⟨8599776368160723557861303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91730947927047717950520565 8599776368160723557861303)
            ·
              refine ⟨12899664552241085336791955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8599776368160723557861303 12899664552241085336791955)
              ·
                refine ⟨19349496828361628005187933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12899664552241085336791955 19349496828361628005187933)
                ·
                  refine ⟨7256061310635610501945475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19349496828361628005187933 7256061310635610501945475)
                  ·
                    refine ⟨10884091965953415752918213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256061310635610501945475 10884091965953415752918213)
                    ·
                      refine ⟨2040767243616265453672165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10884091965953415752918213 2040767243616265453672165)
                      ·
                        rfl

theorem cell23_3974380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_3974380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974380 prefixEnd_3974380 := by exact prefixLift 3974380
  have htrace : WordTrace (prefixWord ++ tailWord_3974380) baseStart_3974380 baseEnd_3974380 := by
    simpa [prefixWord, tailWord_3974380, baseEnd_3974380] using wordTrace_append hprefix tailTrace_3974380
  have hstable : (prefixWord ++ tailWord_3974380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974380).length < 2 ^ (prefixWord ++ tailWord_3974380).sum := by decide
  have hdescent : baseEnd_3974380 < baseStart_3974380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974408 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_3974408 : Nat := 118140960795 + 3974408 * 2 ^ 59
def prefixEnd_3974408 : Nat := 4983230072969 + 3 ^ 40 * 3974408 * 2
def baseEnd_3974408 : Nat := 2040781621074591344122037

theorem tailTrace_3974408 : CollatzResearch.WordTrace tailWord_3974408 prefixEnd_3974408 2040781621074591344122037 := by
  unfold tailWord_3974408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72479284292703032845741939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96639045723604043794322585 72479284292703032845741939)
  ·
    refine ⟨108718926439054549268612909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72479284292703032845741939 108718926439054549268612909)
    ·
      refine ⟨40769597414645455975729841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108718926439054549268612909 40769597414645455975729841)
      ·
        refine ⟨30577198060984091981797381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40769597414645455975729841 30577198060984091981797381)
        ·
          refine ⟨5733224636434517246587009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30577198060984091981797381 5733224636434517246587009)
          ·
            refine ⟨4299918477325887934940257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5733224636434517246587009 4299918477325887934940257)
            ·
              refine ⟨3224938857994415951205193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299918477325887934940257 3224938857994415951205193)
              ·
                refine ⟨2418704143495811963403895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224938857994415951205193 2418704143495811963403895)
                ·
                  refine ⟨3628056215243717945105843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418704143495811963403895 3628056215243717945105843)
                  ·
                    refine ⟨5442084322865576917658765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628056215243717945105843 5442084322865576917658765)
                    ·
                      refine ⟨2040781621074591344122037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442084322865576917658765 2040781621074591344122037)
                      ·
                        rfl

theorem cell23_3974408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_3974408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974408 prefixEnd_3974408 := by exact prefixLift 3974408
  have htrace : WordTrace (prefixWord ++ tailWord_3974408) baseStart_3974408 baseEnd_3974408 := by
    simpa [prefixWord, tailWord_3974408, baseEnd_3974408] using wordTrace_append hprefix tailTrace_3974408
  have hstable : (prefixWord ++ tailWord_3974408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974408).length < 2 ^ (prefixWord ++ tailWord_3974408).sum := by decide
  have hdescent : baseEnd_3974408 < baseStart_3974408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974433 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3974433 : Nat := 118140960795 + 3974433 * 2 ^ 59
def prefixEnd_3974433 : Nat := 4983230072969 + 3 ^ 40 * 3974433 * 2
def baseEnd_3974433 : Nat := 680264819363651248769807

theorem tailTrace_3974433 : CollatzResearch.WordTrace tailWord_3974433 prefixEnd_3974433 680264819363651248769807 := by
  unfold tailWord_3974433
  simp only [CollatzResearch.WordTrace]
  refine ⟨144959480410315494961143953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96639653606876996640762635 144959480410315494961143953)
  ·
    refine ⟨108719610307736621220857965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144959480410315494961143953 108719610307736621220857965)
    ·
      refine ⟨40769853865401232957821737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108719610307736621220857965 40769853865401232957821737)
      ·
        refine ⟨30577390399050924718366303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40769853865401232957821737 30577390399050924718366303)
        ·
          refine ⟨45866085598576387077549455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30577390399050924718366303 45866085598576387077549455)
          ·
            refine ⟨68799128397864580616324183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45866085598576387077549455 68799128397864580616324183)
            ·
              refine ⟨103198692596796870924486275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68799128397864580616324183 103198692596796870924486275)
              ·
                refine ⟨154798038895195306386729413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103198692596796870924486275 154798038895195306386729413)
                ·
                  refine ⟨29024632292849119947511765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154798038895195306386729413 29024632292849119947511765)
                  ·
                    refine ⟨680264819363651248769807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29024632292849119947511765 680264819363651248769807)
                    ·
                      rfl

theorem cell23_3974433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3974433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974433 prefixEnd_3974433 := by exact prefixLift 3974433
  have htrace : WordTrace (prefixWord ++ tailWord_3974433) baseStart_3974433 baseEnd_3974433 := by
    simpa [prefixWord, tailWord_3974433, baseEnd_3974433] using wordTrace_append hprefix tailTrace_3974433
  have hstable : (prefixWord ++ tailWord_3974433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974433).length < 2 ^ (prefixWord ++ tailWord_3974433).sum := by decide
  have hdescent : baseEnd_3974433 < baseStart_3974433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974490 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_3974490 : Nat := 118140960795 + 3974490 * 2 ^ 59
def prefixEnd_3974490 : Nat := 4983230072969 + 3 ^ 40 * 3974490 * 2
def baseEnd_3974490 : Nat := 2040823726488260023296659

theorem tailTrace_3974490 : CollatzResearch.WordTrace tailWord_3974490 prefixEnd_3974490 2040823726488260023296659 := by
  unfold tailWord_3974490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36240389842777248423992231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96641039580739329130645949 36240389842777248423992231)
  ·
    refine ⟨54360584764165872635988347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36240389842777248423992231 54360584764165872635988347)
    ·
      refine ⟨81540877146248808953982521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54360584764165872635988347 81540877146248808953982521)
      ·
        refine ⟨61155657859686606715486891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81540877146248808953982521 61155657859686606715486891)
        ·
          refine ⟨91733486789529910073230337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61155657859686606715486891 91733486789529910073230337)
          ·
            refine ⟨68800115092147432554922753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91733486789529910073230337 68800115092147432554922753)
            ·
              refine ⟨51600086319110574416192065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68800115092147432554922753 51600086319110574416192065)
              ·
                refine ⟨38700064739332930812144049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51600086319110574416192065 38700064739332930812144049)
                ·
                  refine ⟨29025048554499698109108037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38700064739332930812144049 29025048554499698109108037)
                  ·
                    refine ⟨5442196603968693395457757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29025048554499698109108037 5442196603968693395457757)
                    ·
                      refine ⟨2040823726488260023296659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442196603968693395457757 2040823726488260023296659)
                      ·
                        rfl

theorem cell23_3974490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_3974490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974490 prefixEnd_3974490 := by exact prefixLift 3974490
  have htrace : WordTrace (prefixWord ++ tailWord_3974490) baseStart_3974490 baseEnd_3974490 := by
    simpa [prefixWord, tailWord_3974490, baseEnd_3974490] using wordTrace_append hprefix tailTrace_3974490
  have hstable : (prefixWord ++ tailWord_3974490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974490).length < 2 ^ (prefixWord ++ tailWord_3974490).sum := by decide
  have hdescent : baseEnd_3974490 < baseStart_3974490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974540 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_3974540 : Nat := 118140960795 + 3974540 * 2 ^ 59
def prefixEnd_3974540 : Nat := 4983230072969 + 3 ^ 40 * 3974540 * 2
def baseEnd_3974540 : Nat := 680283133506994942557143

theorem tailTrace_3974540 : CollatzResearch.WordTrace tailWord_3974540 prefixEnd_3974540 680283133506994942557143 := by
  unfold tailWord_3974540
  simp only [CollatzResearch.WordTrace]
  refine ⟨72481691510463926117644537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96642255347285234823526049 72481691510463926117644537)
  ·
    refine ⟨54361268632847944588233403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72481691510463926117644537 54361268632847944588233403)
    ·
      refine ⟨81541902949271916882350105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54361268632847944588233403 81541902949271916882350105)
      ·
        refine ⟨61156427211953937661762579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81541902949271916882350105 61156427211953937661762579)
        ·
          refine ⟨91734640817930906492643869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61156427211953937661762579 91734640817930906492643869)
          ·
            refine ⟨34400490306724089934741451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91734640817930906492643869 34400490306724089934741451)
            ·
              refine ⟨51600735460086134902112177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34400490306724089934741451 51600735460086134902112177)
              ·
                refine ⟨38700551595064601176584133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51600735460086134902112177 38700551595064601176584133)
                ·
                  refine ⟨7256353424074612720609525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38700551595064601176584133 7256353424074612720609525)
                  ·
                    refine ⟨680283133506994942557143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7256353424074612720609525 680283133506994942557143)
                    ·
                      rfl

theorem cell23_3974540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_3974540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974540 prefixEnd_3974540 := by exact prefixLift 3974540
  have htrace : WordTrace (prefixWord ++ tailWord_3974540) baseStart_3974540 baseEnd_3974540 := by
    simpa [prefixWord, tailWord_3974540, baseEnd_3974540] using wordTrace_append hprefix tailTrace_3974540
  have hstable : (prefixWord ++ tailWord_3974540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974540).length < 2 ^ (prefixWord ++ tailWord_3974540).sum := by decide
  have hdescent : baseEnd_3974540 < baseStart_3974540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974557 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3974557 : Nat := 118140960795 + 3974557 * 2 ^ 59
def prefixEnd_3974557 : Nat := 4983230072969 + 3 ^ 40 * 3974557 * 2
def baseEnd_3974557 : Nat := 680286043230703753719617

theorem tailTrace_3974557 : CollatzResearch.WordTrace tailWord_3974557 prefixEnd_3974557 680286043230703753719617 := by
  unfold tailWord_3974557
  simp only [CollatzResearch.WordTrace]
  refine ⟨144964003061866264138657925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96642668707910842759105283 144964003061866264138657925)
  ·
    refine ⟨27180750574099924525998361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144964003061866264138657925 27180750574099924525998361)
    ·
      refine ⟨20385562930574943394498771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27180750574099924525998361 20385562930574943394498771)
      ·
        refine ⟨30578344395862415091748157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20385562930574943394498771 30578344395862415091748157)
        ·
          refine ⟨11466879148448405659405559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30578344395862415091748157 11466879148448405659405559)
          ·
            refine ⟨17200318722672608489108339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466879148448405659405559 17200318722672608489108339)
            ·
              refine ⟨25800478084008912733662509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17200318722672608489108339 25800478084008912733662509)
              ·
                refine ⟨9675179281503342275123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25800478084008912733662509 9675179281503342275123441)
                ·
                  refine ⟨7256384461127506706342581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675179281503342275123441 7256384461127506706342581)
                  ·
                    refine ⟨680286043230703753719617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7256384461127506706342581 680286043230703753719617)
                    ·
                      rfl

theorem cell23_3974557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3974557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974557 prefixEnd_3974557 := by exact prefixLift 3974557
  have htrace : WordTrace (prefixWord ++ tailWord_3974557) baseStart_3974557 baseEnd_3974557 := by
    simpa [prefixWord, tailWord_3974557, baseEnd_3974557] using wordTrace_append hprefix tailTrace_3974557
  have hstable : (prefixWord ++ tailWord_3974557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974557).length < 2 ^ (prefixWord ++ tailWord_3974557).sum := by decide
  have hdescent : baseEnd_3974557 < baseStart_3974557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974577 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3974577 : Nat := 118140960795 + 3974577 * 2 ^ 59
def prefixEnd_3974577 : Nat := 4983230072969 + 3 ^ 40 * 3974577 * 2
def baseEnd_3974577 : Nat := 2040868399305201182908759

theorem tailTrace_3974577 : CollatzResearch.WordTrace tailWord_3974577 prefixEnd_3974577 2040868399305201182908759 := by
  unfold tailWord_3974577
  simp only [CollatzResearch.WordTrace]
  refine ⟨144964732521793807554385985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96643155014529205036257323 144964732521793807554385985)
  ·
    refine ⟨108723549391345355665789489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144964732521793807554385985 108723549391345355665789489)
    ·
      refine ⟨81542662043509016749342117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108723549391345355665789489 81542662043509016749342117)
      ·
        refine ⟨15289249133157940640501647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81542662043509016749342117 15289249133157940640501647)
        ·
          refine ⟨22933873699736910960752471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289249133157940640501647 22933873699736910960752471)
          ·
            refine ⟨34400810549605366441128707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22933873699736910960752471 34400810549605366441128707)
            ·
              refine ⟨51601215824408049661693061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34400810549605366441128707 51601215824408049661693061)
              ·
                refine ⟨9675227967076509311567449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51601215824408049661693061 9675227967076509311567449)
                ·
                  refine ⟨7256420975307381983675587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675227967076509311567449 7256420975307381983675587)
                  ·
                    refine ⟨10884631462961072975513381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256420975307381983675587 10884631462961072975513381)
                    ·
                      refine ⟨2040868399305201182908759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10884631462961072975513381 2040868399305201182908759)
                      ·
                        rfl

theorem cell23_3974577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3974577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974577 prefixEnd_3974577 := by exact prefixLift 3974577
  have htrace : WordTrace (prefixWord ++ tailWord_3974577) baseStart_3974577 baseEnd_3974577 := by
    simpa [prefixWord, tailWord_3974577, baseEnd_3974577] using wordTrace_append hprefix tailTrace_3974577
  have hstable : (prefixWord ++ tailWord_3974577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974577).length < 2 ^ (prefixWord ++ tailWord_3974577).sum := by decide
  have hdescent : baseEnd_3974577 < baseStart_3974577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974604 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_3974604 : Nat := 118140960795 + 3974604 * 2 ^ 59
def prefixEnd_3974604 : Nat := 4983230072969 + 3 ^ 40 * 3974604 * 2
def baseEnd_3974604 : Nat := 680294087760957525757045

theorem tailTrace_3974604 : CollatzResearch.WordTrace tailWord_3974604 prefixEnd_3974604 680294087760957525757045 := by
  unfold tailWord_3974604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72482858646347995582809433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96643811528463994110412577 72482858646347995582809433)
  ·
    refine ⟨54362143984760996687107075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72482858646347995582809433 54362143984760996687107075)
    ·
      refine ⟨81543215977141495030660613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54362143984760996687107075 81543215977141495030660613)
      ·
        refine ⟨15289352995714030318248865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81543215977141495030660613 15289352995714030318248865)
        ·
          refine ⟨11467014746785522738686649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15289352995714030318248865 11467014746785522738686649)
          ·
            refine ⟨8600261060089142054014987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11467014746785522738686649 8600261060089142054014987)
            ·
              refine ⟨12900391590133713081022481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600261060089142054014987 12900391590133713081022481)
              ·
                refine ⟨9675293692600284810766861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900391590133713081022481 9675293692600284810766861)
                ·
                  refine ⟨3628235134725106804037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9675293692600284810766861 3628235134725106804037573)
                  ·
                    refine ⟨680294087760957525757045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628235134725106804037573 680294087760957525757045)
                    ·
                      rfl

theorem cell23_3974604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_3974604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974604 prefixEnd_3974604 := by exact prefixLift 3974604
  have htrace : WordTrace (prefixWord ++ tailWord_3974604) baseStart_3974604 baseEnd_3974604 := by
    simpa [prefixWord, tailWord_3974604, baseEnd_3974604] using wordTrace_append hprefix tailTrace_3974604
  have hstable : (prefixWord ++ tailWord_3974604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974604).length < 2 ^ (prefixWord ++ tailWord_3974604).sum := by decide
  have hdescent : baseEnd_3974604 < baseStart_3974604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974621 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3974621 : Nat := 118140960795 + 3974621 * 2 ^ 59
def prefixEnd_3974621 : Nat := 4983230072969 + 3 ^ 40 * 3974621 * 2
def baseEnd_3974621 : Nat := 680296997484666336919519

theorem tailTrace_3974621 : CollatzResearch.WordTrace tailWord_3974621 prefixEnd_3974621 680296997484666336919519 := by
  unfold tailWord_3974621
  simp only [CollatzResearch.WordTrace]
  refine ⟨144966337333634403068987717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96644224889089602045991811 144966337333634403068987717)
  ·
    refine ⟨27181188250056450575435197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144966337333634403068987717 27181188250056450575435197)
    ·
      refine ⟨10192945593771168965788199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27181188250056450575435197 10192945593771168965788199)
      ·
        refine ⟨15289418390656753448682299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10192945593771168965788199 15289418390656753448682299)
        ·
          refine ⟨22934127585985130173023449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289418390656753448682299 22934127585985130173023449)
          ·
            refine ⟨17200595689488847629767587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22934127585985130173023449 17200595689488847629767587)
            ·
              refine ⟨25800893534233271444651381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17200595689488847629767587 25800893534233271444651381)
              ·
                refine ⟨2418833768834369197936067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25800893534233271444651381 2418833768834369197936067)
                ·
                  refine ⟨3628250653251553796904101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418833768834369197936067 3628250653251553796904101)
                  ·
                    refine ⟨680296997484666336919519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628250653251553796904101 680296997484666336919519)
                    ·
                      rfl

theorem cell23_3974621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3974621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974621 prefixEnd_3974621 := by exact prefixLift 3974621
  have htrace : WordTrace (prefixWord ++ tailWord_3974621) baseStart_3974621 baseEnd_3974621 := by
    simpa [prefixWord, tailWord_3974621, baseEnd_3974621] using wordTrace_append hprefix tailTrace_3974621
  have hstable : (prefixWord ++ tailWord_3974621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974621).length < 2 ^ (prefixWord ++ tailWord_3974621).sum := by decide
  have hdescent : baseEnd_3974621 < baseStart_3974621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974684 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3974684 : Nat := 118140960795 + 3974684 * 2 ^ 59
def prefixEnd_3974684 : Nat := 4983230072969 + 3 ^ 40 * 3974684 * 2
def baseEnd_3974684 : Nat := 2040923341735232264270767

theorem tailTrace_3974684 : CollatzResearch.WordTrace tailWord_3974684 prefixEnd_3974684 2040923341735232264270767 := by
  unfold tailWord_3974684
  simp only [CollatzResearch.WordTrace]
  refine ⟨72484317566203082414265553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96645756754937443219020737 72484317566203082414265553)
  ·
    refine ⟨54363238174652311810699165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72484317566203082414265553 54363238174652311810699165)
    ·
      refine ⟨20386214315494616929012187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54363238174652311810699165 20386214315494616929012187)
      ·
        refine ⟨30579321473241925393518281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20386214315494616929012187 30579321473241925393518281)
        ·
          refine ⟨22934491104931444045138711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30579321473241925393518281 22934491104931444045138711)
          ·
            refine ⟨34401736657397166067708067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22934491104931444045138711 34401736657397166067708067)
            ·
              refine ⟨51602604986095749101562101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34401736657397166067708067 51602604986095749101562101)
              ·
                refine ⟨4837744217446476478271447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51602604986095749101562101 4837744217446476478271447)
                ·
                  refine ⟨7256616326169714717407171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837744217446476478271447 7256616326169714717407171)
                  ·
                    refine ⟨10884924489254572076110757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256616326169714717407171 10884924489254572076110757)
                    ·
                      refine ⟨2040923341735232264270767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10884924489254572076110757 2040923341735232264270767)
                      ·
                        rfl

theorem cell23_3974684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3974684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974684 prefixEnd_3974684 := by exact prefixLift 3974684
  have htrace : WordTrace (prefixWord ++ tailWord_3974684) baseStart_3974684 baseEnd_3974684 := by
    simpa [prefixWord, tailWord_3974684, baseEnd_3974684] using wordTrace_append hprefix tailTrace_3974684
  have hstable : (prefixWord ++ tailWord_3974684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974684).length < 2 ^ (prefixWord ++ tailWord_3974684).sum := by decide
  have hdescent : baseEnd_3974684 < baseStart_3974684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974687 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3974687 : Nat := 118140960795 + 3974687 * 2 ^ 59
def prefixEnd_3974687 : Nat := 4983230072969 + 3 ^ 40 * 3974687 * 2
def baseEnd_3974687 : Nat := 2040924882177195752533253

theorem tailTrace_3974687 : CollatzResearch.WordTrace tailWord_3974687 prefixEnd_3974687 2040924882177195752533253 := by
  unfold tailWord_3974687
  simp only [CollatzResearch.WordTrace]
  refine ⟨144968744551395296340890315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96645829700930197560593543 144968744551395296340890315)
  ·
    refine ⟨217453116827092944511335473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144968744551395296340890315 217453116827092944511335473)
    ·
      refine ⟨163089837620319708383501605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217453116827092944511335473 163089837620319708383501605)
      ·
        refine ⟨30579344553809945321906551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163089837620319708383501605 30579344553809945321906551)
        ·
          refine ⟨45869016830714917982859827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30579344553809945321906551 45869016830714917982859827)
          ·
            refine ⟨68803525246072376974289741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45869016830714917982859827 68803525246072376974289741)
            ·
              refine ⟨25801321967277141365358653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68803525246072376974289741 25801321967277141365358653)
              ·
                refine ⟨9675495737728928012009495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25801321967277141365358653 9675495737728928012009495)
                ·
                  refine ⟨14513243606593392018014243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675495737728928012009495 14513243606593392018014243)
                  ·
                    refine ⟨21769865409890088027021365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14513243606593392018014243 21769865409890088027021365)
                    ·
                      refine ⟨2040924882177195752533253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21769865409890088027021365 2040924882177195752533253)
                      ·
                        rfl

theorem cell23_3974687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3974687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974687 prefixEnd_3974687 := by exact prefixLift 3974687
  have htrace : WordTrace (prefixWord ++ tailWord_3974687) baseStart_3974687 baseEnd_3974687 := by
    simpa [prefixWord, tailWord_3974687, baseEnd_3974687] using wordTrace_append hprefix tailTrace_3974687
  have hstable : (prefixWord ++ tailWord_3974687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974687).length < 2 ^ (prefixWord ++ tailWord_3974687).sum := by decide
  have hdescent : baseEnd_3974687 < baseStart_3974687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974707 : List Nat := [1, 1, 1, 2, 4, 4, 2, 8]
def baseStart_3974707 : Nat := 118140960795 + 3974707 * 2 ^ 59
def prefixEnd_3974707 : Nat := 4983230072969 + 3 ^ 40 * 3974707 * 2
def baseEnd_3974707 : Nat := 75590190807047617566043

theorem tailTrace_3974707 : CollatzResearch.WordTrace tailWord_3974707 prefixEnd_3974707 75590190807047617566043 := by
  unfold tailWord_3974707
  simp only [CollatzResearch.WordTrace]
  refine ⟨144969474011322839756618375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96646316007548559837745583 144969474011322839756618375)
  ·
    refine ⟨217454211016984259634927563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144969474011322839756618375 217454211016984259634927563)
    ·
      refine ⟨326181316525476389452391345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217454211016984259634927563 326181316525476389452391345)
      ·
        refine ⟨244635987394107292089293509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326181316525476389452391345 244635987394107292089293509)
        ·
          refine ⟨45869247636395117266742533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244635987394107292089293509 45869247636395117266742533)
          ·
            refine ⟨8600483931824084487514225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45869247636395117266742533 8600483931824084487514225)
            ·
              refine ⟨6450362948868063365635669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8600483931824084487514225 6450362948868063365635669)
              ·
                refine ⟨75590190807047617566043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6450362948868063365635669 75590190807047617566043)
                ·
                  rfl

theorem cell23_3974707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 8].length) (baseStart_3974707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974707 prefixEnd_3974707 := by exact prefixLift 3974707
  have htrace : WordTrace (prefixWord ++ tailWord_3974707) baseStart_3974707 baseEnd_3974707 := by
    simpa [prefixWord, tailWord_3974707, baseEnd_3974707] using wordTrace_append hprefix tailTrace_3974707
  have hstable : (prefixWord ++ tailWord_3974707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974707).length < 2 ^ (prefixWord ++ tailWord_3974707).sum := by decide
  have hdescent : baseEnd_3974707 < baseStart_3974707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974711 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 2, 4]
def baseStart_3974711 : Nat := 118140960795 + 3974711 * 2 ^ 59
def prefixEnd_3974711 : Nat := 4983230072969 + 3 ^ 40 * 3974711 * 2
def baseEnd_3974711 : Nat := 680312401904301219544381

theorem tailTrace_3974711 : CollatzResearch.WordTrace tailWord_3974711 prefixEnd_3974711 680312401904301219544381 := by
  unfold tailWord_3974711
  simp only [CollatzResearch.WordTrace]
  refine ⟨144969619903308348439763987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96646413268872232293175991 144969619903308348439763987)
  ·
    refine ⟨217454429854962522659645981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144969619903308348439763987 217454429854962522659645981)
    ·
      refine ⟨81545411195610945997367243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217454429854962522659645981 81545411195610945997367243)
      ·
        refine ⟨122318116793416418996050865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81545411195610945997367243 122318116793416418996050865)
        ·
          refine ⟨91738587595062314247038149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122318116793416418996050865 91738587595062314247038149)
          ·
            refine ⟨17200985174074183921319653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91738587595062314247038149 17200985174074183921319653)
            ·
              refine ⟨3225184720138909485247435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17200985174074183921319653 3225184720138909485247435)
              ·
                refine ⟨4837777080208364227871153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225184720138909485247435 4837777080208364227871153)
                ·
                  refine ⟨3628332810156273170903365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837777080208364227871153 3628332810156273170903365)
                  ·
                    refine ⟨680312401904301219544381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628332810156273170903365 680312401904301219544381)
                    ·
                      rfl

theorem cell23_3974711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_3974711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974711 prefixEnd_3974711 := by exact prefixLift 3974711
  have htrace : WordTrace (prefixWord ++ tailWord_3974711) baseStart_3974711 baseEnd_3974711 := by
    simpa [prefixWord, tailWord_3974711, baseEnd_3974711] using wordTrace_append hprefix tailTrace_3974711
  have hstable : (prefixWord ++ tailWord_3974711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974711).length < 2 ^ (prefixWord ++ tailWord_3974711).sum := by decide
  have hdescent : baseEnd_3974711 < baseStart_3974711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974738 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_3974738 : Nat := 118140960795 + 3974738 * 2 ^ 59
def prefixEnd_3974738 : Nat := 4983230072969 + 3 ^ 40 * 3974738 * 2
def baseEnd_3974738 : Nat := 2040951069690575052995519

theorem tailTrace_3974738 : CollatzResearch.WordTrace tailWord_3974738 prefixEnd_3974738 2040951069690575052995519 := by
  unfold tailWord_3974738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36242651168552633012749217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96647069782807021367331245 36242651168552633012749217)
  ·
    refine ⟨27181988376414474759561913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36242651168552633012749217 27181988376414474759561913)
    ·
      refine ⟨20386491282310856069671435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27181988376414474759561913 20386491282310856069671435)
      ·
        refine ⟨30579736923466284104507153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20386491282310856069671435 30579736923466284104507153)
        ·
          refine ⟨22934802692599713078380365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30579736923466284104507153 22934802692599713078380365)
          ·
            refine ⟨8600551009724892404392637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22934802692599713078380365 8600551009724892404392637)
            ·
              refine ⟨3225206628646834651647239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8600551009724892404392637 3225206628646834651647239)
              ·
                refine ⟨4837809942970251977470859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225206628646834651647239 4837809942970251977470859)
                ·
                  refine ⟨7256714914455377966206289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837809942970251977470859 7256714914455377966206289)
                  ·
                    refine ⟨5442536185841533474654717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256714914455377966206289 5442536185841533474654717)
                    ·
                      refine ⟨2040951069690575052995519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442536185841533474654717 2040951069690575052995519)
                      ·
                        rfl

theorem cell23_3974738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_3974738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974738 prefixEnd_3974738 := by exact prefixLift 3974738
  have htrace : WordTrace (prefixWord ++ tailWord_3974738) baseStart_3974738 baseEnd_3974738 := by
    simpa [prefixWord, tailWord_3974738, baseEnd_3974738] using wordTrace_append hprefix tailTrace_3974738
  have hstable : (prefixWord ++ tailWord_3974738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974738).length < 2 ^ (prefixWord ++ tailWord_3974738).sum := by decide
  have hdescent : baseEnd_3974738 < baseStart_3974738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974787 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_3974787 : Nat := 118140960795 + 3974787 * 2 ^ 59
def prefixEnd_3974787 : Nat := 4983230072969 + 3 ^ 40 * 3974787 * 2
def baseEnd_3974787 : Nat := 2040976230242645361282793

theorem tailTrace_3974787 : CollatzResearch.WordTrace tailWord_3974787 prefixEnd_3974787 2040976230242645361282793 := by
  unfold tailWord_3974787
  simp only [CollatzResearch.WordTrace]
  refine ⟨144972391851033013419530615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96648261234022008946353743 144972391851033013419530615)
  ·
    refine ⟨217458587776549520129295923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144972391851033013419530615 217458587776549520129295923)
    ·
      refine ⟨326187881664824280193943885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217458587776549520129295923 326187881664824280193943885)
      ·
        refine ⟨122320455624309105072728957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326187881664824280193943885 122320455624309105072728957)
        ·
          refine ⟨45870170859115914402273359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122320455624309105072728957 45870170859115914402273359)
          ·
            refine ⟨68805256288673871603410039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45870170859115914402273359 68805256288673871603410039)
            ·
              refine ⟨103207884433010807405115059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68805256288673871603410039 103207884433010807405115059)
              ·
                refine ⟨154811826649516211107672589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103207884433010807405115059 154811826649516211107672589)
                ·
                  refine ⟨58054434993568579165377221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154811826649516211107672589 58054434993568579165377221)
                  ·
                    refine ⟨10885206561294108593508229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58054434993568579165377221 10885206561294108593508229)
                    ·
                      refine ⟨2040976230242645361282793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10885206561294108593508229 2040976230242645361282793)
                      ·
                        rfl

theorem cell23_3974787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_3974787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974787 prefixEnd_3974787 := by exact prefixLift 3974787
  have htrace : WordTrace (prefixWord ++ tailWord_3974787) baseStart_3974787 baseEnd_3974787 := by
    simpa [prefixWord, tailWord_3974787, baseEnd_3974787] using wordTrace_append hprefix tailTrace_3974787
  have hstable : (prefixWord ++ tailWord_3974787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974787).length < 2 ^ (prefixWord ++ tailWord_3974787).sum := by decide
  have hdescent : baseEnd_3974787 < baseStart_3974787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974791 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_3974791 : Nat := 118140960795 + 3974791 * 2 ^ 59
def prefixEnd_3974791 : Nat := 4983230072969 + 3 ^ 40 * 3974791 * 2
def baseEnd_3974791 : Nat := 2040978284165263345632775

theorem tailTrace_3974791 : CollatzResearch.WordTrace tailWord_3974791 prefixEnd_3974791 2040978284165263345632775 := by
  unfold tailWord_3974791
  simp only [CollatzResearch.WordTrace]
  refine ⟨144972537743018522102676227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96648358495345681401784151 144972537743018522102676227)
  ·
    refine ⟨217458806614527783154014341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144972537743018522102676227 217458806614527783154014341)
    ·
      refine ⟨40773526240223959341377689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217458806614527783154014341 40773526240223959341377689)
      ·
        refine ⟨30580144680167969506033267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40773526240223959341377689 30580144680167969506033267)
        ·
          refine ⟨45870217020251954259049901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30580144680167969506033267 45870217020251954259049901)
          ·
            refine ⟨17201331382594482847143713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45870217020251954259049901 17201331382594482847143713)
            ·
              refine ⟨12900998536945862135357785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17201331382594482847143713 12900998536945862135357785)
              ·
                refine ⟨9675748902709396601518339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900998536945862135357785 9675748902709396601518339)
                ·
                  refine ⟨14513623354064094902277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675748902709396601518339 14513623354064094902277509)
                  ·
                    refine ⟨2721304378887017794177033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14513623354064094902277509 2721304378887017794177033)
                    ·
                      refine ⟨2040978284165263345632775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721304378887017794177033 2040978284165263345632775)
                      ·
                        rfl

theorem cell23_3974791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_3974791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974791 prefixEnd_3974791 := by exact prefixLift 3974791
  have htrace : WordTrace (prefixWord ++ tailWord_3974791) baseStart_3974791 baseEnd_3974791 := by
    simpa [prefixWord, tailWord_3974791, baseEnd_3974791] using wordTrace_append hprefix tailTrace_3974791
  have hstable : (prefixWord ++ tailWord_3974791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974791).length < 2 ^ (prefixWord ++ tailWord_3974791).sum := by decide
  have hdescent : baseEnd_3974791 < baseStart_3974791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974802 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3974802 : Nat := 118140960795 + 3974802 * 2 ^ 59
def prefixEnd_3974802 : Nat := 4983230072969 + 3 ^ 40 * 3974802 * 2
def baseEnd_3974802 : Nat := 2040983932452462802595225

theorem tailTrace_3974802 : CollatzResearch.WordTrace tailWord_3974802 prefixEnd_3974802 2040983932452462802595225 := by
  unfold tailWord_3974802
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243234736494667745331665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96648625963985780654217773 36243234736494667745331665)
  ·
    refine ⟨27182426052371000808998749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36243234736494667745331665 27182426052371000808998749)
    ·
      refine ⟨10193409769639125303374531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27182426052371000808998749 10193409769639125303374531)
      ·
        refine ⟨15290114654458687955061797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193409769639125303374531 15290114654458687955061797)
        ·
          refine ⟨2866896497711003991574087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15290114654458687955061797 2866896497711003991574087)
          ·
            refine ⟨4300344746566505987361131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866896497711003991574087 4300344746566505987361131)
            ·
              refine ⟨6450517119849758981041697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300344746566505987361131 6450517119849758981041697)
              ·
                refine ⟨4837887839887319235781273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6450517119849758981041697 4837887839887319235781273)
                ·
                  refine ⟨3628415879915489426835955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837887839887319235781273 3628415879915489426835955)
                  ·
                    refine ⟨5442623819873234140253933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628415879915489426835955 5442623819873234140253933)
                    ·
                      refine ⟨2040983932452462802595225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442623819873234140253933 2040983932452462802595225)
                      ·
                        rfl

theorem cell23_3974802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3974802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974802 prefixEnd_3974802 := by exact prefixLift 3974802
  have htrace : WordTrace (prefixWord ++ tailWord_3974802) baseStart_3974802 baseEnd_3974802 := by
    simpa [prefixWord, tailWord_3974802, baseEnd_3974802] using wordTrace_append hprefix tailTrace_3974802
  have hstable : (prefixWord ++ tailWord_3974802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974802).length < 2 ^ (prefixWord ++ tailWord_3974802).sum := by decide
  have hdescent : baseEnd_3974802 < baseStart_3974802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974808 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3974808 : Nat := 118140960795 + 3974808 * 2 ^ 59
def prefixEnd_3974808 : Nat := 4983230072969 + 3 ^ 40 * 3974808 * 2
def baseEnd_3974808 : Nat := 2040987013336389779120197

theorem tailTrace_3974808 : CollatzResearch.WordTrace tailWord_3974808 prefixEnd_3974808 2040987013336389779120197 := by
  unfold tailWord_3974808
  simp only [CollatzResearch.WordTrace]
  refine ⟨72486578891978467003022539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96648771855971289337363385 72486578891978467003022539)
  ·
    refine ⟨108729868337967700504533809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72486578891978467003022539 108729868337967700504533809)
    ·
      refine ⟨81547401253475775378400357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108729868337967700504533809 81547401253475775378400357)
      ·
        refine ⟨15290137735026707883450067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81547401253475775378400357 15290137735026707883450067)
        ·
          refine ⟨22935206602540061825175101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290137735026707883450067 22935206602540061825175101)
          ·
            refine ⟨8600702475952523184440663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22935206602540061825175101 8600702475952523184440663)
            ·
              refine ⟨12901053713928784776660995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600702475952523184440663 12901053713928784776660995)
              ·
                refine ⟨19351580570893177164991493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901053713928784776660995 19351580570893177164991493)
                ·
                  refine ⟨3628421357042470718435905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19351580570893177164991493 3628421357042470718435905)
                  ·
                    refine ⟨2721316017781853038826929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3628421357042470718435905 2721316017781853038826929)
                    ·
                      refine ⟨2040987013336389779120197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721316017781853038826929 2040987013336389779120197)
                      ·
                        rfl

theorem cell23_3974808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3974808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974808 prefixEnd_3974808 := by exact prefixLift 3974808
  have htrace : WordTrace (prefixWord ++ tailWord_3974808) baseStart_3974808 baseEnd_3974808 := by
    simpa [prefixWord, tailWord_3974808, baseEnd_3974808] using wordTrace_append hprefix tailTrace_3974808
  have hstable : (prefixWord ++ tailWord_3974808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974808).length < 2 ^ (prefixWord ++ tailWord_3974808).sum := by decide
  have hdescent : baseEnd_3974808 < baseStart_3974808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974844 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_3974844 : Nat := 118140960795 + 3974844 * 2 ^ 59
def prefixEnd_3974844 : Nat := 4983230072969 + 3 ^ 40 * 3974844 * 2
def baseEnd_3974844 : Nat := 680335166213317212756677

theorem tailTrace_3974844 : CollatzResearch.WordTrace tailWord_3974844 prefixEnd_3974844 680335166213317212756677 := by
  unfold tailWord_3974844
  simp only [CollatzResearch.WordTrace]
  refine ⟨72487235405913256077177793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96649647207884341436237057 72487235405913256077177793)
  ·
    refine ⟨54365426554434942057883345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72487235405913256077177793 54365426554434942057883345)
    ·
      refine ⟨40774069915826206543412509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54365426554434942057883345 40774069915826206543412509)
      ·
        refine ⟨15290276218434827453779691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40774069915826206543412509 15290276218434827453779691)
        ·
          refine ⟨22935414327652241180669537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290276218434827453779691 22935414327652241180669537)
          ·
            refine ⟨17201560745739180885502153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22935414327652241180669537 17201560745739180885502153)
            ·
              refine ⟨12901170559304385664126615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17201560745739180885502153 12901170559304385664126615)
              ·
                refine ⟨19351755838956578496189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901170559304385664126615 19351755838956578496189923)
                ·
                  refine ⟨29027633758434867744284885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19351755838956578496189923 29027633758434867744284885)
                  ·
                    refine ⟨680335166213317212756677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29027633758434867744284885 680335166213317212756677)
                    ·
                      rfl

theorem cell23_3974844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_3974844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974844 prefixEnd_3974844 := by exact prefixLift 3974844
  have htrace : WordTrace (prefixWord ++ tailWord_3974844) baseStart_3974844 baseEnd_3974844 := by
    simpa [prefixWord, tailWord_3974844, baseEnd_3974844] using wordTrace_append hprefix tailTrace_3974844
  have hstable : (prefixWord ++ tailWord_3974844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974844).length < 2 ^ (prefixWord ++ tailWord_3974844).sum := by decide
  have hdescent : baseEnd_3974844 < baseStart_3974844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974876 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3974876 : Nat := 118140960795 + 3974876 * 2 ^ 59
def prefixEnd_3974876 : Nat := 4983230072969 + 3 ^ 40 * 3974876 * 2
def baseEnd_3974876 : Nat := 2041021930020895513069885

theorem tailTrace_3974876 : CollatzResearch.WordTrace tailWord_3974876 prefixEnd_3974876 2041021930020895513069885 := by
  unfold tailWord_3974876
  simp only [CollatzResearch.WordTrace]
  refine ⟨72487818973855290809760241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96650425298473721079680321 72487818973855290809760241)
  ·
    refine ⟨54365864230391468107320181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72487818973855290809760241 54365864230391468107320181)
    ·
      refine ⟨5096799771599200135061267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54365864230391468107320181 5096799771599200135061267)
      ·
        refine ⟨7645199657398800202591901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096799771599200135061267 7645199657398800202591901)
        ·
          refine ⟨2866949871524550075971963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7645199657398800202591901 2866949871524550075971963)
          ·
            refine ⟨4300424807286825113957945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866949871524550075971963 4300424807286825113957945)
            ·
              refine ⟨3225318605465118835468459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300424807286825113957945 3225318605465118835468459)
              ·
                refine ⟨4837977908197678253202689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225318605465118835468459 4837977908197678253202689)
                ·
                  refine ⟨3628483431148258689902017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837977908197678253202689 3628483431148258689902017)
                  ·
                    refine ⟨2721362573361194017426513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3628483431148258689902017 2721362573361194017426513)
                    ·
                      refine ⟨2041021930020895513069885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721362573361194017426513 2041021930020895513069885)
                      ·
                        rfl

theorem cell23_3974876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3974876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974876 prefixEnd_3974876 := by exact prefixLift 3974876
  have htrace : WordTrace (prefixWord ++ tailWord_3974876) baseStart_3974876 baseEnd_3974876 := by
    simpa [prefixWord, tailWord_3974876, baseEnd_3974876] using wordTrace_append hprefix tailTrace_3974876
  have hstable : (prefixWord ++ tailWord_3974876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974876).length < 2 ^ (prefixWord ++ tailWord_3974876).sum := by decide
  have hdescent : baseEnd_3974876 < baseStart_3974876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974908 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_3974908 : Nat := 118140960795 + 3974908 * 2 ^ 59
def prefixEnd_3974908 : Nat := 4983230072969 + 3 ^ 40 * 3974908 * 2
def baseEnd_3974908 : Nat := 680346120467279795956579

theorem tailTrace_3974908 : CollatzResearch.WordTrace tailWord_3974908 prefixEnd_3974908 680346120467279795956579 := by
  unfold tailWord_3974908
  simp only [CollatzResearch.WordTrace]
  refine ⟨72488402541797325542342689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96651203389063100723123585 72488402541797325542342689)
  ·
    refine ⟨54366301906347994156757017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72488402541797325542342689 54366301906347994156757017)
    ·
      refine ⟨40774726429760995617567763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54366301906347994156757017 40774726429760995617567763)
      ·
        refine ⟨61162089644641493426351645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40774726429760995617567763 61162089644641493426351645)
        ·
          refine ⟨22935783616740560034881867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61162089644641493426351645 22935783616740560034881867)
          ·
            refine ⟨34403675425110840052322801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22935783616740560034881867 34403675425110840052322801)
            ·
              refine ⟨25802756568833130039242101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34403675425110840052322801 25802756568833130039242101)
              ·
                refine ⟨2419008428328105941178947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25802756568833130039242101 2419008428328105941178947)
                ·
                  refine ⟨3628512642492158911768421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419008428328105941178947 3628512642492158911768421)
                  ·
                    refine ⟨680346120467279795956579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628512642492158911768421 680346120467279795956579)
                    ·
                      rfl

theorem cell23_3974908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_3974908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974908 prefixEnd_3974908 := by exact prefixLift 3974908
  have htrace : WordTrace (prefixWord ++ tailWord_3974908) baseStart_3974908 baseEnd_3974908 := by
    simpa [prefixWord, tailWord_3974908, baseEnd_3974908] using wordTrace_append hprefix tailTrace_3974908
  have hstable : (prefixWord ++ tailWord_3974908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974908).length < 2 ^ (prefixWord ++ tailWord_3974908).sum := by decide
  have hdescent : baseEnd_3974908 < baseStart_3974908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974942 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3974942 : Nat := 118140960795 + 3974942 * 2 ^ 59
def prefixEnd_3974942 : Nat := 4983230072969 + 3 ^ 40 * 3974942 * 2
def baseEnd_3974942 : Nat := 680351939914697418281527

theorem tailTrace_3974942 : CollatzResearch.WordTrace tailWord_3974942 prefixEnd_3974942 680351939914697418281527 := by
  unfold tailWord_3974942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122255645683934361427885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96652030110314316594282053 18122255645683934361427885)
  ·
    refine ⟨6795845867131475385535457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18122255645683934361427885 6795845867131475385535457)
    ·
      refine ⟨5096884400348606539151593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6795845867131475385535457 5096884400348606539151593)
      ·
        refine ⟨3822663300261454904363695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5096884400348606539151593 3822663300261454904363695)
        ·
          refine ⟨5733994950392182356545543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822663300261454904363695 5733994950392182356545543)
          ·
            refine ⟨8600992425588273534818315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733994950392182356545543 8600992425588273534818315)
            ·
              refine ⟨12901488638382410302227473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600992425588273534818315 12901488638382410302227473)
              ·
                refine ⟨9676116478786807726670605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901488638382410302227473 9676116478786807726670605)
                ·
                  refine ⟨3628543679545052897501477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9676116478786807726670605 3628543679545052897501477)
                  ·
                    refine ⟨680351939914697418281527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628543679545052897501477 680351939914697418281527)
                    ·
                      rfl

theorem cell23_3974942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3974942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974942 prefixEnd_3974942 := by exact prefixLift 3974942
  have htrace : WordTrace (prefixWord ++ tailWord_3974942) baseStart_3974942 baseEnd_3974942 := by
    simpa [prefixWord, tailWord_3974942, baseEnd_3974942] using wordTrace_append hprefix tailTrace_3974942
  have hstable : (prefixWord ++ tailWord_3974942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974942).length < 2 ^ (prefixWord ++ tailWord_3974942).sum := by decide
  have hdescent : baseEnd_3974942 < baseStart_3974942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974944 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3974944 : Nat := 118140960795 + 3974944 * 2 ^ 59
def prefixEnd_3974944 : Nat := 4983230072969 + 3 ^ 40 * 3974944 * 2
def baseEnd_3974944 : Nat := 2041056846705401247019571

theorem tailTrace_3974944 : CollatzResearch.WordTrace tailWord_3974944 prefixEnd_3974944 2041056846705401247019571 := by
  unfold tailWord_3974944
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489059055732114616497943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96652078740976152821997257 72489059055732114616497943)
  ·
    refine ⟨108733588583598171924746915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72489059055732114616497943 108733588583598171924746915)
    ·
      refine ⟨163100382875397257887120373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108733588583598171924746915 163100382875397257887120373)
      ·
        refine ⟨15290660894568492926917535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163100382875397257887120373 15290660894568492926917535)
        ·
          refine ⟨22935991341852739390376303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290660894568492926917535 22935991341852739390376303)
          ·
            refine ⟨34403987012779109085564455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22935991341852739390376303 34403987012779109085564455)
            ·
              refine ⟨51605980519168663628346683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34403987012779109085564455 51605980519168663628346683)
              ·
                refine ⟨77408970778752995442520025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51605980519168663628346683 77408970778752995442520025)
                ·
                  refine ⟨58056728084064746581890019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77408970778752995442520025 58056728084064746581890019)
                  ·
                    refine ⟨87085092126097119872835029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58056728084064746581890019 87085092126097119872835029)
                    ·
                      refine ⟨2041056846705401247019571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87085092126097119872835029 2041056846705401247019571)
                      ·
                        rfl

theorem cell23_3974944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3974944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974944 prefixEnd_3974944 := by exact prefixLift 3974944
  have htrace : WordTrace (prefixWord ++ tailWord_3974944) baseStart_3974944 baseEnd_3974944 := by
    simpa [prefixWord, tailWord_3974944, baseEnd_3974944] using wordTrace_append hprefix tailTrace_3974944
  have hstable : (prefixWord ++ tailWord_3974944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974944).length < 2 ^ (prefixWord ++ tailWord_3974944).sum := by decide
  have hdescent : baseEnd_3974944 < baseStart_3974944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974948 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3974948 : Nat := 118140960795 + 3974948 * 2 ^ 59
def prefixEnd_3974948 : Nat := 4983230072969 + 3 ^ 40 * 3974948 * 2
def baseEnd_3974948 : Nat := 2041058900628019231369553

theorem tailTrace_3974948 : CollatzResearch.WordTrace tailWord_3974948 prefixEnd_3974948 2041058900628019231369553 := by
  unfold tailWord_3974948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489132001724868958070749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96652176002299825277427665 72489132001724868958070749)
  ·
    refine ⟨27183424500646825859276531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72489132001724868958070749 27183424500646825859276531)
    ·
      refine ⟨40775136750970238788914797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27183424500646825859276531 40775136750970238788914797)
      ·
        refine ⟨15290676281613839545843049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40775136750970238788914797 15290676281613839545843049)
        ·
          refine ⟨11468007211210379659382287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290676281613839545843049 11468007211210379659382287)
          ·
            refine ⟨17202010816815569489073431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468007211210379659382287 17202010816815569489073431)
            ·
              refine ⟨25803016225223354233610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17202010816815569489073431 25803016225223354233610147)
              ·
                refine ⟨38704524337835031350415221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25803016225223354233610147 38704524337835031350415221)
                ·
                  refine ⟨3628549156672034189101427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38704524337835031350415221 3628549156672034189101427)
                  ·
                    refine ⟨5442823735008051283652141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628549156672034189101427 5442823735008051283652141)
                    ·
                      refine ⟨2041058900628019231369553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442823735008051283652141 2041058900628019231369553)
                      ·
                        rfl

theorem cell23_3974948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3974948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974948 prefixEnd_3974948 := by exact prefixLift 3974948
  have htrace : WordTrace (prefixWord ++ tailWord_3974948) baseStart_3974948 baseEnd_3974948 := by
    simpa [prefixWord, tailWord_3974948, baseEnd_3974948] using wordTrace_append hprefix tailTrace_3974948
  have hstable : (prefixWord ++ tailWord_3974948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974948).length < 2 ^ (prefixWord ++ tailWord_3974948).sum := by decide
  have hdescent : baseEnd_3974948 < baseStart_3974948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974968 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_3974968 : Nat := 118140960795 + 3974968 * 2 ^ 59
def prefixEnd_3974968 : Nat := 4983230072969 + 3 ^ 40 * 3974968 * 2
def baseEnd_3974968 : Nat := 680356390080369717706487

theorem tailTrace_3974968 : CollatzResearch.WordTrace tailWord_3974968 prefixEnd_3974968 680356390080369717706487 := by
  unfold tailWord_3974968
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489496731688640665934779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96652662308918187554579705 72489496731688640665934779)
  ·
    refine ⟨108734245097532960998902169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72489496731688640665934779 108734245097532960998902169)
    ·
      refine ⟨81550683823149720749176627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108734245097532960998902169 81550683823149720749176627)
      ·
        refine ⟨122326025734724581123764941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81550683823149720749176627 122326025734724581123764941)
        ·
          refine ⟨45872259650521717921411853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122326025734724581123764941 45872259650521717921411853)
          ·
            refine ⟨17202097368945644220529445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45872259650521717921411853 17202097368945644220529445)
            ·
              refine ⟨3225393256677308291349271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17202097368945644220529445 3225393256677308291349271)
              ·
                refine ⟨4838089885015962437023907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225393256677308291349271 4838089885015962437023907)
                ·
                  refine ⟨7257134827523943655535861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838089885015962437023907 7257134827523943655535861)
                  ·
                    refine ⟨680356390080369717706487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7257134827523943655535861 680356390080369717706487)
                    ·
                      rfl

theorem cell23_3974968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_3974968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974968 prefixEnd_3974968 := by exact prefixLift 3974968
  have htrace : WordTrace (prefixWord ++ tailWord_3974968) baseStart_3974968 baseEnd_3974968 := by
    simpa [prefixWord, tailWord_3974968, baseEnd_3974968] using wordTrace_append hprefix tailTrace_3974968
  have hstable : (prefixWord ++ tailWord_3974968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974968).length < 2 ^ (prefixWord ++ tailWord_3974968).sum := by decide
  have hdescent : baseEnd_3974968 < baseStart_3974968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974981 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_3974981 : Nat := 118140960795 + 3974981 * 2 ^ 59
def prefixEnd_3974981 : Nat := 4983230072969 + 3 ^ 40 * 3974981 * 2
def baseEnd_3974981 : Nat := 680358615163205867418967

theorem tailTrace_3974981 : CollatzResearch.WordTrace tailWord_3974981 prefixEnd_3974981 680358615163205867418967 := by
  unfold tailWord_3974981
  simp only [CollatzResearch.WordTrace]
  refine ⟨144979467612330184552092797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96652978408220123034728531 144979467612330184552092797)
  ·
    refine ⟨54367300354623819207034799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144979467612330184552092797 54367300354623819207034799)
    ·
      refine ⟨81550950531935728810552199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54367300354623819207034799 81550950531935728810552199)
      ·
        refine ⟨122326425797903593215828299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81550950531935728810552199 122326425797903593215828299)
        ·
          refine ⟨183489638696855389823742449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122326425797903593215828299 183489638696855389823742449)
          ·
            refine ⟨137617229022641542367806837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183489638696855389823742449 137617229022641542367806837)
            ·
              refine ⟨12901615220872644596981891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137617229022641542367806837 12901615220872644596981891)
              ·
                refine ⟨19352422831308966895472837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901615220872644596981891 19352422831308966895472837)
                ·
                  refine ⟨3628579280870431292901157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19352422831308966895472837 3628579280870431292901157)
                  ·
                    refine ⟨680358615163205867418967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628579280870431292901157 680358615163205867418967)
                    ·
                      rfl

theorem cell23_3974981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_3974981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974981 prefixEnd_3974981 := by exact prefixLift 3974981
  have htrace : WordTrace (prefixWord ++ tailWord_3974981) baseStart_3974981 baseEnd_3974981 := by
    simpa [prefixWord, tailWord_3974981, baseEnd_3974981] using wordTrace_append hprefix tailTrace_3974981
  have hstable : (prefixWord ++ tailWord_3974981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974981).length < 2 ^ (prefixWord ++ tailWord_3974981).sum := by decide
  have hdescent : baseEnd_3974981 < baseStart_3974981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974982 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3974982 : Nat := 118140960795 + 3974982 * 2 ^ 59
def prefixEnd_3974982 : Nat := 4983230072969 + 3 ^ 40 * 3974982 * 2
def baseEnd_3974982 : Nat := 2041076358970272098344397

theorem tailTrace_3974982 : CollatzResearch.WordTrace tailWord_3974982 prefixEnd_3974982 2041076358970272098344397 := by
  unfold tailWord_3974982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530609502666455053839975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96653002723551041148586133 4530609502666455053839975)
  ·
    refine ⟨6795914253999682580759963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4530609502666455053839975 6795914253999682580759963)
    ·
      refine ⟨10193871380999523871139945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6795914253999682580759963 10193871380999523871139945)
      ·
        refine ⟨7645403535749642903354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10193871380999523871139945 7645403535749642903354959)
        ·
          refine ⟨11468105303624464355032439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645403535749642903354959 11468105303624464355032439)
          ·
            refine ⟨17202157955436696532548659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468105303624464355032439 17202157955436696532548659)
            ·
              refine ⟨25803236933155044798822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17202157955436696532548659 25803236933155044798822989)
              ·
                refine ⟨9676213849933141799558621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25803236933155044798822989 9676213849933141799558621)
                ·
                  refine ⟨3628580193724928174834483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9676213849933141799558621 3628580193724928174834483)
                  ·
                    refine ⟨5442870290587392262251725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628580193724928174834483 5442870290587392262251725)
                    ·
                      refine ⟨2041076358970272098344397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442870290587392262251725 2041076358970272098344397)
                      ·
                        rfl

theorem cell23_3974982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3974982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3974982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3974982 prefixEnd_3974982 := by exact prefixLift 3974982
  have htrace : WordTrace (prefixWord ++ tailWord_3974982) baseStart_3974982 baseEnd_3974982 := by
    simpa [prefixWord, tailWord_3974982, baseEnd_3974982] using wordTrace_append hprefix tailTrace_3974982
  have hstable : (prefixWord ++ tailWord_3974982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974982).length < 2 ^ (prefixWord ++ tailWord_3974982).sum := by decide
  have hdescent : baseEnd_3974982 < baseStart_3974982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975008 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3975008 : Nat := 118140960795 + 3975008 * 2 ^ 59
def prefixEnd_3975008 : Nat := 4983230072969 + 3 ^ 40 * 3975008 * 2
def baseEnd_3975008 : Nat := 2041089709467288996619277

theorem tailTrace_3975008 : CollatzResearch.WordTrace tailWord_3975008 prefixEnd_3975008 2041089709467288996619277 := by
  unfold tailWord_3975008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72490226191616184081662839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96653634922154912108883785 72490226191616184081662839)
  ·
    refine ⟨108735339287424276122494259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72490226191616184081662839 108735339287424276122494259)
    ·
      refine ⟨163103008931136414183741389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108735339287424276122494259 163103008931136414183741389)
      ·
        refine ⟨61163628349176155318903021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163103008931136414183741389 61163628349176155318903021)
        ·
          refine ⟨22936360630941058244588633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61163628349176155318903021 22936360630941058244588633)
          ·
            refine ⟨17202270473205793683441475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22936360630941058244588633 17202270473205793683441475)
            ·
              refine ⟨25803405709808690525162213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17202270473205793683441475 25803405709808690525162213)
              ·
                refine ⟨4838138570589129473467915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25803405709808690525162213 4838138570589129473467915)
                ·
                  refine ⟨7257207855883694210201873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838138570589129473467915 7257207855883694210201873)
                  ·
                    refine ⟨5442905891912770657651405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257207855883694210201873 5442905891912770657651405)
                    ·
                      refine ⟨2041089709467288996619277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5442905891912770657651405 2041089709467288996619277)
                      ·
                        rfl

theorem cell23_3975008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3975008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975008 prefixEnd_3975008 := by exact prefixLift 3975008
  have htrace : WordTrace (prefixWord ++ tailWord_3975008) baseStart_3975008 baseEnd_3975008 := by
    simpa [prefixWord, tailWord_3975008, baseEnd_3975008] using wordTrace_append hprefix tailTrace_3975008
  have hstable : (prefixWord ++ tailWord_3975008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975008).length < 2 ^ (prefixWord ++ tailWord_3975008).sum := by decide
  have hdescent : baseEnd_3975008 < baseStart_3975008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975011 : List Nat := [1, 1, 1, 5, 4, 1, 1, 9]
def baseStart_3975011 : Nat := 118140960795 + 3975011 * 2 ^ 59
def prefixEnd_3975011 : Nat := 4983230072969 + 3 ^ 40 * 3975011 * 2
def baseEnd_3975011 : Nat := 75595972218861203143769

theorem tailTrace_3975011 : CollatzResearch.WordTrace tailWord_3975011 prefixEnd_3975011 75595972218861203143769 := by
  unfold tailWord_3975011
  simp only [CollatzResearch.WordTrace]
  refine ⟨144980561802221499675684887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96653707868147666450456591 144980561802221499675684887)
  ·
    refine ⟨217470842703332249513527331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144980561802221499675684887 217470842703332249513527331)
    ·
      refine ⟨326206264054998374270290997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217470842703332249513527331 326206264054998374270290997)
      ·
        refine ⟨30581837255156097587839781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326206264054998374270290997 30581837255156097587839781)
        ·
          refine ⟨5734094485341768297719959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30581837255156097587839781 5734094485341768297719959)
          ·
            refine ⟨8601141728012652446579939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734094485341768297719959 8601141728012652446579939)
            ·
              refine ⟨12901712592018978669869909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601141728012652446579939 12901712592018978669869909)
              ·
                refine ⟨75595972218861203143769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12901712592018978669869909 75595972218861203143769)
                ·
                  rfl

theorem cell23_3975011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 9].length) (baseStart_3975011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975011 prefixEnd_3975011 := by exact prefixLift 3975011
  have htrace : WordTrace (prefixWord ++ tailWord_3975011) baseStart_3975011 baseEnd_3975011 := by
    simpa [prefixWord, tailWord_3975011, baseEnd_3975011] using wordTrace_append hprefix tailTrace_3975011
  have hstable : (prefixWord ++ tailWord_3975011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975011).length < 2 ^ (prefixWord ++ tailWord_3975011).sum := by decide
  have hdescent : baseEnd_3975011 < baseStart_3975011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975024 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_3975024 : Nat := 118140960795 + 3975024 * 2 ^ 59
def prefixEnd_3975024 : Nat := 4983230072969 + 3 ^ 40 * 3975024 * 2
def baseEnd_3975024 : Nat := 680365975052586978006401

theorem tailTrace_3975024 : CollatzResearch.WordTrace tailWord_3975024 prefixEnd_3975024 680365975052586978006401 := by
  unfold tailWord_3975024
  simp only [CollatzResearch.WordTrace]
  refine ⟨72490517975587201447954063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96654023967449601930605417 72490517975587201447954063)
  ·
    refine ⟨108735776963380802171931095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72490517975587201447954063 108735776963380802171931095)
    ·
      refine ⟨163103665445071203257896643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108735776963380802171931095 163103665445071203257896643)
      ·
        refine ⟨244655498167606804886844965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163103665445071203257896643 244655498167606804886844965)
        ·
          refine ⟨45872905906426275916283431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244655498167606804886844965 45872905906426275916283431)
          ·
            refine ⟨68809358859639413874425147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45872905906426275916283431 68809358859639413874425147)
            ·
              refine ⟨103214038289459120811637721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68809358859639413874425147 103214038289459120811637721)
              ·
                refine ⟨77410528717094340608728291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103214038289459120811637721 77410528717094340608728291)
                ·
                  refine ⟨116115793075641510913092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77410528717094340608728291 116115793075641510913092437)
                  ·
                    refine ⟨680365975052586978006401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116115793075641510913092437 680365975052586978006401)
                    ·
                      rfl

theorem cell23_3975024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_3975024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975024 prefixEnd_3975024 := by exact prefixLift 3975024
  have htrace : WordTrace (prefixWord ++ tailWord_3975024) baseStart_3975024 baseEnd_3975024 := by
    simpa [prefixWord, tailWord_3975024, baseEnd_3975024] using wordTrace_append hprefix tailTrace_3975024
  have hstable : (prefixWord ++ tailWord_3975024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975024).length < 2 ^ (prefixWord ++ tailWord_3975024).sum := by decide
  have hdescent : baseEnd_3975024 < baseStart_3975024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975065 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 1, 3, 2]
def baseStart_3975065 : Nat := 118140960795 + 3975065 * 2 ^ 59
def prefixEnd_3975065 : Nat := 4983230072969 + 3 ^ 40 * 3975065 * 2
def baseEnd_3975065 : Nat := 2041118977864595273606515

theorem tailTrace_3975065 : CollatzResearch.WordTrace tailWord_3975065 prefixEnd_3975065 2041118977864595273606515 := by
  unfold tailWord_3975065
  simp only [CollatzResearch.WordTrace]
  refine ⟨144982531344025866898150649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96655020896017244598767099 144982531344025866898150649)
  ·
    refine ⟨108736898508019400173612987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144982531344025866898150649 108736898508019400173612987)
    ·
      refine ⟨163105347762029100260419481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108736898508019400173612987 163105347762029100260419481)
      ·
        refine ⟨122329010821521825195314611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163105347762029100260419481 122329010821521825195314611)
        ·
          refine ⟨183493516232282737792971917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122329010821521825195314611 183493516232282737792971917)
          ·
            refine ⟨68810068587106026672364469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183493516232282737792971917 68810068587106026672364469)
            ·
              refine ⟨6450943930041190000534169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68810068587106026672364469 6450943930041190000534169)
              ·
                refine ⟨4838207947530892500400627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6450943930041190000534169 4838207947530892500400627)
                ·
                  refine ⟨7257311921296338750600941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838207947530892500400627 7257311921296338750600941)
                  ·
                    refine ⟨2721491970486127031475353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7257311921296338750600941 2721491970486127031475353)
                    ·
                      refine ⟨2041118977864595273606515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721491970486127031475353 2041118977864595273606515)
                      ·
                        rfl

theorem cell23_3975065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_3975065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975065 prefixEnd_3975065 := by exact prefixLift 3975065
  have htrace : WordTrace (prefixWord ++ tailWord_3975065) baseStart_3975065 baseEnd_3975065 := by
    simpa [prefixWord, tailWord_3975065, baseEnd_3975065] using wordTrace_append hprefix tailTrace_3975065
  have hstable : (prefixWord ++ tailWord_3975065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975065).length < 2 ^ (prefixWord ++ tailWord_3975065).sum := by decide
  have hdescent : baseEnd_3975065 < baseStart_3975065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975091 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_3975091 : Nat := 118140960795 + 3975091 * 2 ^ 59
def prefixEnd_3975091 : Nat := 4983230072969 + 3 ^ 40 * 3975091 * 2
def baseEnd_3975091 : Nat := 2041132328361612171881395

theorem tailTrace_3975091 : CollatzResearch.WordTrace tailWord_3975091 prefixEnd_3975091 2041132328361612171881395 := by
  unfold tailWord_3975091
  simp only [CollatzResearch.WordTrace]
  refine ⟨144983479641931673338597127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96655653094621115559064751 144983479641931673338597127)
  ·
    refine ⟨217475219462897510007895691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144983479641931673338597127 217475219462897510007895691)
    ·
      refine ⟨326212829194346265011843537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217475219462897510007895691 326212829194346265011843537)
      ·
        refine ⟨244659621895759698758882653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326212829194346265011843537 244659621895759698758882653)
        ·
          refine ⟨91747358210909887034580995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244659621895759698758882653 91747358210909887034580995)
          ·
            refine ⟨137621037316364830551871493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91747358210909887034580995 137621037316364830551871493)
            ·
              refine ⟨25803944496818405728475905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137621037316364830551871493 25803944496818405728475905)
              ·
                refine ⟨19352958372613804296356929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25803944496818405728475905 19352958372613804296356929)
                ·
                  refine ⟨14514718779460353222267697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19352958372613804296356929 14514718779460353222267697)
                  ·
                    refine ⟨10886039084595264916700773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14514718779460353222267697 10886039084595264916700773)
                    ·
                      refine ⟨2041132328361612171881395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10886039084595264916700773 2041132328361612171881395)
                      ·
                        rfl

theorem cell23_3975091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_3975091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975091 prefixEnd_3975091 := by exact prefixLift 3975091
  have htrace : WordTrace (prefixWord ++ tailWord_3975091) baseStart_3975091 baseEnd_3975091 := by
    simpa [prefixWord, tailWord_3975091, baseEnd_3975091] using wordTrace_append hprefix tailTrace_3975091
  have hstable : (prefixWord ++ tailWord_3975091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975091).length < 2 ^ (prefixWord ++ tailWord_3975091).sum := by decide
  have hdescent : baseEnd_3975091 < baseStart_3975091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975112 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_3975112 : Nat := 118140960795 + 3975112 * 2 ^ 59
def prefixEnd_3975112 : Nat := 4983230072969 + 3 ^ 40 * 3975112 * 2
def baseEnd_3975112 : Nat := 2041143111455356589718799

theorem tailTrace_3975112 : CollatzResearch.WordTrace tailWord_3975112 prefixEnd_3975112 2041143111455356589718799 := by
  unfold tailWord_3975112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72492122787427796962555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96656163716570395950074393 72492122787427796962555795)
  ·
    refine ⟨108738184181141695443833693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72492122787427796962555795 108738184181141695443833693)
    ·
      refine ⟨40776819067928135791437635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108738184181141695443833693 40776819067928135791437635)
      ·
        refine ⟨61165228601892203687156453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40776819067928135791437635 61165228601892203687156453)
        ·
          refine ⟨11468480362854788191341835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61165228601892203687156453 11468480362854788191341835)
          ·
            refine ⟨17202720544282182287012753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468480362854788191341835 17202720544282182287012753)
            ·
              refine ⟨12902040408211636715259565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17202720544282182287012753 12902040408211636715259565)
              ·
                refine ⟨4838265153079363768222337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12902040408211636715259565 4838265153079363768222337)
                ·
                  refine ⟨3628698864809522826166753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838265153079363768222337 3628698864809522826166753)
                  ·
                    refine ⟨2721524148607142119625065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3628698864809522826166753 2721524148607142119625065)
                    ·
                      refine ⟨2041143111455356589718799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721524148607142119625065 2041143111455356589718799)
                      ·
                        rfl

theorem cell23_3975112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_3975112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975112 prefixEnd_3975112 := by exact prefixLift 3975112
  have htrace : WordTrace (prefixWord ++ tailWord_3975112) baseStart_3975112 baseEnd_3975112 := by
    simpa [prefixWord, tailWord_3975112, baseEnd_3975112] using wordTrace_append hprefix tailTrace_3975112
  have hstable : (prefixWord ++ tailWord_3975112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975112).length < 2 ^ (prefixWord ++ tailWord_3975112).sum := by decide
  have hdescent : baseEnd_3975112 < baseStart_3975112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975135 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 5]
def baseStart_3975135 : Nat := 118140960795 + 3975135 * 2 ^ 59
def prefixEnd_3975135 : Nat := 4983230072969 + 3 ^ 40 * 3975135 * 2
def baseEnd_3975135 : Nat := 226794991278934444414577

theorem tailTrace_3975135 : CollatzResearch.WordTrace tailWord_3975135 prefixEnd_3975135 226794991278934444414577 := by
  unfold tailWord_3975135
  simp only [CollatzResearch.WordTrace]
  refine ⟨144985084453772268853198859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96656722969181512568799239 144985084453772268853198859)
  ·
    refine ⟨217477626680658403279798289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144985084453772268853198859 217477626680658403279798289)
    ·
      refine ⟨163108220010493802459848717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217477626680658403279798289 163108220010493802459848717)
      ·
        refine ⟨61165582503935175922443269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163108220010493802459848717 61165582503935175922443269)
        ·
          refine ⟨11468546719487845485458113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61165582503935175922443269 11468546719487845485458113)
          ·
            refine ⟨8601410039615884114093585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11468546719487845485458113 8601410039615884114093585)
            ·
              refine ⟨6451057529711913085570189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601410039615884114093585 6451057529711913085570189)
              ·
                refine ⟨2419146573641967407088821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6451057529711913085570189 2419146573641967407088821)
                ·
                  refine ⟨226794991278934444414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419146573641967407088821 226794991278934444414577)
                  ·
                    rfl

theorem cell23_3975135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 5].length) (baseStart_3975135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975135 prefixEnd_3975135 := by exact prefixLift 3975135
  have htrace : WordTrace (prefixWord ++ tailWord_3975135) baseStart_3975135 baseEnd_3975135 := by
    simpa [prefixWord, tailWord_3975135, baseEnd_3975135] using wordTrace_append hprefix tailTrace_3975135
  have hstable : (prefixWord ++ tailWord_3975135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975135).length < 2 ^ (prefixWord ++ tailWord_3975135).sum := by decide
  have hdescent : baseEnd_3975135 < baseStart_3975135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975168 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2]
def baseStart_3975168 : Nat := 118140960795 + 3975168 * 2 ^ 59
def prefixEnd_3975168 : Nat := 4983230072969 + 3 ^ 40 * 3975168 * 2
def baseEnd_3975168 : Nat := 2041171866372008370618541

theorem tailTrace_3975168 : CollatzResearch.WordTrace tailWord_3975168 prefixEnd_3975168 2041171866372008370618541 := by
  unfold tailWord_3975168
  simp only [CollatzResearch.WordTrace]
  refine ⟨72493144031326357744575079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96657525375101810326100105 72493144031326357744575079)
  ·
    refine ⟨108739716046989536616862619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72493144031326357744575079 108739716046989536616862619)
    ·
      refine ⟨163109574070484304925293929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108739716046989536616862619 163109574070484304925293929)
      ·
        refine ⟨122332180552863228693970447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163109574070484304925293929 122332180552863228693970447)
        ·
          refine ⟨183498270829294843040955671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122332180552863228693970447 183498270829294843040955671)
          ·
            refine ⟨275247406243942264561433507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183498270829294843040955671 275247406243942264561433507)
            ·
              refine ⟨412871109365913396842150261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275247406243942264561433507 412871109365913396842150261)
              ·
                refine ⟨38706666503054380953951587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412871109365913396842150261 38706666503054380953951587)
                ·
                  refine ⟨58059999754581571430927381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38706666503054380953951587 58059999754581571430927381)
                  ·
                    refine ⟨2721562488496011160824721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58059999754581571430927381 2721562488496011160824721)
                    ·
                      refine ⟨2041171866372008370618541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721562488496011160824721 2041171866372008370618541)
                      ·
                        rfl

theorem cell23_3975168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_3975168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975168 prefixEnd_3975168 := by exact prefixLift 3975168
  have htrace : WordTrace (prefixWord ++ tailWord_3975168) baseStart_3975168 baseEnd_3975168 := by
    simpa [prefixWord, tailWord_3975168, baseEnd_3975168] using wordTrace_append hprefix tailTrace_3975168
  have hstable : (prefixWord ++ tailWord_3975168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975168).length < 2 ^ (prefixWord ++ tailWord_3975168).sum := by decide
  have hdescent : baseEnd_3975168 < baseStart_3975168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975195 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 1, 4]
def baseStart_3975195 : Nat := 118140960795 + 3975195 * 2 ^ 59
def prefixEnd_3975195 : Nat := 4983230072969 + 3 ^ 40 * 3975195 * 2
def baseEnd_3975195 : Nat := 680395243449893254993639

theorem tailTrace_3975195 : CollatzResearch.WordTrace tailWord_3975195 prefixEnd_3975195 680395243449893254993639 := by
  unfold tailWord_3975195
  simp only [CollatzResearch.WordTrace]
  refine ⟨144987272833554899100383039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96658181889036599400255359 144987272833554899100383039)
  ·
    refine ⟨217480909250332348650574559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144987272833554899100383039 217480909250332348650574559)
    ·
      refine ⟨326221363875498522975861839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217480909250332348650574559 326221363875498522975861839)
      ·
        refine ⟨489332045813247784463792759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326221363875498522975861839 489332045813247784463792759)
        ·
          refine ⟨733998068719871676695689139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489332045813247784463792759 733998068719871676695689139)
          ·
            refine ⟨1100997103079807515043533709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733998068719871676695689139 1100997103079807515043533709)
            ·
              refine ⟨412873913654927818141325141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1100997103079807515043533709 412873913654927818141325141)
              ·
                refine ⟨2419183087821842684421827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 412873913654927818141325141 2419183087821842684421827)
                ·
                  refine ⟨3628774631732764026632741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419183087821842684421827 3628774631732764026632741)
                  ·
                    refine ⟨680395243449893254993639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628774631732764026632741 680395243449893254993639)
                    ·
                      rfl

theorem cell23_3975195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 4].length) (baseStart_3975195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975195 prefixEnd_3975195 := by exact prefixLift 3975195
  have htrace : WordTrace (prefixWord ++ tailWord_3975195) baseStart_3975195 baseEnd_3975195 := by
    simpa [prefixWord, tailWord_3975195, baseEnd_3975195] using wordTrace_append hprefix tailTrace_3975195
  have hstable : (prefixWord ++ tailWord_3975195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975195).length < 2 ^ (prefixWord ++ tailWord_3975195).sum := by decide
  have hdescent : baseEnd_3975195 < baseStart_3975195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975205 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3975205 : Nat := 118140960795 + 3975205 * 2 ^ 59
def prefixEnd_3975205 : Nat := 4983230072969 + 3 ^ 40 * 3975205 * 2
def baseEnd_3975205 : Nat := 2041190865156224725855871

theorem tailTrace_3975205 : CollatzResearch.WordTrace tailWord_3975205 prefixEnd_3975205 2041190865156224725855871 := by
  unfold tailWord_3975205
  simp only [CollatzResearch.WordTrace]
  refine ⟨144987637563518670808247069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96658425042345780538831379 144987637563518670808247069)
  ·
    refine ⟨54370364086319501553092651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144987637563518670808247069 54370364086319501553092651)
    ·
      refine ⟨81555546129479252329638977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54370364086319501553092651 81555546129479252329638977)
      ·
        refine ⟨61166659597109439247229233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81555546129479252329638977 61166659597109439247229233)
        ·
          refine ⟨45874994697832079435421925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61166659597109439247229233 45874994697832079435421925)
          ·
            refine ⟨8601561505843514894141611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45874994697832079435421925 8601561505843514894141611)
            ·
              refine ⟨12902342258765272341212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601561505843514894141611 12902342258765272341212417)
              ·
                refine ⟨9676756694073954255909313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12902342258765272341212417 9676756694073954255909313)
                ·
                  refine ⟨7257567520555465691931985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676756694073954255909313 7257567520555465691931985)
                  ·
                    refine ⟨5443175640416599268948989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257567520555465691931985 5443175640416599268948989)
                    ·
                      refine ⟨2041190865156224725855871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5443175640416599268948989 2041190865156224725855871)
                      ·
                        rfl

theorem cell23_3975205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3975205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975205 prefixEnd_3975205 := by exact prefixLift 3975205
  have htrace : WordTrace (prefixWord ++ tailWord_3975205) baseStart_3975205 baseEnd_3975205 := by
    simpa [prefixWord, tailWord_3975205, baseEnd_3975205] using wordTrace_append hprefix tailTrace_3975205
  have hstable : (prefixWord ++ tailWord_3975205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975205).length < 2 ^ (prefixWord ++ tailWord_3975205).sum := by decide
  have hdescent : baseEnd_3975205 < baseStart_3975205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975211 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_3975211 : Nat := 118140960795 + 3975211 * 2 ^ 59
def prefixEnd_3975211 : Nat := 4983230072969 + 3 ^ 40 * 3975211 * 2
def baseEnd_3975211 : Nat := 2041193946040151702380843

theorem tailTrace_3975211 : CollatzResearch.WordTrace tailWord_3975211 prefixEnd_3975211 2041193946040151702380843 := by
  unfold tailWord_3975211
  simp only [CollatzResearch.WordTrace]
  refine ⟨144987856401496933832965487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96658570934331289221976991 144987856401496933832965487)
  ·
    refine ⟨217481784602245400749448231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144987856401496933832965487 217481784602245400749448231)
    ·
      refine ⟨326222676903368101124172347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217481784602245400749448231 326222676903368101124172347)
      ·
        refine ⟨489334015355052151686258521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326222676903368101124172347 489334015355052151686258521)
        ·
          refine ⟨367000511516289113764693891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489334015355052151686258521 367000511516289113764693891)
          ·
            refine ⟨550500767274433670647040837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367000511516289113764693891 550500767274433670647040837)
            ·
              refine ⟨103218893863956313246320157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550500767274433670647040837 103218893863956313246320157)
              ·
                refine ⟨38707085198983617467370059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103218893863956313246320157 38707085198983617467370059)
                ·
                  refine ⟨58060627798475426201055089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38707085198983617467370059 58060627798475426201055089)
                  ·
                    refine ⟨43545470848856569650791317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58060627798475426201055089 43545470848856569650791317)
                    ·
                      refine ⟨2041193946040151702380843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43545470848856569650791317 2041193946040151702380843)
                      ·
                        rfl

theorem cell23_3975211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_3975211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975211 prefixEnd_3975211 := by exact prefixLift 3975211
  have htrace : WordTrace (prefixWord ++ tailWord_3975211) baseStart_3975211 baseEnd_3975211 := by
    simpa [prefixWord, tailWord_3975211, baseEnd_3975211] using wordTrace_append hprefix tailTrace_3975211
  have hstable : (prefixWord ++ tailWord_3975211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975211).length < 2 ^ (prefixWord ++ tailWord_3975211).sum := by decide
  have hdescent : baseEnd_3975211 < baseStart_3975211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975225 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 6]
def baseStart_3975225 : Nat := 118140960795 + 3975225 * 2 ^ 59
def prefixEnd_3975225 : Nat := 4983230072969 + 3 ^ 40 * 3975225 * 2
def baseEnd_3975225 : Nat := 226800126085479405289531

theorem tailTrace_3975225 : CollatzResearch.WordTrace tailWord_3975225 prefixEnd_3975225 226800126085479405289531 := by
  unfold tailWord_3975225
  simp only [CollatzResearch.WordTrace]
  refine ⟨144988367023446214223975129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96658911348964142815983419 144988367023446214223975129)
  ·
    refine ⟨108741275267584660667981347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144988367023446214223975129 108741275267584660667981347)
    ·
      refine ⟨163111912901376991001972021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108741275267584660667981347 163111912901376991001972021)
      ·
        refine ⟨15291741834504092906434877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163111912901376991001972021 15291741834504092906434877)
        ·
          refine ⟨5734403187939034839913079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15291741834504092906434877 5734403187939034839913079)
          ·
            refine ⟨8601604781908552259869619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734403187939034839913079 8601604781908552259869619)
            ·
              refine ⟨12902407172862828389804429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601604781908552259869619 12902407172862828389804429)
              ·
                refine ⟨4838402689823560646176661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12902407172862828389804429 4838402689823560646176661)
                ·
                  refine ⟨226800126085479405289531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4838402689823560646176661 226800126085479405289531)
                  ·
                    rfl

theorem cell23_3975225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_3975225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975225 prefixEnd_3975225 := by exact prefixLift 3975225
  have htrace : WordTrace (prefixWord ++ tailWord_3975225) baseStart_3975225 baseEnd_3975225 := by
    simpa [prefixWord, tailWord_3975225, baseEnd_3975225] using wordTrace_append hprefix tailTrace_3975225
  have hstable : (prefixWord ++ tailWord_3975225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975225).length < 2 ^ (prefixWord ++ tailWord_3975225).sum := by decide
  have hdescent : baseEnd_3975225 < baseStart_3975225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975251 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 10]
def baseStart_3975251 : Nat := 118140960795 + 3975251 * 2 ^ 59
def prefixEnd_3975251 : Nat := 4983230072969 + 3 ^ 40 * 3975251 * 2
def baseEnd_3975251 : Nat := 680404828422110515293553

theorem tailTrace_3975251 : CollatzResearch.WordTrace tailWord_3975251 prefixEnd_3975251 680404828422110515293553 := by
  unfold tailWord_3975251
  simp only [CollatzResearch.WordTrace]
  refine ⟨144989315321352020664421607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96659543547568013776281071 144989315321352020664421607)
  ·
    refine ⟨217483972982028030996632411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144989315321352020664421607 217483972982028030996632411)
    ·
      refine ⟨326225959473042046494948617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217483972982028030996632411 326225959473042046494948617)
      ·
        refine ⟨244669469604781534871211463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326225959473042046494948617 244669469604781534871211463)
        ·
          refine ⟨367004204407172302306817195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244669469604781534871211463 367004204407172302306817195)
          ·
            refine ⟨550506306610758453460225793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367004204407172302306817195 550506306610758453460225793)
            ·
              refine ⟨412879729958068840095169345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550506306610758453460225793 412879729958068840095169345)
              ·
                refine ⟨309659797468551630071377009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412879729958068840095169345 309659797468551630071377009)
                ·
                  refine ⟨232244848101413722553532757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309659797468551630071377009 232244848101413722553532757)
                  ·
                    refine ⟨680404828422110515293553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 232244848101413722553532757 680404828422110515293553)
                    ·
                      rfl

theorem cell23_3975251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_3975251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975251 prefixEnd_3975251 := by exact prefixLift 3975251
  have htrace : WordTrace (prefixWord ++ tailWord_3975251) baseStart_3975251 baseEnd_3975251 := by
    simpa [prefixWord, tailWord_3975251, baseEnd_3975251] using wordTrace_append hprefix tailTrace_3975251
  have hstable : (prefixWord ++ tailWord_3975251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975251).length < 2 ^ (prefixWord ++ tailWord_3975251).sum := by decide
  have hdescent : baseEnd_3975251 < baseStart_3975251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975269 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_3975269 : Nat := 118140960795 + 3975269 * 2 ^ 59
def prefixEnd_3975269 : Nat := 4983230072969 + 3 ^ 40 * 3975269 * 2
def baseEnd_3975269 : Nat := 2041223727918112475455577

theorem tailTrace_3975269 : CollatzResearch.WordTrace tailWord_3975269 prefixEnd_3975269 2041223727918112475455577 := by
  unfold tailWord_3975269
  simp only [CollatzResearch.WordTrace]
  refine ⟨144989971835286809738576861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96659981223524539825717907 144989971835286809738576861)
  ·
    refine ⟨54371239438232553651966323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144989971835286809738576861 54371239438232553651966323)
    ·
      refine ⟨81556859157348830477949485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54371239438232553651966323 81556859157348830477949485)
      ·
        refine ⟨30583822184005811429231057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81556859157348830477949485 30583822184005811429231057)
        ·
          refine ⟨22937866638004358571923293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30583822184005811429231057 22937866638004358571923293)
          ·
            refine ⟨8601699989251634464471235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22937866638004358571923293 8601699989251634464471235)
            ·
              refine ⟨12902549983877451696706853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601699989251634464471235 12902549983877451696706853)
              ·
                refine ⟨2419228121977022193132535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12902549983877451696706853 2419228121977022193132535)
                ·
                  refine ⟨3628842182965533289698803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419228121977022193132535 3628842182965533289698803)
                  ·
                    refine ⟨5443263274448299934548205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628842182965533289698803 5443263274448299934548205)
                    ·
                      refine ⟨2041223727918112475455577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5443263274448299934548205 2041223727918112475455577)
                      ·
                        rfl

theorem cell23_3975269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_3975269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975269 prefixEnd_3975269 := by exact prefixLift 3975269
  have htrace : WordTrace (prefixWord ++ tailWord_3975269) baseStart_3975269 baseEnd_3975269 := by
    simpa [prefixWord, tailWord_3975269, baseEnd_3975269] using wordTrace_append hprefix tailTrace_3975269
  have hstable : (prefixWord ++ tailWord_3975269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975269).length < 2 ^ (prefixWord ++ tailWord_3975269).sum := by decide
  have hdescent : baseEnd_3975269 < baseStart_3975269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975292 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_3975292 : Nat := 118140960795 + 3975292 * 2 ^ 59
def prefixEnd_3975292 : Nat := 4983230072969 + 3 ^ 40 * 3975292 * 2
def baseEnd_3975292 : Nat := 2041235537973165885467971

theorem tailTrace_3975292 : CollatzResearch.WordTrace tailWord_3975292 prefixEnd_3975292 2041235537973165885467971 := by
  unfold tailWord_3975292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72495405357101742333332065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96660540476135656444442753 72495405357101742333332065)
  ·
    refine ⟨54371554017826306749999049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72495405357101742333332065 54371554017826306749999049)
    ·
      refine ⟨40778665513369730062499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54371554017826306749999049 40778665513369730062499287)
      ·
        refine ⟨61167998270054595093748931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778665513369730062499287 61167998270054595093748931)
        ·
          refine ⟨91751997405081892640623397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61167998270054595093748931 91751997405081892640623397)
          ·
            refine ⟨17203499513452854870116887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91751997405081892640623397 17203499513452854870116887)
            ·
              refine ⟨25805249270179282305175331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203499513452854870116887 25805249270179282305175331)
              ·
                refine ⟨38707873905268923457762997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25805249270179282305175331 38707873905268923457762997)
                ·
                  refine ⟨3628863178618961574165281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38707873905268923457762997 3628863178618961574165281)
                  ·
                    refine ⟨2721647383964221180623961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3628863178618961574165281 2721647383964221180623961)
                    ·
                      refine ⟨2041235537973165885467971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721647383964221180623961 2041235537973165885467971)
                      ·
                        rfl

theorem cell23_3975292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_3975292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975292 prefixEnd_3975292 := by exact prefixLift 3975292
  have htrace : WordTrace (prefixWord ++ tailWord_3975292) baseStart_3975292 baseEnd_3975292 := by
    simpa [prefixWord, tailWord_3975292, baseEnd_3975292] using wordTrace_append hprefix tailTrace_3975292
  have hstable : (prefixWord ++ tailWord_3975292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975292).length < 2 ^ (prefixWord ++ tailWord_3975292).sum := by decide
  have hdescent : baseEnd_3975292 < baseStart_3975292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975319 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 2, 4]
def baseStart_3975319 : Nat := 118140960795 + 3975319 * 2 ^ 59
def prefixEnd_3975319 : Nat := 4983230072969 + 3 ^ 40 * 3975319 * 2
def baseEnd_3975319 : Nat := 680416467316945759943449

theorem tailTrace_3975319 : CollatzResearch.WordTrace tailWord_3975319 prefixEnd_3975319 680416467316945759943449 := by
  unfold tailWord_3975319
  simp only [CollatzResearch.WordTrace]
  refine ⟨144991795485105668277897011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96661196990070445518598007 144991795485105668277897011)
  ·
    refine ⟨217487693227658502416845517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144991795485105668277897011 217487693227658502416845517)
    ·
      refine ⟨81557884960371938406317069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217487693227658502416845517 81557884960371938406317069)
      ·
        refine ⟨30584206860139476902368901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81557884960371938406317069 30584206860139476902368901)
        ·
          refine ⟨5734538786276151919194169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30584206860139476902368901 5734538786276151919194169)
          ·
            refine ⟨4300904089707113939395627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5734538786276151919194169 4300904089707113939395627)
            ·
              refine ⟨6451356134560670909093441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300904089707113939395627 6451356134560670909093441)
              ·
                refine ⟨4838517100920503181820081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451356134560670909093441 4838517100920503181820081)
                ·
                  refine ⟨3628887825690377386365061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838517100920503181820081 3628887825690377386365061)
                  ·
                    refine ⟨680416467316945759943449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628887825690377386365061 680416467316945759943449)
                    ·
                      rfl

theorem cell23_3975319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_3975319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975319 prefixEnd_3975319 := by exact prefixLift 3975319
  have htrace : WordTrace (prefixWord ++ tailWord_3975319) baseStart_3975319 baseEnd_3975319 := by
    simpa [prefixWord, tailWord_3975319, baseEnd_3975319] using wordTrace_append hprefix tailTrace_3975319
  have hstable : (prefixWord ++ tailWord_3975319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975319).length < 2 ^ (prefixWord ++ tailWord_3975319).sum := by decide
  have hdescent : baseEnd_3975319 < baseStart_3975319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975349 : List Nat := [1, 3, 3, 4, 1, 2, 2, 7]
def baseStart_3975349 : Nat := 118140960795 + 3975349 * 2 ^ 59
def prefixEnd_3975349 : Nat := 4983230072969 + 3 ^ 40 * 3975349 * 2
def baseEnd_3975349 : Nat := 75602400235943413424267

theorem tailTrace_3975349 : CollatzResearch.WordTrace tailWord_3975349 prefixEnd_3975349 75602400235943413424267 := by
  unfold tailWord_3975349
  simp only [CollatzResearch.WordTrace]
  refine ⟨144992889674996983401489101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96661926449997988934326067 144992889674996983401489101)
  ·
    refine ⟨54372333628123868775558413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144992889674996983401489101 54372333628123868775558413)
    ·
      refine ⟨20389625110546450790834405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54372333628123868775558413 20389625110546450790834405)
      ·
        refine ⟨3823054708227459523281451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20389625110546450790834405 3823054708227459523281451)
        ·
          refine ⟨5734582062341189284922177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823054708227459523281451 5734582062341189284922177)
          ·
            refine ⟨4300936546755891963691633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5734582062341189284922177 4300936546755891963691633)
            ·
              refine ⟨3225702410066918972768725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300936546755891963691633 3225702410066918972768725)
              ·
                refine ⟨75602400235943413424267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3225702410066918972768725 75602400235943413424267)
                ·
                  rfl

theorem cell23_3975349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 7].length) (baseStart_3975349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975349 prefixEnd_3975349 := by exact prefixLift 3975349
  have htrace : WordTrace (prefixWord ++ tailWord_3975349) baseStart_3975349 baseEnd_3975349 := by
    simpa [prefixWord, tailWord_3975349, baseEnd_3975349] using wordTrace_append hprefix tailTrace_3975349
  have hstable : (prefixWord ++ tailWord_3975349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975349).length < 2 ^ (prefixWord ++ tailWord_3975349).sum := by decide
  have hdescent : baseEnd_3975349 < baseStart_3975349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975408 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_3975408 : Nat := 118140960795 + 3975408 * 2 ^ 59
def prefixEnd_3975408 : Nat := 4983230072969 + 3 ^ 40 * 3975408 * 2
def baseEnd_3975408 : Nat := 2041295101729087431617437

theorem tailTrace_3975408 : CollatzResearch.WordTrace tailWord_3975408 prefixEnd_3975408 2041295101729087431617437 := by
  unfold tailWord_3975408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497520790891618238943439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96663361054522157651924585 72497520790891618238943439)
  ·
    refine ⟨108746281186337427358415159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72497520790891618238943439 108746281186337427358415159)
    ·
      refine ⟨163119421779506141037622739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108746281186337427358415159 163119421779506141037622739)
      ·
        refine ⟨244679132669259211556434109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163119421779506141037622739 244679132669259211556434109)
        ·
          refine ⟨91754674750972204333662791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244679132669259211556434109 91754674750972204333662791)
          ·
            refine ⟨137632012126458306500494187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91754674750972204333662791 137632012126458306500494187)
            ·
              refine ⟨206448018189687459750741281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137632012126458306500494187 206448018189687459750741281)
              ·
                refine ⟨154836013642265594813055961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206448018189687459750741281 154836013642265594813055961)
                ·
                  refine ⟨116127010231699196109791971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154836013642265594813055961 116127010231699196109791971)
                  ·
                    refine ⟨174190515347548794164687957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116127010231699196109791971 174190515347548794164687957)
                    ·
                      refine ⟨2041295101729087431617437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174190515347548794164687957 2041295101729087431617437)
                      ·
                        rfl

theorem cell23_3975408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_3975408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975408 prefixEnd_3975408 := by exact prefixLift 3975408
  have htrace : WordTrace (prefixWord ++ tailWord_3975408) baseStart_3975408 baseEnd_3975408 := by
    simpa [prefixWord, tailWord_3975408, baseEnd_3975408] using wordTrace_append hprefix tailTrace_3975408
  have hstable : (prefixWord ++ tailWord_3975408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975408).length < 2 ^ (prefixWord ++ tailWord_3975408).sum := by decide
  have hdescent : baseEnd_3975408 < baseStart_3975408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975435 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 2, 5]
def baseStart_3975435 : Nat := 118140960795 + 3975435 * 2 ^ 59
def prefixEnd_3975435 : Nat := 4983230072969 + 3 ^ 40 * 3975435 * 2
def baseEnd_3975435 : Nat := 680436321902252941993271

theorem tailTrace_3975435 : CollatzResearch.WordTrace tailWord_3975435 prefixEnd_3975435 680436321902252941993271 := by
  unfold tailWord_3975435
  simp only [CollatzResearch.WordTrace]
  refine ⟨144996026352685420089119759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96664017568456946726079839 144996026352685420089119759)
  ·
    refine ⟨217494039529028130133679639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144996026352685420089119759 217494039529028130133679639)
    ·
      refine ⟨326241059293542195200519459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217494039529028130133679639 326241059293542195200519459)
      ·
        refine ⟨489361588940313292800779189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326241059293542195200519459 489361588940313292800779189)
        ·
          refine ⟨45877648963154371200073049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489361588940313292800779189 45877648963154371200073049)
          ·
            refine ⟨34408236722365778400054787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45877648963154371200073049 34408236722365778400054787)
            ·
              refine ⟨51612355083548667600082181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34408236722365778400054787 51612355083548667600082181)
              ·
                refine ⟨9677316578165375175015409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51612355083548667600082181 9677316578165375175015409)
                ·
                  refine ⟨7257987433624031381261557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677316578165375175015409 7257987433624031381261557)
                  ·
                    refine ⟨680436321902252941993271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7257987433624031381261557 680436321902252941993271)
                    ·
                      rfl

theorem cell23_3975435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].length) (baseStart_3975435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975435 prefixEnd_3975435 := by exact prefixLift 3975435
  have htrace : WordTrace (prefixWord ++ tailWord_3975435) baseStart_3975435 baseEnd_3975435 := by
    simpa [prefixWord, tailWord_3975435, baseEnd_3975435] using wordTrace_append hprefix tailTrace_3975435
  have hstable : (prefixWord ++ tailWord_3975435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975435).length < 2 ^ (prefixWord ++ tailWord_3975435).sum := by decide
  have hdescent : baseEnd_3975435 < baseStart_3975435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975445 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3975445 : Nat := 118140960795 + 3975445 * 2 ^ 59
def prefixEnd_3975445 : Nat := 4983230072969 + 3 ^ 40 * 3975445 * 2
def baseEnd_3975445 : Nat := 2041314100513303786854767

theorem tailTrace_3975445 : CollatzResearch.WordTrace tailWord_3975445 prefixEnd_3975445 2041314100513303786854767 := by
  unfold tailWord_3975445
  simp only [CollatzResearch.WordTrace]
  refine ⟨144996391082649191796983789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96664260721766127864655859 144996391082649191796983789)
  ·
    refine ⟨54373646655993446923868921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144996391082649191796983789 54373646655993446923868921)
    ·
      refine ⟨40780234991995085192901691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54373646655993446923868921 40780234991995085192901691)
      ·
        refine ⟨61170352487992627789352537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40780234991995085192901691 61170352487992627789352537)
        ·
          refine ⟨45877764365994470842014403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61170352487992627789352537 45877764365994470842014403)
          ·
            refine ⟨68816646548991706263021605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45877764365994470842014403 68816646548991706263021605)
            ·
              refine ⟨12903121227935944924316551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68816646548991706263021605 12903121227935944924316551)
              ·
                refine ⟨19354681841903917386474827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12903121227935944924316551 19354681841903917386474827)
                ·
                  refine ⟨29032022762855876079712241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19354681841903917386474827 29032022762855876079712241)
                  ·
                    refine ⟨21774017072141907059784181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29032022762855876079712241 21774017072141907059784181)
                    ·
                      refine ⟨2041314100513303786854767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21774017072141907059784181 2041314100513303786854767)
                      ·
                        rfl

theorem cell23_3975445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3975445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975445 prefixEnd_3975445 := by exact prefixLift 3975445
  have htrace : WordTrace (prefixWord ++ tailWord_3975445) baseStart_3975445 baseEnd_3975445 := by
    simpa [prefixWord, tailWord_3975445, baseEnd_3975445] using wordTrace_append hprefix tailTrace_3975445
  have hstable : (prefixWord ++ tailWord_3975445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975445).length < 2 ^ (prefixWord ++ tailWord_3975445).sum := by decide
  have hdescent : baseEnd_3975445 < baseStart_3975445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975469 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3975469 : Nat := 118140960795 + 3975469 * 2 ^ 59
def prefixEnd_3975469 : Nat := 4983230072969 + 3 ^ 40 * 3975469 * 2
def baseEnd_3975469 : Nat := 680442141349670564318219

theorem tailTrace_3975469 : CollatzResearch.WordTrace tailWord_3975469 prefixEnd_3975469 680442141349670564318219 := by
  unfold tailWord_3975469
  simp only [CollatzResearch.WordTrace]
  refine ⟨144997266434562243895857461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96664844289708162597238307 144997266434562243895857461)
  ·
    refine ⟨13593493728240210365236637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144997266434562243895857461 13593493728240210365236637)
    ·
      refine ⟨5097560148090078886963739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13593493728240210365236637 5097560148090078886963739)
      ·
        refine ⟨7646340222135118330445609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097560148090078886963739 7646340222135118330445609)
        ·
          refine ⟨5734755166601338747834207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7646340222135118330445609 5734755166601338747834207)
          ·
            refine ⟨8602132749902008121751311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734755166601338747834207 8602132749902008121751311)
            ·
              refine ⟨12903199124853012182626967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8602132749902008121751311 12903199124853012182626967)
              ·
                refine ⟨19354798687279518273940451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12903199124853012182626967 19354798687279518273940451)
                ·
                  refine ⟨29032198030919277410910677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19354798687279518273940451 29032198030919277410910677)
                  ·
                    refine ⟨680442141349670564318219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29032198030919277410910677 680442141349670564318219)
                    ·
                      rfl

theorem cell23_3975469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3975469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975469 prefixEnd_3975469 := by exact prefixLift 3975469
  have htrace : WordTrace (prefixWord ++ tailWord_3975469) baseStart_3975469 baseEnd_3975469 := by
    simpa [prefixWord, tailWord_3975469, baseEnd_3975469] using wordTrace_append hprefix tailTrace_3975469
  have hstable : (prefixWord ++ tailWord_3975469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975469).length < 2 ^ (prefixWord ++ tailWord_3975469).sum := by decide
  have hdescent : baseEnd_3975469 < baseStart_3975469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975495 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 8]
def baseStart_3975495 : Nat := 118140960795 + 3975495 * 2 ^ 59
def prefixEnd_3975495 : Nat := 4983230072969 + 3 ^ 40 * 3975495 * 2
def baseEnd_3975495 : Nat := 226815530505114287914393

theorem tailTrace_3975495 : CollatzResearch.WordTrace tailWord_3975495 prefixEnd_3975495 226815530505114287914393 := by
  unfold tailWord_3975495
  simp only [CollatzResearch.WordTrace]
  refine ⟨144998214732468050336303939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96665476488312033557535959 144998214732468050336303939)
  ·
    refine ⟨217497322098702075504455909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144998214732468050336303939 217497322098702075504455909)
    ·
      refine ⟨40780747893506639157085483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217497322098702075504455909 40780747893506639157085483)
      ·
        refine ⟨61171121840259958735628225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40780747893506639157085483 61171121840259958735628225)
        ·
          refine ⟨45878341380194969051721169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61171121840259958735628225 45878341380194969051721169)
          ·
            refine ⟨34408756035146226788790877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45878341380194969051721169 34408756035146226788790877)
            ·
              refine ⟨12903283513179835045796579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34408756035146226788790877 12903283513179835045796579)
              ·
                refine ⟨19354925269769752568694869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12903283513179835045796579 19354925269769752568694869)
                ·
                  refine ⟨226815530505114287914393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19354925269769752568694869 226815530505114287914393)
                  ·
                    rfl

theorem cell23_3975495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 8].length) (baseStart_3975495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975495 prefixEnd_3975495 := by exact prefixLift 3975495
  have htrace : WordTrace (prefixWord ++ tailWord_3975495) baseStart_3975495 baseEnd_3975495 := by
    simpa [prefixWord, tailWord_3975495, baseEnd_3975495] using wordTrace_append hprefix tailTrace_3975495
  have hstable : (prefixWord ++ tailWord_3975495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975495).length < 2 ^ (prefixWord ++ tailWord_3975495).sum := by decide
  have hdescent : baseEnd_3975495 < baseStart_3975495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975549 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_3975549 : Nat := 118140960795 + 3975549 * 2 ^ 59
def prefixEnd_3975549 : Nat := 4983230072969 + 3 ^ 40 * 3975549 * 2
def baseEnd_3975549 : Nat := 2041367502501371379954289

theorem tailTrace_3975549 : CollatzResearch.WordTrace tailWord_3975549 prefixEnd_3975549 2041367502501371379954289 := by
  unfold tailWord_3975549
  simp only [CollatzResearch.WordTrace]
  refine ⟨145000184274272417558769701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96666789516181611705846467 145000184274272417558769701)
  ·
    refine ⟨27187534551426078292269319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145000184274272417558769701 27187534551426078292269319)
    ·
      refine ⟨40781301827139117438403979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27187534551426078292269319 40781301827139117438403979)
      ·
        refine ⟨61171952740708676157605969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40781301827139117438403979 61171952740708676157605969)
        ·
          refine ⟨45878964555531507118204477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61171952740708676157605969 45878964555531507118204477)
          ·
            refine ⟨17204611708324315169326679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45878964555531507118204477 17204611708324315169326679)
            ·
              refine ⟨25806917562486472753990019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204611708324315169326679 25806917562486472753990019)
              ·
                refine ⟨38710376343729709130985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25806917562486472753990019 38710376343729709130985029)
                ·
                  refine ⟨7258195564449320462059693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38710376343729709130985029 7258195564449320462059693)
                  ·
                    refine ⟨2721823336668495173272385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7258195564449320462059693 2721823336668495173272385)
                    ·
                      refine ⟨2041367502501371379954289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2721823336668495173272385 2041367502501371379954289)
                      ·
                        rfl

theorem cell23_3975549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_3975549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975549 prefixEnd_3975549 := by exact prefixLift 3975549
  have htrace : WordTrace (prefixWord ++ tailWord_3975549) baseStart_3975549 baseEnd_3975549 := by
    simpa [prefixWord, tailWord_3975549, baseEnd_3975549] using wordTrace_append hprefix tailTrace_3975549
  have hstable : (prefixWord ++ tailWord_3975549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975549).length < 2 ^ (prefixWord ++ tailWord_3975549).sum := by decide
  have hdescent : baseEnd_3975549 < baseStart_3975549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975576 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_3975576 : Nat := 118140960795 + 3975576 * 2 ^ 59
def prefixEnd_3975576 : Nat := 4983230072969 + 3 ^ 40 * 3975576 * 2
def baseEnd_3975576 : Nat := 680460455493014258105555

theorem tailTrace_3975576 : CollatzResearch.WordTrace tailWord_3975576 prefixEnd_3975576 680460455493014258105555 := by
  unfold tailWord_3975576
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500584522587300585001291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96667446030116400780001721 72500584522587300585001291)
  ·
    refine ⟨108750876783880950877501937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72500584522587300585001291 108750876783880950877501937)
    ·
      refine ⟨81563157587910713158126453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108750876783880950877501937 81563157587910713158126453)
      ·
        refine ⟨7646546023866629358574355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81563157587910713158126453 7646546023866629358574355)
        ·
          refine ⟨11469819035799944037861533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646546023866629358574355 11469819035799944037861533)
          ·
            refine ⟨4301182138424979014198075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11469819035799944037861533 4301182138424979014198075)
            ·
              refine ⟨6451773207637468521297113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301182138424979014198075 6451773207637468521297113)
              ·
                refine ⟨4838829905728101390972835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451773207637468521297113 4838829905728101390972835)
                ·
                  refine ⟨7258244858592152086459253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838829905728101390972835 7258244858592152086459253)
                  ·
                    refine ⟨680460455493014258105555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7258244858592152086459253 680460455493014258105555)
                    ·
                      rfl

theorem cell23_3975576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_3975576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975576 prefixEnd_3975576 := by exact prefixLift 3975576
  have htrace : WordTrace (prefixWord ++ tailWord_3975576) baseStart_3975576 baseEnd_3975576 := by
    simpa [prefixWord, tailWord_3975576, baseEnd_3975576] using wordTrace_append hprefix tailTrace_3975576
  have hstable : (prefixWord ++ tailWord_3975576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975576).length < 2 ^ (prefixWord ++ tailWord_3975576).sum := by decide
  have hdescent : baseEnd_3975576 < baseStart_3975576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975642 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3975642 : Nat := 118140960795 + 3975642 * 2 ^ 59
def prefixEnd_3975642 : Nat := 4983230072969 + 3 ^ 40 * 3975642 * 2
def baseEnd_3975642 : Nat := 2041415256202239516091361

theorem tailTrace_3975642 : CollatzResearch.WordTrace tailWord_3975642 prefixEnd_3975642 2041415256202239516091361 := by
  unfold tailWord_3975642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250894065733873610476295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96669050841956996294603453 36250894065733873610476295)
  ·
    refine ⟨54376341098600810415714443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36250894065733873610476295 54376341098600810415714443)
    ·
      refine ⟨81564511647901215623571665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54376341098600810415714443 81564511647901215623571665)
      ·
        refine ⟨61173383735925911717678749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81564511647901215623571665 61173383735925911717678749)
        ·
          refine ⟨22940018900972216894129531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61173383735925911717678749 22940018900972216894129531)
          ·
            refine ⟨34410028351458325341194297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22940018900972216894129531 34410028351458325341194297)
            ·
              refine ⟨25807521263593744005895723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34410028351458325341194297 25807521263593744005895723)
              ·
                refine ⟨38711281895390616008843585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25807521263593744005895723 38711281895390616008843585)
                ·
                  refine ⟨29033461421542962006632689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38711281895390616008843585 29033461421542962006632689)
                  ·
                    refine ⟨21775096066157221504974517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29033461421542962006632689 21775096066157221504974517)
                    ·
                      refine ⟨2041415256202239516091361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21775096066157221504974517 2041415256202239516091361)
                      ·
                        rfl

theorem cell23_3975642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3975642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975642 prefixEnd_3975642 := by exact prefixLift 3975642
  have htrace : WordTrace (prefixWord ++ tailWord_3975642) baseStart_3975642 baseEnd_3975642 := by
    simpa [prefixWord, tailWord_3975642, baseEnd_3975642] using wordTrace_append hprefix tailTrace_3975642
  have hstable : (prefixWord ++ tailWord_3975642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975642).length < 2 ^ (prefixWord ++ tailWord_3975642).sum := by decide
  have hdescent : baseEnd_3975642 < baseStart_3975642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975650 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3975650 : Nat := 118140960795 + 3975650 * 2 ^ 59
def prefixEnd_3975650 : Nat := 4983230072969 + 3 ^ 40 * 3975650 * 2
def baseEnd_3975650 : Nat := 2041419364047475484791325

theorem tailTrace_3975650 : CollatzResearch.WordTrace tailWord_3975650 prefixEnd_3975650 2041419364047475484791325 := by
  unfold tailWord_3975650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250967011726627952049101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96669245364604341205464269 36250967011726627952049101)
  ·
    refine ⟨13594112629397485482018413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36250967011726627952049101 13594112629397485482018413)
    ·
      refine ⟨5097792236024057055756905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13594112629397485482018413 5097792236024057055756905)
      ·
        refine ⟨3823344177018042791817679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5097792236024057055756905 3823344177018042791817679)
        ·
          refine ⟨5735016265527064187726519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823344177018042791817679 5735016265527064187726519)
          ·
            refine ⟨8602524398290596281589779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735016265527064187726519 8602524398290596281589779)
            ·
              refine ⟨12903786597435894422384669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8602524398290596281589779 12903786597435894422384669)
              ·
                refine ⟨4838919974038460408394251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12903786597435894422384669 4838919974038460408394251)
                ·
                  refine ⟨7258379961057690612591377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838919974038460408394251 7258379961057690612591377)
                  ·
                    refine ⟨5443784970793267959443533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7258379961057690612591377 5443784970793267959443533)
                    ·
                      refine ⟨2041419364047475484791325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5443784970793267959443533 2041419364047475484791325)
                      ·
                        rfl

theorem cell23_3975650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3975650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975650 prefixEnd_3975650 := by exact prefixLift 3975650
  have htrace : WordTrace (prefixWord ++ tailWord_3975650) baseStart_3975650 baseEnd_3975650 := by
    simpa [prefixWord, tailWord_3975650, baseEnd_3975650] using wordTrace_append hprefix tailTrace_3975650
  have hstable : (prefixWord ++ tailWord_3975650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975650).length < 2 ^ (prefixWord ++ tailWord_3975650).sum := by decide
  have hdescent : baseEnd_3975650 < baseStart_3975650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975752 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_3975752 : Nat := 118140960795 + 3975752 * 2 ^ 59
def prefixEnd_3975752 : Nat := 4983230072969 + 3 ^ 40 * 3975752 * 2
def baseEnd_3975752 : Nat := 680490579691411361905285

theorem tailTrace_3975752 : CollatzResearch.WordTrace tailWord_3975752 prefixEnd_3975752 680490579691411361905285 := by
  unfold tailWord_3975752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72503794146268491614204755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96671725528357988818939673 72503794146268491614204755)
  ·
    refine ⟨108755691219402737421307133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72503794146268491614204755 108755691219402737421307133)
    ·
      refine ⟨40783384207276026532990175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108755691219402737421307133 40783384207276026532990175)
      ·
        refine ⟨61175076310914039799485263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40783384207276026532990175 61175076310914039799485263)
        ·
          refine ⟨91762614466371059699227895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61175076310914039799485263 91762614466371059699227895)
          ·
            refine ⟨137643921699556589548841843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91762614466371059699227895 137643921699556589548841843)
            ·
              refine ⟨206465882549334884323262765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137643921699556589548841843 206465882549334884323262765)
              ·
                refine ⟨77424705956000581621223537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206465882549334884323262765 77424705956000581621223537)
                ·
                  refine ⟨58068529467000436215917653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77424705956000581621223537 58068529467000436215917653)
                  ·
                    refine ⟨680490579691411361905285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58068529467000436215917653 680490579691411361905285)
                    ·
                      rfl

theorem cell23_3975752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_3975752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975752 prefixEnd_3975752 := by exact prefixLift 3975752
  have htrace : WordTrace (prefixWord ++ tailWord_3975752) baseStart_3975752 baseEnd_3975752 := by
    simpa [prefixWord, tailWord_3975752, baseEnd_3975752] using wordTrace_append hprefix tailTrace_3975752
  have hstable : (prefixWord ++ tailWord_3975752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975752).length < 2 ^ (prefixWord ++ tailWord_3975752).sum := by decide
  have hdescent : baseEnd_3975752 < baseStart_3975752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975759 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_3975759 : Nat := 118140960795 + 3975759 * 2 ^ 59
def prefixEnd_3975759 : Nat := 4983230072969 + 3 ^ 40 * 3975759 * 2
def baseEnd_3975759 : Nat := 2041475333438815558328323

theorem tailTrace_3975759 : CollatzResearch.WordTrace tailWord_3975759 prefixEnd_3975759 2041475333438815558328323 := by
  unfold tailWord_3975759
  simp only [CollatzResearch.WordTrace]
  refine ⟨145007843603511623423914331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96671895735674415615942887 145007843603511623423914331)
  ·
    refine ⟨217511765405267435135871497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145007843603511623423914331 217511765405267435135871497)
    ·
      refine ⟨163133824053950576351903623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217511765405267435135871497 163133824053950576351903623)
      ·
        refine ⟨244700736080925864527855435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163133824053950576351903623 244700736080925864527855435)
        ·
          refine ⟨367051104121388796791783153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244700736080925864527855435 367051104121388796791783153)
          ·
            refine ⟨275288328091041597593837365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367051104121388796791783153 275288328091041597593837365)
            ·
              refine ⟨25808280758535149774422253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275288328091041597593837365 25808280758535149774422253)
              ·
                refine ⟨9678105284450681165408345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25808280758535149774422253 9678105284450681165408345)
                ·
                  refine ⟨7258578963338010874056259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678105284450681165408345 7258578963338010874056259)
                  ·
                    refine ⟨10887868445007016311084389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258578963338010874056259 10887868445007016311084389)
                    ·
                      refine ⟨2041475333438815558328323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10887868445007016311084389 2041475333438815558328323)
                      ·
                        rfl

theorem cell23_3975759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_3975759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975759 prefixEnd_3975759 := by exact prefixLift 3975759
  have htrace : WordTrace (prefixWord ++ tailWord_3975759) baseStart_3975759 baseEnd_3975759 := by
    simpa [prefixWord, tailWord_3975759, baseEnd_3975759] using wordTrace_append hprefix tailTrace_3975759
  have hstable : (prefixWord ++ tailWord_3975759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975759).length < 2 ^ (prefixWord ++ tailWord_3975759).sum := by decide
  have hdescent : baseEnd_3975759 < baseStart_3975759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975786 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3975786 : Nat := 118140960795 + 3975786 * 2 ^ 59
def prefixEnd_3975786 : Nat := 4983230072969 + 3 ^ 40 * 3975786 * 2
def baseEnd_3975786 : Nat := 680496399138828984230233

theorem tailTrace_3975786 : CollatzResearch.WordTrace tailWord_3975786 prefixEnd_3975786 680496399138828984230233 := by
  unfold tailWord_3975786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252207093603451758786803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96672552249609204690098141 36252207093603451758786803)
  ·
    refine ⟨54378310640405177638180205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252207093603451758786803 54378310640405177638180205)
    ·
      refine ⟨20391866490151941614317577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54378310640405177638180205 20391866490151941614317577)
      ·
        refine ⟨15293899867613956210738183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20391866490151941614317577 15293899867613956210738183)
        ·
          refine ⟨22940849801420934316107275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15293899867613956210738183 22940849801420934316107275)
          ·
            refine ⟨34411274702131401474160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22940849801420934316107275 34411274702131401474160913)
            ·
              refine ⟨25808456026598551105620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34411274702131401474160913 25808456026598551105620685)
              ·
                refine ⟨9678171009974456664607757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25808456026598551105620685 9678171009974456664607757)
                ·
                  refine ⟨3629314128740421249227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9678171009974456664607757 3629314128740421249227909)
                  ·
                    refine ⟨680496399138828984230233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629314128740421249227909 680496399138828984230233)
                    ·
                      rfl

theorem cell23_3975786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3975786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975786 prefixEnd_3975786 := by exact prefixLift 3975786
  have htrace : WordTrace (prefixWord ++ tailWord_3975786) baseStart_3975786 baseEnd_3975786 := by
    simpa [prefixWord, tailWord_3975786, baseEnd_3975786] using wordTrace_append hprefix tailTrace_3975786
  have hstable : (prefixWord ++ tailWord_3975786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975786).length < 2 ^ (prefixWord ++ tailWord_3975786).sum := by decide
  have hdescent : baseEnd_3975786 < baseStart_3975786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975799 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 6]
def baseStart_3975799 : Nat := 118140960795 + 3975799 * 2 ^ 59
def prefixEnd_3975799 : Nat := 4983230072969 + 3 ^ 40 * 3975799 * 2
def baseEnd_3975799 : Nat := 226832874740555044647571

theorem tailTrace_3975799 : CollatzResearch.WordTrace tailWord_3975799 prefixEnd_3975799 226832874740555044647571 := by
  unfold tailWord_3975799
  simp only [CollatzResearch.WordTrace]
  refine ⟨145009302523366710255370451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96672868348911140170246967 145009302523366710255370451)
  ·
    refine ⟨217513953785050065383055677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145009302523366710255370451 217513953785050065383055677)
    ·
      refine ⟨81567732669393774518645879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217513953785050065383055677 81567732669393774518645879)
      ·
        refine ⟨122351599004090661777968819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81567732669393774518645879 122351599004090661777968819)
        ·
          refine ⟨183527398506135992666953229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122351599004090661777968819 183527398506135992666953229)
          ·
            refine ⟨68822774439800997250107461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183527398506135992666953229 68822774439800997250107461)
            ·
              refine ⟨12904270207462686984395149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68822774439800997250107461 12904270207462686984395149)
              ·
                refine ⟨4839101327798507619148181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12904270207462686984395149 4839101327798507619148181)
                ·
                  refine ⟨226832874740555044647571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4839101327798507619148181 226832874740555044647571)
                  ·
                    rfl

theorem cell23_3975799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6].length) (baseStart_3975799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975799 prefixEnd_3975799 := by exact prefixLift 3975799
  have htrace : WordTrace (prefixWord ++ tailWord_3975799) baseStart_3975799 baseEnd_3975799 := by
    simpa [prefixWord, tailWord_3975799, baseEnd_3975799] using wordTrace_append hprefix tailTrace_3975799
  have hstable : (prefixWord ++ tailWord_3975799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975799).length < 2 ^ (prefixWord ++ tailWord_3975799).sum := by decide
  have hdescent : baseEnd_3975799 < baseStart_3975799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975813 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_3975813 : Nat := 118140960795 + 3975813 * 2 ^ 59
def prefixEnd_3975813 : Nat := 4983230072969 + 3 ^ 40 * 3975813 * 2
def baseEnd_3975813 : Nat := 2041503061394158347053075

theorem tailTrace_3975813 : CollatzResearch.WordTrace tailWord_3975813 prefixEnd_3975813 2041503061394158347053075 := by
  unfold tailWord_3975813
  simp only [CollatzResearch.WordTrace]
  refine ⟨145009813145315990646380093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96673208763543993764253395 145009813145315990646380093)
  ·
    refine ⟨54378679929493496492392535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145009813145315990646380093 54378679929493496492392535)
    ·
      refine ⟨81568019894240244738588803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54378679929493496492392535 81568019894240244738588803)
      ·
        refine ⟨122352029841360367107883205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81568019894240244738588803 122352029841360367107883205)
        ·
          refine ⟨22941005595255068832728101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122352029841360367107883205 22941005595255068832728101)
          ·
            refine ⟨4301438549110325406136519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22941005595255068832728101 4301438549110325406136519)
            ·
              refine ⟨6452157823665488109204779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301438549110325406136519 6452157823665488109204779)
              ·
                refine ⟨9678236735498232163807169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452157823665488109204779 9678236735498232163807169)
                ·
                  refine ⟨7258677551623674122855377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678236735498232163807169 7258677551623674122855377)
                  ·
                    refine ⟨5444008163717755592141533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7258677551623674122855377 5444008163717755592141533)
                    ·
                      refine ⟨2041503061394158347053075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444008163717755592141533 2041503061394158347053075)
                      ·
                        rfl

theorem cell23_3975813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_3975813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975813 prefixEnd_3975813 := by exact prefixLift 3975813
  have htrace : WordTrace (prefixWord ++ tailWord_3975813) baseStart_3975813 baseEnd_3975813 := by
    simpa [prefixWord, tailWord_3975813, baseEnd_3975813] using wordTrace_append hprefix tailTrace_3975813
  have hstable : (prefixWord ++ tailWord_3975813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975813).length < 2 ^ (prefixWord ++ tailWord_3975813).sum := by decide
  have hdescent : baseEnd_3975813 < baseStart_3975813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975853 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_3975853 : Nat := 118140960795 + 3975853 * 2 ^ 59
def prefixEnd_3975853 : Nat := 4983230072969 + 3 ^ 40 * 3975853 * 2
def baseEnd_3975853 : Nat := 2041523600620338190552891

theorem tailTrace_3975853 : CollatzResearch.WordTrace tailWord_3975853 prefixEnd_3975853 2041523600620338190552891 := by
  unfold tailWord_3975853
  simp only [CollatzResearch.WordTrace]
  refine ⟨145011272065171077477836213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96674181376780718318557475 145011272065171077477836213)
  ·
    refine ⟨13594806756109788513547145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145011272065171077477836213 13594806756109788513547145)
    ·
      refine ⟨10196105067082341385160359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13594806756109788513547145 10196105067082341385160359)
      ·
        refine ⟨15294157600623512077740539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10196105067082341385160359 15294157600623512077740539)
        ·
          refine ⟨22941236400935268116610809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294157600623512077740539 22941236400935268116610809)
          ·
            refine ⟨17205927300701451087458107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22941236400935268116610809 17205927300701451087458107)
            ·
              refine ⟨25808890951052176631187161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17205927300701451087458107 25808890951052176631187161)
              ·
                refine ⟨19356668213289132473390371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25808890951052176631187161 19356668213289132473390371)
                ·
                  refine ⟨29035002319933698710085557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19356668213289132473390371 29035002319933698710085557)
                  ·
                    refine ⟨2722031467493784254070521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29035002319933698710085557 2722031467493784254070521)
                    ·
                      refine ⟨2041523600620338190552891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722031467493784254070521 2041523600620338190552891)
                      ·
                        rfl

theorem cell23_3975853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_3975853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975853 prefixEnd_3975853 := by exact prefixLift 3975853
  have htrace : WordTrace (prefixWord ++ tailWord_3975853) baseStart_3975853 baseEnd_3975853 := by
    simpa [prefixWord, tailWord_3975853, baseEnd_3975853] using wordTrace_append hprefix tailTrace_3975853
  have hstable : (prefixWord ++ tailWord_3975853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975853).length < 2 ^ (prefixWord ++ tailWord_3975853).sum := by decide
  have hdescent : baseEnd_3975853 < baseStart_3975853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975863 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 1, 5]
def baseStart_3975863 : Nat := 118140960795 + 3975863 * 2 ^ 59
def prefixEnd_3975863 : Nat := 4983230072969 + 3 ^ 40 * 3975863 * 2
def baseEnd_3975863 : Nat := 680509578475627717142615

theorem tailTrace_3975863 : CollatzResearch.WordTrace tailWord_3975863 prefixEnd_3975863 680509578475627717142615 := by
  unfold tailWord_3975863
  simp only [CollatzResearch.WordTrace]
  refine ⟨145011636795134849185700243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96674424530089899457133495 145011636795134849185700243)
  ·
    refine ⟨217517455192702273778550365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145011636795134849185700243 217517455192702273778550365)
    ·
      refine ⟨81569045697263352666956387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217517455192702273778550365 81569045697263352666956387)
      ·
        refine ⟨122353568545895029000434581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81569045697263352666956387 122353568545895029000434581)
        ·
          refine ⟨5735323525588829484395371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122353568545895029000434581 5735323525588829484395371)
          ·
            refine ⟨8602985288383244226593057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735323525588829484395371 8602985288383244226593057)
            ·
              refine ⟨6452238966287433169944793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602985288383244226593057 6452238966287433169944793)
              ·
                refine ⟨4839179224715574877458595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452238966287433169944793 4839179224715574877458595)
                ·
                  refine ⟨7258768837073362316187893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839179224715574877458595 7258768837073362316187893)
                  ·
                    refine ⟨680509578475627717142615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7258768837073362316187893 680509578475627717142615)
                    ·
                      rfl

theorem cell23_3975863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_3975863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975863 prefixEnd_3975863 := by exact prefixLift 3975863
  have htrace : WordTrace (prefixWord ++ tailWord_3975863) baseStart_3975863 baseEnd_3975863 := by
    simpa [prefixWord, tailWord_3975863, baseEnd_3975863] using wordTrace_append hprefix tailTrace_3975863
  have hstable : (prefixWord ++ tailWord_3975863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975863).length < 2 ^ (prefixWord ++ tailWord_3975863).sum := by decide
  have hdescent : baseEnd_3975863 < baseStart_3975863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975866 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_3975866 : Nat := 118140960795 + 3975866 * 2 ^ 59
def prefixEnd_3975866 : Nat := 4983230072969 + 3 ^ 40 * 3975866 * 2
def baseEnd_3975866 : Nat := 2041530275868846639690331

theorem tailTrace_3975866 : CollatzResearch.WordTrace tailWord_3975866 prefixEnd_3975866 2041530275868846639690331 := by
  unfold tailWord_3975866
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252936553530995174514863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96674497476082653798706301 36252936553530995174514863)
  ·
    refine ⟨54379404830296492761772295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252936553530995174514863 54379404830296492761772295)
    ·
      refine ⟨81569107245444739142658443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379404830296492761772295 81569107245444739142658443)
      ·
        refine ⟨122353660868167108713987665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81569107245444739142658443 122353660868167108713987665)
        ·
          refine ⟨91765245651125331535490749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122353660868167108713987665 91765245651125331535490749)
          ·
            refine ⟨34411967119171999325809031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91765245651125331535490749 34411967119171999325809031)
            ·
              refine ⟨51617950678757998988713547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34411967119171999325809031 51617950678757998988713547)
              ·
                refine ⟨77426926018136998483070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51617950678757998988713547 77426926018136998483070321)
                ·
                  refine ⟨58070194513602748862302741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77426926018136998483070321 58070194513602748862302741)
                  ·
                    refine ⟨2722040367825128852920441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58070194513602748862302741 2722040367825128852920441)
                    ·
                      refine ⟨2041530275868846639690331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722040367825128852920441 2041530275868846639690331)
                      ·
                        rfl

theorem cell23_3975866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_3975866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975866 prefixEnd_3975866 := by exact prefixLift 3975866
  have htrace : WordTrace (prefixWord ++ tailWord_3975866) baseStart_3975866 baseEnd_3975866 := by
    simpa [prefixWord, tailWord_3975866, baseEnd_3975866] using wordTrace_append hprefix tailTrace_3975866
  have hstable : (prefixWord ++ tailWord_3975866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975866).length < 2 ^ (prefixWord ++ tailWord_3975866).sum := by decide
  have hdescent : baseEnd_3975866 < baseStart_3975866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975886 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3975886 : Nat := 118140960795 + 3975886 * 2 ^ 59
def prefixEnd_3975886 : Nat := 4983230072969 + 3 ^ 40 * 3975886 * 2
def baseEnd_3975886 : Nat := 2041540545481936561440239

theorem tailTrace_3975886 : CollatzResearch.WordTrace tailWord_3975886 prefixEnd_3975886 2041540545481936561440239 := by
  unfold tailWord_3975886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126559459256440514223439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96674983782701016075858341 18126559459256440514223439)
  ·
    refine ⟨27189839188884660771335159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126559459256440514223439 27189839188884660771335159)
    ·
      refine ⟨40784758783326991157002739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27189839188884660771335159 40784758783326991157002739)
      ·
        refine ⟨61177138174990486735504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40784758783326991157002739 61177138174990486735504109)
        ·
          refine ⟨22941426815621432525814041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61177138174990486735504109 22941426815621432525814041)
          ·
            refine ⟨17206070111716074394360531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22941426815621432525814041 17206070111716074394360531)
            ·
              refine ⟨25809105167574111591540797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17206070111716074394360531 25809105167574111591540797)
              ·
                refine ⟨9678414437840291846827799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25809105167574111591540797 9678414437840291846827799)
                ·
                  refine ⟨14517621656760437770241699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9678414437840291846827799 14517621656760437770241699)
                  ·
                    refine ⟨21776432485140656655362549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14517621656760437770241699 21776432485140656655362549)
                    ·
                      refine ⟨2041540545481936561440239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21776432485140656655362549 2041540545481936561440239)
                      ·
                        rfl

theorem cell23_3975886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3975886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975886 prefixEnd_3975886 := by exact prefixLift 3975886
  have htrace : WordTrace (prefixWord ++ tailWord_3975886) baseStart_3975886 baseEnd_3975886 := by
    simpa [prefixWord, tailWord_3975886, baseEnd_3975886] using wordTrace_append hprefix tailTrace_3975886
  have hstable : (prefixWord ++ tailWord_3975886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975886).length < 2 ^ (prefixWord ++ tailWord_3975886).sum := by decide
  have hdescent : baseEnd_3975886 < baseStart_3975886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975916 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_3975916 : Nat := 118140960795 + 3975916 * 2 ^ 59
def prefixEnd_3975916 : Nat := 4983230072969 + 3 ^ 40 * 3975916 * 2
def baseEnd_3975916 : Nat := 2041555949901571444065101

theorem tailTrace_3975916 : CollatzResearch.WordTrace tailWord_3975916 prefixEnd_3975916 2041555949901571444065101 := by
  unfold tailWord_3975916
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506784931971419618689801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96675713242628559491586401 72506784931971419618689801)
  ·
    refine ⟨54380088698978564714017351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72506784931971419618689801 54380088698978564714017351)
    ·
      refine ⟨81570133048467847071026027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54380088698978564714017351 81570133048467847071026027)
      ·
        refine ⟨122355199572701770606539041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81570133048467847071026027 122355199572701770606539041)
        ·
          refine ⟨91766399679526327954904281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122355199572701770606539041 91766399679526327954904281)
          ·
            refine ⟨68824799759644745966178211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91766399679526327954904281 68824799759644745966178211)
            ·
              refine ⟨103237199639467118949267317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68824799759644745966178211 103237199639467118949267317)
              ·
                refine ⟨9678487466200042401493811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103237199639467118949267317 9678487466200042401493811)
                ·
                  refine ⟨14517731199300063602240717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9678487466200042401493811 14517731199300063602240717)
                  ·
                    refine ⟨5444149199737523850840269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14517731199300063602240717 5444149199737523850840269)
                    ·
                      refine ⟨2041555949901571444065101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444149199737523850840269 2041555949901571444065101)
                      ·
                        rfl

theorem cell23_3975916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_3975916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975916 prefixEnd_3975916 := by exact prefixLift 3975916
  have htrace : WordTrace (prefixWord ++ tailWord_3975916) baseStart_3975916 baseEnd_3975916 := by
    simpa [prefixWord, tailWord_3975916, baseEnd_3975916] using wordTrace_append hprefix tailTrace_3975916
  have hstable : (prefixWord ++ tailWord_3975916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975916).length < 2 ^ (prefixWord ++ tailWord_3975916).sum := by decide
  have hdescent : baseEnd_3975916 < baseStart_3975916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975929 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3975929 : Nat := 118140960795 + 3975929 * 2 ^ 59
def prefixEnd_3975929 : Nat := 4983230072969 + 3 ^ 40 * 3975929 * 2
def baseEnd_3975929 : Nat := 2041562625150079893202541

theorem tailTrace_3975929 : CollatzResearch.WordTrace tailWord_3975929 prefixEnd_3975929 2041562625150079893202541 := by
  unfold tailWord_3975929
  simp only [CollatzResearch.WordTrace]
  refine ⟨145014044012895742457602841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96676029341930494971735227 145014044012895742457602841)
  ·
    refine ⟨108760533009671806843202131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145014044012895742457602841 108760533009671806843202131)
    ·
      refine ⟨163140799514507710264803197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108760533009671806843202131 163140799514507710264803197)
      ·
        refine ⟨61177799817940391349301199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163140799514507710264803197 61177799817940391349301199)
        ·
          refine ⟨91766699726910587023951799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61177799817940391349301199 91766699726910587023951799)
          ·
            refine ⟨137650049590365880535927699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91766699726910587023951799 137650049590365880535927699)
            ·
              refine ⟨206475074385548820803891549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137650049590365880535927699 206475074385548820803891549)
              ·
                refine ⟨77428152894580807801459331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206475074385548820803891549 77428152894580807801459331)
                ·
                  refine ⟨116142229341871211702188997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77428152894580807801459331 116142229341871211702188997)
                  ·
                    refine ⟨21776668001600852194160437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116142229341871211702188997 21776668001600852194160437)
                    ·
                      refine ⟨2041562625150079893202541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21776668001600852194160437 2041562625150079893202541)
                      ·
                        rfl

theorem cell23_3975929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3975929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975929 prefixEnd_3975929 := by exact prefixLift 3975929
  have htrace : WordTrace (prefixWord ++ tailWord_3975929) baseStart_3975929 baseEnd_3975929 := by
    simpa [prefixWord, tailWord_3975929, baseEnd_3975929] using wordTrace_append hprefix tailTrace_3975929
  have hstable : (prefixWord ++ tailWord_3975929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975929).length < 2 ^ (prefixWord ++ tailWord_3975929).sum := by decide
  have hdescent : baseEnd_3975929 < baseStart_3975929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975979 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 9]
def baseStart_3975979 : Nat := 118140960795 + 3975979 * 2 ^ 59
def prefixEnd_3975979 : Nat := 4983230072969 + 3 ^ 40 * 3975979 * 2
def baseEnd_3975979 : Nat := 226843144353644966397479

theorem tailTrace_3975979 : CollatzResearch.WordTrace tailWord_3975979 prefixEnd_3975979 226843144353644966397479 := by
  unfold tailWord_3975979
  simp only [CollatzResearch.WordTrace]
  refine ⟨145015867662714600996922991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96677245108476400664615327 145015867662714600996922991)
  ·
    refine ⟨217523801494071901495384487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145015867662714600996922991 217523801494071901495384487)
    ·
      refine ⟨326285702241107852243076731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217523801494071901495384487 326285702241107852243076731)
      ·
        refine ⟨489428553361661778364615097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326285702241107852243076731 489428553361661778364615097)
        ·
          refine ⟨367071415021246333773461323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489428553361661778364615097 367071415021246333773461323)
          ·
            refine ⟨550607122531869500660191985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367071415021246333773461323 550607122531869500660191985)
            ·
              refine ⟨412955341898902125495143989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550607122531869500660191985 412955341898902125495143989)
              ·
                refine ⟨38714563303022074265169749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412955341898902125495143989 38714563303022074265169749)
                ·
                  refine ⟨226843144353644966397479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38714563303022074265169749 226843144353644966397479)
                  ·
                    rfl

theorem cell23_3975979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_3975979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975979 prefixEnd_3975979 := by exact prefixLift 3975979
  have htrace : WordTrace (prefixWord ++ tailWord_3975979) baseStart_3975979 baseEnd_3975979 := by
    simpa [prefixWord, tailWord_3975979, baseEnd_3975979] using wordTrace_append hprefix tailTrace_3975979
  have hstable : (prefixWord ++ tailWord_3975979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975979).length < 2 ^ (prefixWord ++ tailWord_3975979).sum := by decide
  have hdescent : baseEnd_3975979 < baseStart_3975979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975986 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3975986 : Nat := 118140960795 + 3975986 * 2 ^ 59
def prefixEnd_3975986 : Nat := 4983230072969 + 3 ^ 40 * 3975986 * 2
def baseEnd_3975986 : Nat := 2041591893547386170189779

theorem tailTrace_3975986 : CollatzResearch.WordTrace tailWord_3975986 prefixEnd_3975986 2041591893547386170189779 := by
  unfold tailWord_3975986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254030743422310298106953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96677415315792827461618541 36254030743422310298106953)
  ·
    refine ⟨27190523057566732723580215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36254030743422310298106953 27190523057566732723580215)
    ·
      refine ⟨40785784586350099085370323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27190523057566732723580215 40785784586350099085370323)
      ·
        refine ⟨61178676879525148628055485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40785784586350099085370323 61178676879525148628055485)
        ·
          refine ⟨22942003829821930735520807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61178676879525148628055485 22942003829821930735520807)
          ·
            refine ⟨34413005744732896103281211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22942003829821930735520807 34413005744732896103281211)
            ·
              refine ⟨51619508617099344154921817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34413005744732896103281211 51619508617099344154921817)
              ·
                refine ⟨38714631462824508116191363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51619508617099344154921817 38714631462824508116191363)
                ·
                  refine ⟨58071947194236762174287045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38714631462824508116191363 58071947194236762174287045)
                  ·
                    refine ⟨10888490098919392907678821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58071947194236762174287045 10888490098919392907678821)
                    ·
                      refine ⟨2041591893547386170189779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10888490098919392907678821 2041591893547386170189779)
                      ·
                        rfl

theorem cell23_3975986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3975986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975986 prefixEnd_3975986 := by exact prefixLift 3975986
  have htrace : WordTrace (prefixWord ++ tailWord_3975986) baseStart_3975986 baseEnd_3975986 := by
    simpa [prefixWord, tailWord_3975986, baseEnd_3975986] using wordTrace_append hprefix tailTrace_3975986
  have hstable : (prefixWord ++ tailWord_3975986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975986).length < 2 ^ (prefixWord ++ tailWord_3975986).sum := by decide
  have hdescent : baseEnd_3975986 < baseStart_3975986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975994 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_3975994 : Nat := 118140960795 + 3975994 * 2 ^ 59
def prefixEnd_3975994 : Nat := 4983230072969 + 3 ^ 40 * 3975994 * 2
def baseEnd_3975994 : Nat := 2041596001392622138889743

theorem tailTrace_3975994 : CollatzResearch.WordTrace tailWord_3975994 prefixEnd_3975994 2041596001392622138889743 := by
  unfold tailWord_3975994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254103689415064639679759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96677609838440172372479357 36254103689415064639679759)
  ·
    refine ⟨54381155534122596959519639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36254103689415064639679759 54381155534122596959519639)
    ·
      refine ⟨81571733301183895439279459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54381155534122596959519639 81571733301183895439279459)
      ·
        refine ⟨122357599951775843158919189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81571733301183895439279459 122357599951775843158919189)
        ·
          refine ⟨5735512497739492648074337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122357599951775843158919189 5735512497739492648074337)
          ·
            refine ⟨4301634373304619486055753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5735512497739492648074337 4301634373304619486055753)
            ·
              refine ⟨3226225779978464614541815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301634373304619486055753 3226225779978464614541815)
              ·
                refine ⟨4839338669967696921812723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226225779978464614541815 4839338669967696921812723)
                ·
                  refine ⟨7259008004951545382719085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839338669967696921812723 7259008004951545382719085)
                  ·
                    refine ⟨2722128001856829518519657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7259008004951545382719085 2722128001856829518519657)
                    ·
                      refine ⟨2041596001392622138889743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722128001856829518519657 2041596001392622138889743)
                      ·
                        rfl

theorem cell23_3975994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_3975994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3975994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3975994 prefixEnd_3975994 := by exact prefixLift 3975994
  have htrace : WordTrace (prefixWord ++ tailWord_3975994) baseStart_3975994 baseEnd_3975994 := by
    simpa [prefixWord, tailWord_3975994, baseEnd_3975994] using wordTrace_append hprefix tailTrace_3975994
  have hstable : (prefixWord ++ tailWord_3975994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975994).length < 2 ^ (prefixWord ++ tailWord_3975994).sum := by decide
  have hdescent : baseEnd_3975994 < baseStart_3975994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976001 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3976001 : Nat := 118140960795 + 3976001 * 2 ^ 59
def prefixEnd_3976001 : Nat := 4983230072969 + 3 ^ 40 * 3976001 * 2
def baseEnd_3976001 : Nat := 2041599595757203611502211

theorem tailTrace_3976001 : CollatzResearch.WordTrace tailWord_3976001 prefixEnd_3976001 2041599595757203611502211 := by
  unfold tailWord_3976001
  simp only [CollatzResearch.WordTrace]
  refine ⟨145016670068634898754223857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96677780045756599169482571 145016670068634898754223857)
  ·
    refine ⟨108762502551476174065667893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145016670068634898754223857 108762502551476174065667893)
    ·
      refine ⟨10196484614200891318656365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108762502551476174065667893 10196484614200891318656365)
      ·
        refine ⟨3823681730325334244496137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10196484614200891318656365 3823681730325334244496137)
        ·
          refine ⟨2867761297744000683372103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823681730325334244496137 2867761297744000683372103)
          ·
            refine ⟨4301641946616001025058155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867761297744000683372103 4301641946616001025058155)
            ·
              refine ⟨6452462919924001537587233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301641946616001025058155 6452462919924001537587233)
              ·
                refine ⟨4839347189943001153190425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452462919924001537587233 4839347189943001153190425)
                ·
                  refine ⟨3629510392457250864892819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839347189943001153190425 3629510392457250864892819)
                  ·
                    refine ⟨5444265588685876297339229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3629510392457250864892819 5444265588685876297339229)
                    ·
                      refine ⟨2041599595757203611502211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444265588685876297339229 2041599595757203611502211)
                      ·
                        rfl

theorem cell23_3976001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3976001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976001 prefixEnd_3976001 := by exact prefixLift 3976001
  have htrace : WordTrace (prefixWord ++ tailWord_3976001) baseStart_3976001 baseEnd_3976001 := by
    simpa [prefixWord, tailWord_3976001, baseEnd_3976001] using wordTrace_append hprefix tailTrace_3976001
  have hstable : (prefixWord ++ tailWord_3976001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976001).length < 2 ^ (prefixWord ++ tailWord_3976001).sum := by decide
  have hdescent : baseEnd_3976001 < baseStart_3976001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976023 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_3976023 : Nat := 118140960795 + 3976023 * 2 ^ 59
def prefixEnd_3976023 : Nat := 4983230072969 + 3 ^ 40 * 3976023 * 2
def baseEnd_3976023 : Nat := 2041610892331602525427109

theorem tailTrace_3976023 : CollatzResearch.WordTrace tailWord_3976023 prefixEnd_3976023 2041610892331602525427109 := by
  unfold tailWord_3976023
  simp only [CollatzResearch.WordTrace]
  refine ⟨145017472474555196511524723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96678314983036797674349815 145017472474555196511524723)
  ·
    refine ⟨217526208711832794767287085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145017472474555196511524723 217526208711832794767287085)
    ·
      refine ⟨81572328266937298037732657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217526208711832794767287085 81572328266937298037732657)
      ·
        refine ⟨61179246200202973528299493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81572328266937298037732657 61179246200202973528299493)
        ·
          refine ⟨11471108662538057536556155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61179246200202973528299493 11471108662538057536556155)
          ·
            refine ⟨17206662993807086304834233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471108662538057536556155 17206662993807086304834233)
            ·
              refine ⟨12904997245355314728625675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17206662993807086304834233 12904997245355314728625675)
              ·
                refine ⟨19357495868032972092938513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904997245355314728625675 19357495868032972092938513)
                ·
                  refine ⟨14518121901024729069703885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19357495868032972092938513 14518121901024729069703885)
                  ·
                    refine ⟨5444295712884273401138957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14518121901024729069703885 5444295712884273401138957)
                    ·
                      refine ⟨2041610892331602525427109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444295712884273401138957 2041610892331602525427109)
                      ·
                        rfl

theorem cell23_3976023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_3976023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976023 prefixEnd_3976023 := by exact prefixLift 3976023
  have htrace : WordTrace (prefixWord ++ tailWord_3976023) baseStart_3976023 baseEnd_3976023 := by
    simpa [prefixWord, tailWord_3976023, baseEnd_3976023] using wordTrace_append hprefix tailTrace_3976023
  have hstable : (prefixWord ++ tailWord_3976023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976023).length < 2 ^ (prefixWord ++ tailWord_3976023).sum := by decide
  have hdescent : baseEnd_3976023 < baseStart_3976023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976026 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_3976026 : Nat := 118140960795 + 3976026 * 2 ^ 59
def prefixEnd_3976026 : Nat := 4983230072969 + 3 ^ 40 * 3976026 * 2
def baseEnd_3976026 : Nat := 680537477591188671229865

theorem tailTrace_3976026 : CollatzResearch.WordTrace tailWord_3976026 prefixEnd_3976026 680537477591188671229865 := by
  unfold tailWord_3976026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254395473386082005970983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96678387929029552015922621 36254395473386082005970983)
  ·
    refine ⟨54381593210079123008956475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36254395473386082005970983 54381593210079123008956475)
    ·
      refine ⟨81572389815118684513434713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54381593210079123008956475 81572389815118684513434713)
      ·
        refine ⟨61179292361339013385076035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81572389815118684513434713 61179292361339013385076035)
        ·
          refine ⟨91768938542008520077614053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61179292361339013385076035 91768938542008520077614053)
          ·
            refine ⟨17206675976626597514552635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91768938542008520077614053 17206675976626597514552635)
            ·
              refine ⟨25810013964939896271828953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17206675976626597514552635 25810013964939896271828953)
              ·
                refine ⟨19357510473704922203871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25810013964939896271828953 19357510473704922203871715)
                ·
                  refine ⟨29036265710557383305807573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19357510473704922203871715 29036265710557383305807573)
                  ·
                    refine ⟨680537477591188671229865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29036265710557383305807573 680537477591188671229865)
                    ·
                      rfl

theorem cell23_3976026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_3976026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976026 prefixEnd_3976026 := by exact prefixLift 3976026
  have htrace : WordTrace (prefixWord ++ tailWord_3976026) baseStart_3976026 baseEnd_3976026 := by
    simpa [prefixWord, tailWord_3976026, baseEnd_3976026] using wordTrace_append hprefix tailTrace_3976026
  have hstable : (prefixWord ++ tailWord_3976026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976026).length < 2 ^ (prefixWord ++ tailWord_3976026).sum := by decide
  have hdescent : baseEnd_3976026 < baseStart_3976026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976063 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 4, 2]
def baseStart_3976063 : Nat := 118140960795 + 3976063 * 2 ^ 59
def prefixEnd_3976063 : Nat := 4983230072969 + 3 ^ 40 * 3976063 * 2
def baseEnd_3976063 : Nat := 2041631431557782368926925

theorem tailTrace_3976063 : CollatzResearch.WordTrace tailWord_3976063 prefixEnd_3976063 2041631431557782368926925 := by
  unfold tailWord_3976063
  simp only [CollatzResearch.WordTrace]
  refine ⟨145018931394410283342980843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96679287596273522228653895 145018931394410283342980843)
  ·
    refine ⟨217528397091615425014471265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145018931394410283342980843 217528397091615425014471265)
    ·
      refine ⟨163146297818711568760853449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217528397091615425014471265 163146297818711568760853449)
      ·
        refine ⟨122359723364033676570640087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163146297818711568760853449 122359723364033676570640087)
        ·
          refine ⟨183539585046050514855960131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122359723364033676570640087 183539585046050514855960131)
          ·
            refine ⟨275309377569075772283940197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183539585046050514855960131 275309377569075772283940197)
            ·
              refine ⟨51620508294201707303238787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275309377569075772283940197 51620508294201707303238787)
              ·
                refine ⟨77430762441302560954858181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51620508294201707303238787 77430762441302560954858181)
                ·
                  refine ⟨14518267957744230179035909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77430762441302560954858181 14518267957744230179035909)
                  ·
                    refine ⟨2722175242077043158569233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14518267957744230179035909 2722175242077043158569233)
                    ·
                      refine ⟨2041631431557782368926925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722175242077043158569233 2041631431557782368926925)
                      ·
                        rfl

theorem cell23_3976063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_3976063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976063 prefixEnd_3976063 := by exact prefixLift 3976063
  have htrace : WordTrace (prefixWord ++ tailWord_3976063) baseStart_3976063 baseEnd_3976063 := by
    simpa [prefixWord, tailWord_3976063, baseEnd_3976063] using wordTrace_append hprefix tailTrace_3976063
  have hstable : (prefixWord ++ tailWord_3976063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976063).length < 2 ^ (prefixWord ++ tailWord_3976063).sum := by decide
  have hdescent : baseEnd_3976063 < baseStart_3976063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976076 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3976076 : Nat := 118140960795 + 3976076 * 2 ^ 59
def prefixEnd_3976076 : Nat := 4983230072969 + 3 ^ 40 * 3976076 * 2
def baseEnd_3976076 : Nat := 2041638106806290818064365

theorem tailTrace_3976076 : CollatzResearch.WordTrace tailWord_3976076 prefixEnd_3976076 2041638106806290818064365 := by
  unfold tailWord_3976076
  simp only [CollatzResearch.WordTrace]
  refine ⟨72509702771681593281602041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96679603695575457708802721 72509702771681593281602041)
  ·
    refine ⟨54382277078761194961201531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72509702771681593281602041 54382277078761194961201531)
    ·
      refine ⟨81573415618141792441802297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54382277078761194961201531 81573415618141792441802297)
      ·
        refine ⟨61180061713606344331351723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81573415618141792441802297 61180061713606344331351723)
        ·
          refine ⟨91770092570409516497027585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61180061713606344331351723 91770092570409516497027585)
          ·
            refine ⟨68827569427807137372770689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91770092570409516497027585 68827569427807137372770689)
            ·
              refine ⟨51620677070855353029578017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68827569427807137372770689 51620677070855353029578017)
              ·
                refine ⟨38715507803141514772183513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51620677070855353029578017 38715507803141514772183513)
                ·
                  refine ⟨29036630852356136079137635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38715507803141514772183513 29036630852356136079137635)
                  ·
                    refine ⟨43554946278534204118706453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29036630852356136079137635 43554946278534204118706453)
                    ·
                      refine ⟨2041638106806290818064365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43554946278534204118706453 2041638106806290818064365)
                      ·
                        rfl

theorem cell23_3976076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3976076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976076 prefixEnd_3976076 := by exact prefixLift 3976076
  have htrace : WordTrace (prefixWord ++ tailWord_3976076) baseStart_3976076 baseEnd_3976076 := by
    simpa [prefixWord, tailWord_3976076, baseEnd_3976076] using wordTrace_append hprefix tailTrace_3976076
  have hstable : (prefixWord ++ tailWord_3976076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976076).length < 2 ^ (prefixWord ++ tailWord_3976076).sum := by decide
  have hdescent : baseEnd_3976076 < baseStart_3976076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976100 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3976100 : Nat := 118140960795 + 3976100 * 2 ^ 59
def prefixEnd_3976100 : Nat := 4983230072969 + 3 ^ 40 * 3976100 * 2
def baseEnd_3976100 : Nat := 2041650430341998724164255

theorem tailTrace_3976100 : CollatzResearch.WordTrace tailWord_3976100 prefixEnd_3976100 2041650430341998724164255 := by
  unfold tailWord_3976100
  simp only [CollatzResearch.WordTrace]
  refine ⟨72510140447638119331038877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96680187263517492441385169 72510140447638119331038877)
  ·
    refine ⟨27191302667864294749139579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72510140447638119331038877 27191302667864294749139579)
    ·
      refine ⟨40786954001796442123709369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27191302667864294749139579 40786954001796442123709369)
      ·
        refine ⟨30590215501347331592782027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40786954001796442123709369 30590215501347331592782027)
        ·
          refine ⟨45885323252020997389173041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590215501347331592782027 45885323252020997389173041)
          ·
            refine ⟨34413992439015748041879781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45885323252020997389173041 34413992439015748041879781)
            ·
              refine ⟨6452623582315452757852459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34413992439015748041879781 6452623582315452757852459)
              ·
                refine ⟨9678935373473179136778689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452623582315452757852459 9678935373473179136778689)
                ·
                  refine ⟨7259201530104884352584017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678935373473179136778689 7259201530104884352584017)
                  ·
                    refine ⟨5444401147578663264438013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259201530104884352584017 5444401147578663264438013)
                    ·
                      refine ⟨2041650430341998724164255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444401147578663264438013 2041650430341998724164255)
                      ·
                        rfl

theorem cell23_3976100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3976100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976100 prefixEnd_3976100 := by exact prefixLift 3976100
  have htrace : WordTrace (prefixWord ++ tailWord_3976100) baseStart_3976100 baseEnd_3976100 := by
    simpa [prefixWord, tailWord_3976100, baseEnd_3976100] using wordTrace_append hprefix tailTrace_3976100
  have hstable : (prefixWord ++ tailWord_3976100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976100).length < 2 ^ (prefixWord ++ tailWord_3976100).sum := by decide
  have hdescent : baseEnd_3976100 < baseStart_3976100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976140 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3976140 : Nat := 118140960795 + 3976140 * 2 ^ 59
def prefixEnd_3976140 : Nat := 4983230072969 + 3 ^ 40 * 3976140 * 2
def baseEnd_3976140 : Nat := 2041670969568178567664071

theorem tailTrace_3976140 : CollatzResearch.WordTrace tailWord_3976140 prefixEnd_3976140 2041670969568178567664071 := by
  unfold tailWord_3976140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72510869907565662746766937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96681159876754216995689249 72510869907565662746766937)
  ·
    refine ⟨54383152430674247060075203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72510869907565662746766937 54383152430674247060075203)
    ·
      refine ⟨81574728646011370590112805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54383152430674247060075203 81574728646011370590112805)
      ·
        refine ⟨15295261621127131985646151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81574728646011370590112805 15295261621127131985646151)
        ·
          refine ⟨22942892431690697978469227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295261621127131985646151 22942892431690697978469227)
          ·
            refine ⟨34414338647536046967703841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22942892431690697978469227 34414338647536046967703841)
            ·
              refine ⟨25810753985652035225777881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34414338647536046967703841 25810753985652035225777881)
              ·
                refine ⟨19358065489239026419333411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25810753985652035225777881 19358065489239026419333411)
                ·
                  refine ⟨29037098233858539629000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358065489239026419333411 29037098233858539629000117)
                  ·
                    refine ⟨2722227959424238090218761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29037098233858539629000117 2722227959424238090218761)
                    ·
                      refine ⟨2041670969568178567664071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722227959424238090218761 2041670969568178567664071)
                      ·
                        rfl

theorem cell23_3976140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3976140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976140 prefixEnd_3976140 := by exact prefixLift 3976140
  have htrace : WordTrace (prefixWord ++ tailWord_3976140) baseStart_3976140 baseEnd_3976140 := by
    simpa [prefixWord, tailWord_3976140, baseEnd_3976140] using wordTrace_append hprefix tailTrace_3976140
  have hstable : (prefixWord ++ tailWord_3976140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976140).length < 2 ^ (prefixWord ++ tailWord_3976140).sum := by decide
  have hdescent : baseEnd_3976140 < baseStart_3976140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976141 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3976141 : Nat := 118140960795 + 3976141 * 2 ^ 59
def prefixEnd_3976141 : Nat := 4983230072969 + 3 ^ 40 * 3976141 * 2
def baseEnd_3976141 : Nat := 680557161016277687917189

theorem tailTrace_3976141 : CollatzResearch.WordTrace tailWord_3976141 prefixEnd_3976141 680557161016277687917189 := by
  unfold tailWord_3976141
  simp only [CollatzResearch.WordTrace]
  refine ⟨145021776288127702664320277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96681184192085135109546851 145021776288127702664320277)
  ·
    refine ⟨6797895763505986062390013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145021776288127702664320277 6797895763505986062390013)
    ·
      refine ⟨2549210911314744773396255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6797895763505986062390013 2549210911314744773396255)
      ·
        refine ⟨3823816366972117160094383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549210911314744773396255 3823816366972117160094383)
        ·
          refine ⟨5735724550458175740141575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823816366972117160094383 5735724550458175740141575)
          ·
            refine ⟨8603586825687263610212363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735724550458175740141575 8603586825687263610212363)
            ·
              refine ⟨12905380238530895415318545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603586825687263610212363 12905380238530895415318545)
              ·
                refine ⟨9679035178898171561488909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12905380238530895415318545 9679035178898171561488909)
                ·
                  refine ⟨3629638192086814335558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9679035178898171561488909 3629638192086814335558341)
                  ·
                    refine ⟨680557161016277687917189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629638192086814335558341 680557161016277687917189)
                    ·
                      rfl

theorem cell23_3976141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3976141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976141 prefixEnd_3976141 := by exact prefixLift 3976141
  have htrace : WordTrace (prefixWord ++ tailWord_3976141) baseStart_3976141 baseEnd_3976141 := by
    simpa [prefixWord, tailWord_3976141, baseEnd_3976141] using wordTrace_append hprefix tailTrace_3976141
  have hstable : (prefixWord ++ tailWord_3976141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976141).length < 2 ^ (prefixWord ++ tailWord_3976141).sum := by decide
  have hdescent : baseEnd_3976141 < baseStart_3976141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976157 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3976157 : Nat := 118140960795 + 3976157 * 2 ^ 59
def prefixEnd_3976157 : Nat := 4983230072969 + 3 ^ 40 * 3976157 * 2
def baseEnd_3976157 : Nat := 2041679698739305001151493

theorem tailTrace_3976157 : CollatzResearch.WordTrace tailWord_3976157 prefixEnd_3976157 2041679698739305001151493 := by
  unfold tailWord_3976157
  simp only [CollatzResearch.WordTrace]
  refine ⟨145022359856069737396902725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96681573237379824931268483 145022359856069737396902725)
  ·
    refine ⟨27191692473013075761919261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145022359856069737396902725 27191692473013075761919261)
    ·
      refine ⟨10196884677379903410719723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27191692473013075761919261 10196884677379903410719723)
      ·
        refine ⟨15295327016069855116079585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10196884677379903410719723 15295327016069855116079585)
        ·
          refine ⟨11471495262052391337059689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15295327016069855116079585 11471495262052391337059689)
          ·
            refine ⟨8603621446539293502794767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11471495262052391337059689 8603621446539293502794767)
            ·
              refine ⟨12905432169808940254192151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603621446539293502794767 12905432169808940254192151)
              ·
                refine ⟨19358148254713410381288227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905432169808940254192151 19358148254713410381288227)
                ·
                  refine ⟨29037222382070115571932341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358148254713410381288227 29037222382070115571932341)
                  ·
                    refine ⟨2722239598319073334868657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29037222382070115571932341 2722239598319073334868657)
                    ·
                      refine ⟨2041679698739305001151493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722239598319073334868657 2041679698739305001151493)
                      ·
                        rfl

theorem cell23_3976157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3976157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976157 prefixEnd_3976157 := by exact prefixLift 3976157
  have htrace : WordTrace (prefixWord ++ tailWord_3976157) baseStart_3976157 baseEnd_3976157 := by
    simpa [prefixWord, tailWord_3976157, baseEnd_3976157] using wordTrace_append hprefix tailTrace_3976157
  have hstable : (prefixWord ++ tailWord_3976157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976157).length < 2 ^ (prefixWord ++ tailWord_3976157).sum := by decide
  have hdescent : baseEnd_3976157 < baseStart_3976157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976163 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 6]
def baseStart_3976163 : Nat := 118140960795 + 3976163 * 2 ^ 59
def prefixEnd_3976163 : Nat := 4983230072969 + 3 ^ 40 * 3976163 * 2
def baseEnd_3976163 : Nat := 680560926541077325892155

theorem tailTrace_3976163 : CollatzResearch.WordTrace tailWord_3976163 prefixEnd_3976163 680560926541077325892155 := by
  unfold tailWord_3976163
  simp only [CollatzResearch.WordTrace]
  refine ⟨145022578694048000421621143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96681719129365333614414095 145022578694048000421621143)
  ·
    refine ⟨217533868041072000632431715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145022578694048000421621143 217533868041072000632431715)
    ·
      refine ⟨326300802061608000948647573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217533868041072000632431715 326300802061608000948647573)
      ·
        refine ⟨15295350096637875044467855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326300802061608000948647573 15295350096637875044467855)
        ·
          refine ⟨22943025144956812566701783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295350096637875044467855 22943025144956812566701783)
          ·
            refine ⟨34414537717435218850052675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943025144956812566701783 34414537717435218850052675)
            ·
              refine ⟨51621806576152828275079013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34414537717435218850052675 51621806576152828275079013)
              ·
                refine ⟨9679088733028655301577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51621806576152828275079013 9679088733028655301577315)
                ·
                  refine ⟨14518633099542982952365973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679088733028655301577315 14518633099542982952365973)
                  ·
                    refine ⟨680560926541077325892155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14518633099542982952365973 680560926541077325892155)
                    ·
                      rfl

theorem cell23_3976163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_3976163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976163 prefixEnd_3976163 := by exact prefixLift 3976163
  have htrace : WordTrace (prefixWord ++ tailWord_3976163) baseStart_3976163 baseEnd_3976163 := by
    simpa [prefixWord, tailWord_3976163, baseEnd_3976163] using wordTrace_append hprefix tailTrace_3976163
  have hstable : (prefixWord ++ tailWord_3976163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976163).length < 2 ^ (prefixWord ++ tailWord_3976163).sum := by decide
  have hdescent : baseEnd_3976163 < baseStart_3976163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976167 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3976167 : Nat := 118140960795 + 3976167 * 2 ^ 59
def prefixEnd_3976167 : Nat := 4983230072969 + 3 ^ 40 * 3976167 * 2
def baseEnd_3976167 : Nat := 680561611181949987342149

theorem tailTrace_3976167 : CollatzResearch.WordTrace tailWord_3976167 prefixEnd_3976167 680561611181949987342149 := by
  unfold tailWord_3976167
  simp only [CollatzResearch.WordTrace]
  refine ⟨145022724586033509104766755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96681816390689006069844503 145022724586033509104766755)
  ·
    refine ⟨217534086879050263657150133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145022724586033509104766755 217534086879050263657150133)
    ·
      refine ⟨20393820644910962217857825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217534086879050263657150133 20393820644910962217857825)
      ·
        refine ⟨15295365483683221663393369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20393820644910962217857825 15295365483683221663393369)
        ·
          refine ⟨11471524112762416247545027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15295365483683221663393369 11471524112762416247545027)
          ·
            refine ⟨17207286169143624371317541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471524112762416247545027 17207286169143624371317541)
            ·
              refine ⟨3226366156714429569622039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17207286169143624371317541 3226366156714429569622039)
              ·
                refine ⟨4839549235071644354433059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226366156714429569622039 4839549235071644354433059)
                ·
                  refine ⟨7259323852607466531649589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839549235071644354433059 7259323852607466531649589)
                  ·
                    refine ⟨680561611181949987342149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7259323852607466531649589 680561611181949987342149)
                    ·
                      rfl

theorem cell23_3976167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3976167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976167 prefixEnd_3976167 := by exact prefixLift 3976167
  have htrace : WordTrace (prefixWord ++ tailWord_3976167) baseStart_3976167 baseEnd_3976167 := by
    simpa [prefixWord, tailWord_3976167, baseEnd_3976167] using wordTrace_append hprefix tailTrace_3976167
  have hstable : (prefixWord ++ tailWord_3976167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976167).length < 2 ^ (prefixWord ++ tailWord_3976167).sum := by decide
  have hdescent : baseEnd_3976167 < baseStart_3976167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976181 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3976181 : Nat := 118140960795 + 3976181 * 2 ^ 59
def prefixEnd_3976181 : Nat := 4983230072969 + 3 ^ 40 * 3976181 * 2
def baseEnd_3976181 : Nat := 2041692022275012907251383

theorem tailTrace_3976181 : CollatzResearch.WordTrace tailWord_3976181 prefixEnd_3976181 2041692022275012907251383 := by
  unfold tailWord_3976181
  simp only [CollatzResearch.WordTrace]
  refine ⟨145023235207982789495776397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96682156805321859663850931 145023235207982789495776397)
  ·
    refine ⟨54383713202993546060916149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145023235207982789495776397 54383713202993546060916149)
    ·
      refine ⟨5098473112780644943210889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54383713202993546060916149 5098473112780644943210889)
      ·
        refine ⟨3823854834585483707408167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5098473112780644943210889 3823854834585483707408167)
        ·
          refine ⟨5735782251878225561112251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823854834585483707408167 5735782251878225561112251)
          ·
            refine ⟨8603673377817338341668377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735782251878225561112251 8603673377817338341668377)
            ·
              refine ⟨6452755033363003756251283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603673377817338341668377 6452755033363003756251283)
              ·
                refine ⟨9679132550044505634376925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452755033363003756251283 9679132550044505634376925)
                ·
                  refine ⟨3629674706266689612891347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9679132550044505634376925 3629674706266689612891347)
                  ·
                    refine ⟨5444512059400034419337021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3629674706266689612891347 5444512059400034419337021)
                    ·
                      refine ⟨2041692022275012907251383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444512059400034419337021 2041692022275012907251383)
                      ·
                        rfl

theorem cell23_3976181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3976181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976181 prefixEnd_3976181 := by exact prefixLift 3976181
  have htrace : WordTrace (prefixWord ++ tailWord_3976181) baseStart_3976181 baseEnd_3976181 := by
    simpa [prefixWord, tailWord_3976181, baseEnd_3976181] using wordTrace_append hprefix tailTrace_3976181
  have hstable : (prefixWord ++ tailWord_3976181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976181).length < 2 ^ (prefixWord ++ tailWord_3976181).sum := by decide
  have hdescent : baseEnd_3976181 < baseStart_3976181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976197 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_3976197 : Nat := 118140960795 + 3976197 * 2 ^ 59
def prefixEnd_3976197 : Nat := 4983230072969 + 3 ^ 40 * 3976197 * 2
def baseEnd_3976197 : Nat := 680566745988494948217103

theorem tailTrace_3976197 : CollatzResearch.WordTrace tailWord_3976197 prefixEnd_3976197 680566745988494948217103 := by
  unfold tailWord_3976197
  simp only [CollatzResearch.WordTrace]
  refine ⟨145023818775924824228358845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96682545850616549485572563 145023818775924824228358845)
  ·
    refine ⟨54383932040971809085634567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145023818775924824228358845 54383932040971809085634567)
    ·
      refine ⟨81575898061457713628451851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54383932040971809085634567 81575898061457713628451851)
      ·
        refine ⟨122363847092186570442677777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81575898061457713628451851 122363847092186570442677777)
        ·
          refine ⟨91772885319139927832008333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122363847092186570442677777 91772885319139927832008333)
          ·
            refine ⟨34414831994677472937003125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91772885319139927832008333 34414831994677472937003125)
            ·
              refine ⟨3226390499501013087844043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34414831994677472937003125 3226390499501013087844043)
              ·
                refine ⟨4839585749251519631766065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226390499501013087844043 4839585749251519631766065)
                ·
                  refine ⟨3629689311938639723824549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839585749251519631766065 3629689311938639723824549)
                  ·
                    refine ⟨680566745988494948217103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629689311938639723824549 680566745988494948217103)
                    ·
                      rfl

theorem cell23_3976197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_3976197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976197 prefixEnd_3976197 := by exact prefixLift 3976197
  have htrace : WordTrace (prefixWord ++ tailWord_3976197) baseStart_3976197 baseEnd_3976197 := by
    simpa [prefixWord, tailWord_3976197, baseEnd_3976197] using wordTrace_append hprefix tailTrace_3976197
  have hstable : (prefixWord ++ tailWord_3976197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976197).length < 2 ^ (prefixWord ++ tailWord_3976197).sum := by decide
  have hdescent : baseEnd_3976197 < baseStart_3976197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976200 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3976200 : Nat := 118140960795 + 3976200 * 2 ^ 59
def prefixEnd_3976200 : Nat := 4983230072969 + 3 ^ 40 * 3976200 * 2
def baseEnd_3976200 : Nat := 2041701778407448332913795

theorem tailTrace_3976200 : CollatzResearch.WordTrace tailWord_3976200 prefixEnd_3976200 2041701778407448332913795 := by
  unfold tailWord_3976200
  simp only [CollatzResearch.WordTrace]
  refine ⟨72511964097456977870359027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96682618796609303827145369 72511964097456977870359027)
  ·
    refine ⟨108767946146185466805538541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72511964097456977870359027 108767946146185466805538541)
    ·
      refine ⟨40787979804819550052076953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108767946146185466805538541 40787979804819550052076953)
      ·
        refine ⟨30590984853614662539057715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40787979804819550052076953 30590984853614662539057715)
        ·
          refine ⟨45886477280421993808586573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590984853614662539057715 45886477280421993808586573)
          ·
            refine ⟨17207428980158247678219965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45886477280421993808586573 17207428980158247678219965)
            ·
              refine ⟨6452785867559342879332487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17207428980158247678219965 6452785867559342879332487)
              ·
                refine ⟨9679178801339014318998731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452785867559342879332487 9679178801339014318998731)
                ·
                  refine ⟨14518768202008521478498097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679178801339014318998731 14518768202008521478498097)
                  ·
                    refine ⟨10889076151506391108873573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14518768202008521478498097 10889076151506391108873573)
                    ·
                      refine ⟨2041701778407448332913795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10889076151506391108873573 2041701778407448332913795)
                      ·
                        rfl

theorem cell23_3976200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3976200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976200 prefixEnd_3976200 := by exact prefixLift 3976200
  have htrace : WordTrace (prefixWord ++ tailWord_3976200) baseStart_3976200 baseEnd_3976200 := by
    simpa [prefixWord, tailWord_3976200, baseEnd_3976200] using wordTrace_append hprefix tailTrace_3976200
  have hstable : (prefixWord ++ tailWord_3976200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976200).length < 2 ^ (prefixWord ++ tailWord_3976200).sum := by decide
  have hdescent : baseEnd_3976200 < baseStart_3976200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976238 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3976238 : Nat := 118140960795 + 3976238 * 2 ^ 59
def prefixEnd_3976238 : Nat := 4983230072969 + 3 ^ 40 * 3976238 * 2
def baseEnd_3976238 : Nat := 2041721290672319184238621

theorem tailTrace_3976238 : CollatzResearch.WordTrace tailWord_3976238 prefixEnd_3976238 2041721290672319184238621 := by
  unfold tailWord_3976238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128164271097036028825171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96683542779184192153734245 18128164271097036028825171)
  ·
    refine ⟨27192246406645554043237757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18128164271097036028825171 27192246406645554043237757)
    ·
      refine ⟨10197092402492082766214159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27192246406645554043237757 10197092402492082766214159)
      ·
        refine ⟨15295638603738124149321239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197092402492082766214159 15295638603738124149321239)
        ·
          refine ⟨22943457905607186223981859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295638603738124149321239 22943457905607186223981859)
          ·
            refine ⟨34415186858410779335972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943457905607186223981859 34415186858410779335972789)
            ·
              refine ⟨3226423767976010562747449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34415186858410779335972789 3226423767976010562747449)
              ·
                refine ⟨2419817825982007922060587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226423767976010562747449 2419817825982007922060587)
                ·
                  refine ⟨3629726738973011883090881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419817825982007922060587 3629726738973011883090881)
                  ·
                    refine ⟨2722295054229758912318161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3629726738973011883090881 2722295054229758912318161)
                    ·
                      refine ⟨2041721290672319184238621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722295054229758912318161 2041721290672319184238621)
                      ·
                        rfl

theorem cell23_3976238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3976238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976238 prefixEnd_3976238 := by exact prefixLift 3976238
  have htrace : WordTrace (prefixWord ++ tailWord_3976238) baseStart_3976238 baseEnd_3976238 := by
    simpa [prefixWord, tailWord_3976238, baseEnd_3976238] using wordTrace_append hprefix tailTrace_3976238
  have hstable : (prefixWord ++ tailWord_3976238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976238).length < 2 ^ (prefixWord ++ tailWord_3976238).sum := by decide
  have hdescent : baseEnd_3976238 < baseStart_3976238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976243 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_3976243 : Nat := 118140960795 + 3976243 * 2 ^ 59
def prefixEnd_3976243 : Nat := 4983230072969 + 3 ^ 40 * 3976243 * 2
def baseEnd_3976243 : Nat := 2041723858075591664676097

theorem tailTrace_3976243 : CollatzResearch.WordTrace tailWord_3976243 prefixEnd_3976243 2041723858075591664676097 := by
  unfold tailWord_3976243
  simp only [CollatzResearch.WordTrace]
  refine ⟨145025496533758174084533383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96683664355838782723022255 145025496533758174084533383)
  ·
    refine ⟨217538244800637261126800075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145025496533758174084533383 217538244800637261126800075)
    ·
      refine ⟨326307367200955891690200113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217538244800637261126800075 326307367200955891690200113)
      ·
        refine ⟨244730525400716918767650085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326307367200955891690200113 244730525400716918767650085)
        ·
          refine ⟨45886973512634422268934391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244730525400716918767650085 45886973512634422268934391)
          ·
            refine ⟨68830460268951633403401587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45886973512634422268934391 68830460268951633403401587)
            ·
              refine ⟨103245690403427450105102381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68830460268951633403401587 103245690403427450105102381)
              ·
                refine ⟨38717133901285293789413393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103245690403427450105102381 38717133901285293789413393)
                ·
                  refine ⟨29037850425963970342060045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38717133901285293789413393 29037850425963970342060045)
                  ·
                    refine ⟨10889193909736488878272517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29037850425963970342060045 10889193909736488878272517)
                    ·
                      refine ⟨2041723858075591664676097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10889193909736488878272517 2041723858075591664676097)
                      ·
                        rfl

theorem cell23_3976243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_3976243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976243 prefixEnd_3976243 := by exact prefixLift 3976243
  have htrace : WordTrace (prefixWord ++ tailWord_3976243) baseStart_3976243 baseEnd_3976243 := by
    simpa [prefixWord, tailWord_3976243, baseEnd_3976243] using wordTrace_append hprefix tailTrace_3976243
  have hstable : (prefixWord ++ tailWord_3976243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976243).length < 2 ^ (prefixWord ++ tailWord_3976243).sum := by decide
  have hdescent : baseEnd_3976243 < baseStart_3976243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976277 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3976277 : Nat := 118140960795 + 3976277 * 2 ^ 59
def prefixEnd_3976277 : Nat := 4983230072969 + 3 ^ 40 * 3976277 * 2
def baseEnd_3976277 : Nat := 2041741316417844531650941

theorem tailTrace_3976277 : CollatzResearch.WordTrace tailWord_3976277 prefixEnd_3976277 2041741316417844531650941 := by
  unfold tailWord_3976277
  simp only [CollatzResearch.WordTrace]
  refine ⟨145026736615634997891271085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96684491077089998594180723 145026736615634997891271085)
  ·
    refine ⟨54385026230863124209226657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145026736615634997891271085 54385026230863124209226657)
    ·
      refine ⟨40788769673147343156919993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54385026230863124209226657 40788769673147343156919993)
      ·
        refine ⟨30591577254860507367689995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40788769673147343156919993 30591577254860507367689995)
        ·
          refine ⟨45887365882290761051534993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30591577254860507367689995 45887365882290761051534993)
          ·
            refine ⟨34415524411718070788651245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45887365882290761051534993 34415524411718070788651245)
            ·
              refine ⟨12905821654394276545744217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34415524411718070788651245 12905821654394276545744217)
              ·
                refine ⟨9679366240795707409308163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12905821654394276545744217 9679366240795707409308163)
                ·
                  refine ⟨14519049361193561113962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679366240795707409308163 14519049361193561113962245)
                  ·
                    refine ⟨2722321755223792708867921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14519049361193561113962245 2722321755223792708867921)
                    ·
                      refine ⟨2041741316417844531650941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722321755223792708867921 2041741316417844531650941)
                      ·
                        rfl

theorem cell23_3976277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3976277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976277 prefixEnd_3976277 := by exact prefixLift 3976277
  have htrace : WordTrace (prefixWord ++ tailWord_3976277) baseStart_3976277 baseEnd_3976277 := by
    simpa [prefixWord, tailWord_3976277, baseEnd_3976277] using wordTrace_append hprefix tailTrace_3976277
  have hstable : (prefixWord ++ tailWord_3976277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976277).length < 2 ^ (prefixWord ++ tailWord_3976277).sum := by decide
  have hdescent : baseEnd_3976277 < baseStart_3976277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976330 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_3976330 : Nat := 118140960795 + 3976330 * 2 ^ 59
def prefixEnd_3976330 : Nat := 4983230072969 + 3 ^ 40 * 3976330 * 2
def baseEnd_3976330 : Nat := 680589510297510941429399

theorem tailTrace_3976330 : CollatzResearch.WordTrace tailWord_3976330 prefixEnd_3976330 680589510297510941429399 := by
  unfold tailWord_3976330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257167421110746985737611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96685779789628658628633629 36257167421110746985737611)
  ·
    refine ⟨54385751131666120478606417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36257167421110746985737611 54385751131666120478606417)
    ·
      refine ⟨40789313348749590358954813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54385751131666120478606417 40789313348749590358954813)
      ·
        refine ⟨15295992505781096384608055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40789313348749590358954813 15295992505781096384608055)
        ·
          refine ⟨22943988758671644576912083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295992505781096384608055 22943988758671644576912083)
          ·
            refine ⟨34415983138007466865368125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943988758671644576912083 34415983138007466865368125)
            ·
              refine ⟨12905993676752800074513047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34415983138007466865368125 12905993676752800074513047)
              ·
                refine ⟨19358990515129200111769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905993676752800074513047 19358990515129200111769571)
                ·
                  refine ⟨29038485772693800167654357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358990515129200111769571 29038485772693800167654357)
                  ·
                    refine ⟨680589510297510941429399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29038485772693800167654357 680589510297510941429399)
                    ·
                      rfl

theorem cell23_3976330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_3976330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976330 prefixEnd_3976330 := by exact prefixLift 3976330
  have htrace : WordTrace (prefixWord ++ tailWord_3976330) baseStart_3976330 baseEnd_3976330 := by
    simpa [prefixWord, tailWord_3976330, baseEnd_3976330] using wordTrace_append hprefix tailTrace_3976330
  have hstable : (prefixWord ++ tailWord_3976330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976330).length < 2 ^ (prefixWord ++ tailWord_3976330).sum := by decide
  have hdescent : baseEnd_3976330 < baseStart_3976330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976334 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_3976334 : Nat := 118140960795 + 3976334 * 2 ^ 59
def prefixEnd_3976334 : Nat := 4983230072969 + 3 ^ 40 * 3976334 * 2
def baseEnd_3976334 : Nat := 226863398312794534293131

theorem tailTrace_3976334 : CollatzResearch.WordTrace tailWord_3976334 prefixEnd_3976334 226863398312794534293131 := by
  unfold tailWord_3976334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128601947053562078262007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96685877050952331084064037 18128601947053562078262007)
  ·
    refine ⟨27192902920580343117393011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18128601947053562078262007 27192902920580343117393011)
    ·
      refine ⟨40789354380870514676089517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27192902920580343117393011 40789354380870514676089517)
      ·
        refine ⟨15296007892826443003533569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40789354380870514676089517 15296007892826443003533569)
        ·
          refine ⟨11472005919619832252650177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15296007892826443003533569 11472005919619832252650177)
          ·
            refine ⟨8604004439714874189487633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11472005919619832252650177 8604004439714874189487633)
            ·
              refine ⟨6453003329786155642115725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8604004439714874189487633 6453003329786155642115725)
              ·
                refine ⟨2419876248669808365793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6453003329786155642115725 2419876248669808365793397)
                ·
                  refine ⟨226863398312794534293131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419876248669808365793397 226863398312794534293131)
                  ·
                    rfl

theorem cell23_3976334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_3976334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976334 prefixEnd_3976334 := by exact prefixLift 3976334
  have htrace : WordTrace (prefixWord ++ tailWord_3976334) baseStart_3976334 baseEnd_3976334 := by
    simpa [prefixWord, tailWord_3976334, baseEnd_3976334] using wordTrace_append hprefix tailTrace_3976334
  have hstable : (prefixWord ++ tailWord_3976334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976334).length < 2 ^ (prefixWord ++ tailWord_3976334).sum := by decide
  have hdescent : baseEnd_3976334 < baseStart_3976334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_3976363 : Nat := 118140960795 + 3976363 * 2 ^ 59
def prefixEnd_3976363 : Nat := 4983230072969 + 3 ^ 40 * 3976363 * 2
def baseEnd_3976363 : Nat := 2041785475754131195175545

theorem tailTrace_3976363 : CollatzResearch.WordTrace tailWord_3976363 prefixEnd_3976363 2041785475754131195175545 := by
  unfold tailWord_3976363
  simp only [CollatzResearch.WordTrace]
  refine ⟨145029873293323434578901743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96686582195548956385934495 145029873293323434578901743)
  ·
    refine ⟨217544809939985151868352615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145029873293323434578901743 217544809939985151868352615)
    ·
      refine ⟨326317214909977727802528923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217544809939985151868352615 326317214909977727802528923)
      ·
        refine ⟨489475822364966591703793385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326317214909977727802528923 489475822364966591703793385)
        ·
          refine ⟨367106866773724943777845039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489475822364966591703793385 367106866773724943777845039)
          ·
            refine ⟨550660300160587415666767559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367106866773724943777845039 550660300160587415666767559)
            ·
              refine ⟨825990450240881123500151339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550660300160587415666767559 825990450240881123500151339)
              ·
                refine ⟨1238985675361321685250227009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825990450240881123500151339 1238985675361321685250227009)
                ·
                  refine ⟨929239256520991263937670257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238985675361321685250227009 929239256520991263937670257)
                  ·
                    refine ⟨696929442390743447953252693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929239256520991263937670257 696929442390743447953252693)
                    ·
                      refine ⟨2041785475754131195175545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 696929442390743447953252693 2041785475754131195175545)
                      ·
                        rfl

theorem cell23_3976363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_3976363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976363 prefixEnd_3976363 := by exact prefixLift 3976363
  have htrace : WordTrace (prefixWord ++ tailWord_3976363) baseStart_3976363 baseEnd_3976363 := by
    simpa [prefixWord, tailWord_3976363, baseEnd_3976363] using wordTrace_append hprefix tailTrace_3976363
  have hstable : (prefixWord ++ tailWord_3976363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976363).length < 2 ^ (prefixWord ++ tailWord_3976363).sum := by decide
  have hdescent : baseEnd_3976363 < baseStart_3976363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976367 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 4, 2]
def baseStart_3976367 : Nat := 118140960795 + 3976367 * 2 ^ 59
def prefixEnd_3976367 : Nat := 4983230072969 + 3 ^ 40 * 3976367 * 2
def baseEnd_3976367 : Nat := 2041787529676749179525527

theorem tailTrace_3976367 : CollatzResearch.WordTrace tailWord_3976367 prefixEnd_3976367 2041787529676749179525527 := by
  unfold tailWord_3976367
  simp only [CollatzResearch.WordTrace]
  refine ⟨145030019185308943262047355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96686679456872628841364903 145030019185308943262047355)
  ·
    refine ⟨217545028777963414893071033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145030019185308943262047355 217545028777963414893071033)
    ·
      refine ⟨163158771583472561169803275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217545028777963414893071033 163158771583472561169803275)
      ·
        refine ⟨244738157375208841754704913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163158771583472561169803275 244738157375208841754704913)
        ·
          refine ⟨183553618031406631316028685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244738157375208841754704913 183553618031406631316028685)
          ·
            refine ⟨68832606761777486743510757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183553618031406631316028685 68832606761777486743510757)
            ·
              refine ⟨12906113767833278764408267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68832606761777486743510757 12906113767833278764408267)
              ·
                refine ⟨19359170651749918146612401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12906113767833278764408267 19359170651749918146612401)
                ·
                  refine ⟨14519377988812438609959301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19359170651749918146612401 14519377988812438609959301)
                  ·
                    refine ⟨2722383372902332239367369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14519377988812438609959301 2722383372902332239367369)
                    ·
                      refine ⟨2041787529676749179525527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722383372902332239367369 2041787529676749179525527)
                      ·
                        rfl

theorem cell23_3976367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4, 2].length) (baseStart_3976367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976367 prefixEnd_3976367 := by exact prefixLift 3976367
  have htrace : WordTrace (prefixWord ++ tailWord_3976367) baseStart_3976367 baseEnd_3976367 := by
    simpa [prefixWord, tailWord_3976367, baseEnd_3976367] using wordTrace_append hprefix tailTrace_3976367
  have hstable : (prefixWord ++ tailWord_3976367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976367).length < 2 ^ (prefixWord ++ tailWord_3976367).sum := by decide
  have hdescent : baseEnd_3976367 < baseStart_3976367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976377 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_3976377 : Nat := 118140960795 + 3976377 * 2 ^ 59
def prefixEnd_3976377 : Nat := 4983230072969 + 3 ^ 40 * 3976377 * 2
def baseEnd_3976377 : Nat := 680597554827764713466827

theorem tailTrace_3976377 : CollatzResearch.WordTrace tailWord_3976377 prefixEnd_3976377 680597554827764713466827 := by
  unfold tailWord_3976377
  simp only [CollatzResearch.WordTrace]
  refine ⟨145030383915272714969911385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96686922610181809979940923 145030383915272714969911385)
  ·
    refine ⟨108772787936454536227433539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145030383915272714969911385 108772787936454536227433539)
    ·
      refine ⟨163159181904681804341150309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108772787936454536227433539 163159181904681804341150309)
      ·
        refine ⟨30592346607127838313965683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163159181904681804341150309 30592346607127838313965683)
        ·
          refine ⟨45888519910691757470948525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30592346607127838313965683 45888519910691757470948525)
          ·
            refine ⟨17208194966509409051605697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45888519910691757470948525 17208194966509409051605697)
            ·
              refine ⟨12906146224882056788704273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17208194966509409051605697 12906146224882056788704273)
              ·
                refine ⟨9679609668661542591528205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12906146224882056788704273 9679609668661542591528205)
                ·
                  refine ⟨3629853625748078471823077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9679609668661542591528205 3629853625748078471823077)
                  ·
                    refine ⟨680597554827764713466827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629853625748078471823077 680597554827764713466827)
                    ·
                      rfl

theorem cell23_3976377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_3976377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976377 prefixEnd_3976377 := by exact prefixLift 3976377
  have htrace : WordTrace (prefixWord ++ tailWord_3976377) baseStart_3976377 baseEnd_3976377 := by
    simpa [prefixWord, tailWord_3976377, baseEnd_3976377] using wordTrace_append hprefix tailTrace_3976377
  have hstable : (prefixWord ++ tailWord_3976377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976377).length < 2 ^ (prefixWord ++ tailWord_3976377).sum := by decide
  have hdescent : baseEnd_3976377 < baseStart_3976377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976484 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_3976484 : Nat := 118140960795 + 3976484 * 2 ^ 59
def prefixEnd_3976484 : Nat := 4983230072969 + 3 ^ 40 * 3976484 * 2
def baseEnd_3976484 : Nat := 680615868971108407254163

theorem tailTrace_3976484 : CollatzResearch.WordTrace tailWord_3976484 prefixEnd_3976484 680615868971108407254163 := by
  unfold tailWord_3976484
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517143262942536122028253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96689524350590048162704337 72517143262942536122028253)
  ·
    refine ⟨27193928723603451045760595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72517143262942536122028253 27193928723603451045760595)
    ·
      refine ⟨40790893085405176568640893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27193928723603451045760595 40790893085405176568640893)
      ·
        refine ⟨15296584907026941213240335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40790893085405176568640893 15296584907026941213240335)
        ·
          refine ⟨22944877360540411819860503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296584907026941213240335 22944877360540411819860503)
          ·
            refine ⟨34417316040810617729790755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22944877360540411819860503 34417316040810617729790755)
            ·
              refine ⟨51625974061215926594686133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34417316040810617729790755 51625974061215926594686133)
              ·
                refine ⟨4839935068238993118251825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51625974061215926594686133 4839935068238993118251825)
                ·
                  refine ⟨3629951301179244838688869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839935068238993118251825 3629951301179244838688869)
                  ·
                    refine ⟨680615868971108407254163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629951301179244838688869 680615868971108407254163)
                    ·
                      rfl

theorem cell23_3976484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_3976484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976484 prefixEnd_3976484 := by exact prefixLift 3976484
  have htrace : WordTrace (prefixWord ++ tailWord_3976484) baseStart_3976484 baseEnd_3976484 := by
    simpa [prefixWord, tailWord_3976484, baseEnd_3976484] using wordTrace_append hprefix tailTrace_3976484
  have hstable : (prefixWord ++ tailWord_3976484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976484).length < 2 ^ (prefixWord ++ tailWord_3976484).sum := by decide
  have hdescent : baseEnd_3976484 < baseStart_3976484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976502 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3976502 : Nat := 118140960795 + 3976502 * 2 ^ 59
def prefixEnd_3976502 : Nat := 4983230072969 + 3 ^ 40 * 3976502 * 2
def baseEnd_3976502 : Nat := 2041856849565106151337407

theorem tailTrace_3976502 : CollatzResearch.WordTrace tailWord_3976502 prefixEnd_3976502 2041856849565106151337407 := by
  unfold tailWord_3976502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9064683939988741332388235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96689962026546574212141173 9064683939988741332388235)
  ·
    refine ⟨13597025909983111998582353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9064683939988741332388235 13597025909983111998582353)
    ·
      refine ⟨10197769432487333998936765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13597025909983111998582353 10197769432487333998936765)
      ·
        refine ⟨3824163537182750249601287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10197769432487333998936765 3824163537182750249601287)
        ·
          refine ⟨5736245305774125374401931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824163537182750249601287 5736245305774125374401931)
          ·
            refine ⟨8604367958661188061602897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736245305774125374401931 8604367958661188061602897)
            ·
              refine ⟨6453275968995891046202173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8604367958661188061602897 6453275968995891046202173)
              ·
                refine ⟨2419978488373459142325815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6453275968995891046202173 2419978488373459142325815)
                ·
                  refine ⟨3629967732560188713488723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419978488373459142325815 3629967732560188713488723)
                  ·
                    refine ⟨5444951598840283070233085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3629967732560188713488723 5444951598840283070233085)
                    ·
                      refine ⟨2041856849565106151337407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444951598840283070233085 2041856849565106151337407)
                      ·
                        rfl

theorem cell23_3976502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3976502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976502 prefixEnd_3976502 := by exact prefixLift 3976502
  have htrace : WordTrace (prefixWord ++ tailWord_3976502) baseStart_3976502 baseEnd_3976502 := by
    simpa [prefixWord, tailWord_3976502, baseEnd_3976502] using wordTrace_append hprefix tailTrace_3976502
  have hstable : (prefixWord ++ tailWord_3976502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976502).length < 2 ^ (prefixWord ++ tailWord_3976502).sum := by decide
  have hdescent : baseEnd_3976502 < baseStart_3976502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976508 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_3976508 : Nat := 118140960795 + 3976508 * 2 ^ 59
def prefixEnd_3976508 : Nat := 4983230072969 + 3 ^ 40 * 3976508 * 2
def baseEnd_3976508 : Nat := 2041859930449033127862379

theorem tailTrace_3976508 : CollatzResearch.WordTrace tailWord_3976508 prefixEnd_3976508 2041859930449033127862379 := by
  unfold tailWord_3976508
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517580938899062171465089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96690107918532082895286785 72517580938899062171465089)
  ·
    refine ⟨54388185704174296628598817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72517580938899062171465089 54388185704174296628598817)
    ·
      refine ⟨40791139278130722471449113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54388185704174296628598817 40791139278130722471449113)
      ·
        refine ⟨30593354458598041853586835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40791139278130722471449113 30593354458598041853586835)
        ·
          refine ⟨45890031687897062780380253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30593354458598041853586835 45890031687897062780380253)
          ·
            refine ⟨17208761882961398542642595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45890031687897062780380253 17208761882961398542642595)
            ·
              refine ⟨25813142824442097813963893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208761882961398542642595 25813142824442097813963893)
              ·
                refine ⟨2419982139791446670059115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25813142824442097813963893 2419982139791446670059115)
                ·
                  refine ⟨3629973209687170005088673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419982139791446670059115 3629973209687170005088673)
                  ·
                    refine ⟨2722479907265377503816505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3629973209687170005088673 2722479907265377503816505)
                    ·
                      refine ⟨2041859930449033127862379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722479907265377503816505 2041859930449033127862379)
                      ·
                        rfl

theorem cell23_3976508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_3976508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976508 prefixEnd_3976508 := by exact prefixLift 3976508
  have htrace : WordTrace (prefixWord ++ tailWord_3976508) baseStart_3976508 baseEnd_3976508 := by
    simpa [prefixWord, tailWord_3976508, baseEnd_3976508] using wordTrace_append hprefix tailTrace_3976508
  have hstable : (prefixWord ++ tailWord_3976508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976508).length < 2 ^ (prefixWord ++ tailWord_3976508).sum := by decide
  have hdescent : baseEnd_3976508 < baseStart_3976508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976511 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 1, 2, 3]
def baseStart_3976511 : Nat := 118140960795 + 3976511 * 2 ^ 59
def prefixEnd_3976511 : Nat := 4983230072969 + 3 ^ 40 * 3976511 * 2
def baseEnd_3976511 : Nat := 2041861470890996616124865

theorem tailTrace_3976511 : CollatzResearch.WordTrace tailWord_3976511 prefixEnd_3976511 2041861470890996616124865 := by
  unfold tailWord_3976511
  simp only [CollatzResearch.WordTrace]
  refine ⟨145035271296787255855289387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96690180864524837236859591 145035271296787255855289387)
  ·
    refine ⟨217552906945180883782934081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145035271296787255855289387 217552906945180883782934081)
    ·
      refine ⟨163164680208885662837200561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217552906945180883782934081 163164680208885662837200561)
      ·
        refine ⟨122373510156664247127900421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163164680208885662837200561 122373510156664247127900421)
        ·
          refine ⟨22945033154374546336481329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122373510156664247127900421 22945033154374546336481329)
          ·
            refine ⟨17208774865780909752360997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22945033154374546336481329 17208774865780909752360997)
            ·
              refine ⟨3226645287333920578567687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17208774865780909752360997 3226645287333920578567687)
              ·
                refine ⟨4839967931000880867851531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226645287333920578567687 4839967931000880867851531)
                ·
                  refine ⟨7259951896501321301777297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839967931000880867851531 7259951896501321301777297)
                  ·
                    refine ⟨5444963922375990976332973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259951896501321301777297 5444963922375990976332973)
                    ·
                      refine ⟨2041861470890996616124865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5444963922375990976332973 2041861470890996616124865)
                      ·
                        rfl

theorem cell23_3976511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_3976511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976511 prefixEnd_3976511 := by exact prefixLift 3976511
  have htrace : WordTrace (prefixWord ++ tailWord_3976511) baseStart_3976511 baseEnd_3976511 := by
    simpa [prefixWord, tailWord_3976511, baseEnd_3976511] using wordTrace_append hprefix tailTrace_3976511
  have hstable : (prefixWord ++ tailWord_3976511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976511).length < 2 ^ (prefixWord ++ tailWord_3976511).sum := by decide
  have hdescent : baseEnd_3976511 < baseStart_3976511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976567 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3976567 : Nat := 118140960795 + 3976567 * 2 ^ 59
def prefixEnd_3976567 : Nat := 4983230072969 + 3 ^ 40 * 3976567 * 2
def baseEnd_3976567 : Nat := 2041890225807648397024607

theorem tailTrace_3976567 : CollatzResearch.WordTrace tailWord_3976567 prefixEnd_3976567 2041890225807648397024607 := by
  unfold tailWord_3976567
  simp only [CollatzResearch.WordTrace]
  refine ⟨145037313784584377419327955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96691542523056251612885303 145037313784584377419327955)
  ·
    refine ⟨217555970676876566128991933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145037313784584377419327955 217555970676876566128991933)
    ·
      refine ⟨81583489003828712298371975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217555970676876566128991933 81583489003828712298371975)
      ·
        refine ⟨122375233505743068447557963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81583489003828712298371975 122375233505743068447557963)
        ·
          refine ⟨183562850258614602671336945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122375233505743068447557963 183562850258614602671336945)
          ·
            refine ⟨137672137693960952003502709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183562850258614602671336945 137672137693960952003502709)
            ·
              refine ⟨12906762908808839250328379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137672137693960952003502709 12906762908808839250328379)
              ·
                refine ⟨19360144363213258875492569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12906762908808839250328379 19360144363213258875492569)
                ·
                  refine ⟨14520108272409944156619427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19360144363213258875492569 14520108272409944156619427)
                  ·
                    refine ⟨21780162408614916234929141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14520108272409944156619427 21780162408614916234929141)
                    ·
                      refine ⟨2041890225807648397024607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21780162408614916234929141 2041890225807648397024607)
                      ·
                        rfl

theorem cell23_3976567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3976567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976567 prefixEnd_3976567 := by exact prefixLift 3976567
  have htrace : WordTrace (prefixWord ++ tailWord_3976567) baseStart_3976567 baseEnd_3976567 := by
    simpa [prefixWord, tailWord_3976567, baseEnd_3976567] using wordTrace_append hprefix tailTrace_3976567
  have hstable : (prefixWord ++ tailWord_3976567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976567).length < 2 ^ (prefixWord ++ tailWord_3976567).sum := by decide
  have hdescent : baseEnd_3976567 < baseStart_3976567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976581 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_3976581 : Nat := 118140960795 + 3976581 * 2 ^ 59
def prefixEnd_3976581 : Nat := 4983230072969 + 3 ^ 40 * 3976581 * 2
def baseEnd_3976581 : Nat := 2041897414536811342249543

theorem tailTrace_3976581 : CollatzResearch.WordTrace tailWord_3976581 prefixEnd_3976581 2041897414536811342249543 := by
  unfold tailWord_3976581
  simp only [CollatzResearch.WordTrace]
  refine ⟨145037824406533657810337597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96691882937689105206891731 145037824406533657810337597)
  ·
    refine ⟨54389184152450121678876599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145037824406533657810337597 54389184152450121678876599)
    ·
      refine ⟨81583776228675182518314899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54389184152450121678876599 81583776228675182518314899)
      ·
        refine ⟨122375664343012773777472349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81583776228675182518314899 122375664343012773777472349)
        ·
          refine ⟨45890874128629790166552131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122375664343012773777472349 45890874128629790166552131)
          ·
            refine ⟨68836311192944685249828197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45890874128629790166552131 68836311192944685249828197)
            ·
              refine ⟨12906808348677128484342787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68836311192944685249828197 12906808348677128484342787)
              ·
                refine ⟨19360212523015692726514181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12906808348677128484342787 19360212523015692726514181)
                ·
                  refine ⟨3630039848065442386221409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19360212523015692726514181 3630039848065442386221409)
                  ·
                    refine ⟨2722529886049081789666057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3630039848065442386221409 2722529886049081789666057)
                    ·
                      refine ⟨2041897414536811342249543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722529886049081789666057 2041897414536811342249543)
                      ·
                        rfl

theorem cell23_3976581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_3976581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976581 prefixEnd_3976581 := by exact prefixLift 3976581
  have htrace : WordTrace (prefixWord ++ tailWord_3976581) baseStart_3976581 baseEnd_3976581 := by
    simpa [prefixWord, tailWord_3976581, baseEnd_3976581] using wordTrace_append hprefix tailTrace_3976581
  have hstable : (prefixWord ++ tailWord_3976581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976581).length < 2 ^ (prefixWord ++ tailWord_3976581).sum := by decide
  have hdescent : baseEnd_3976581 < baseStart_3976581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976654 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3976654 : Nat := 118140960795 + 3976654 * 2 ^ 59
def prefixEnd_3976654 : Nat := 4983230072969 + 3 ^ 40 * 3976654 * 2
def baseEnd_3976654 : Nat := 2041934898624589556636707

theorem tailTrace_3976654 : CollatzResearch.WordTrace tailWord_3976654 prefixEnd_3976654 2041934898624589556636707 := by
  unfold tailWord_3976654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18130060866908648909718127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96693657956846127518496677 18130060866908648909718127)
  ·
    refine ⟨27195091300362973364577191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18130060866908648909718127 27195091300362973364577191)
    ·
      refine ⟨40792636950544460046865787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27195091300362973364577191 40792636950544460046865787)
      ·
        refine ⟨61188955425816690070298681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40792636950544460046865787 61188955425816690070298681)
        ·
          refine ⟨45891716569362517552724011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61188955425816690070298681 45891716569362517552724011)
          ·
            refine ⟨68837574854043776329086017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45891716569362517552724011 68837574854043776329086017)
            ·
              refine ⟨51628181140532832246814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68837574854043776329086017 51628181140532832246814513)
              ·
                refine ⟨38721135855399624185110885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51628181140532832246814513 38721135855399624185110885)
                ·
                  refine ⟨7260212972887429534708291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38721135855399624185110885 7260212972887429534708291)
                  ·
                    refine ⟨10890319459331144302062437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260212972887429534708291 10890319459331144302062437)
                    ·
                      refine ⟨2041934898624589556636707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10890319459331144302062437 2041934898624589556636707)
                      ·
                        rfl

theorem cell23_3976654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3976654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976654 prefixEnd_3976654 := by exact prefixLift 3976654
  have htrace : WordTrace (prefixWord ++ tailWord_3976654) baseStart_3976654 baseEnd_3976654 := by
    simpa [prefixWord, tailWord_3976654, baseEnd_3976654] using wordTrace_append hprefix tailTrace_3976654
  have hstable : (prefixWord ++ tailWord_3976654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976654).length < 2 ^ (prefixWord ++ tailWord_3976654).sum := by decide
  have hdescent : baseEnd_3976654 < baseStart_3976654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976664 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_3976664 : Nat := 118140960795 + 3976664 * 2 ^ 59
def prefixEnd_3976664 : Nat := 4983230072969 + 3 ^ 40 * 3976664 * 2
def baseEnd_3976664 : Nat := 680646677810378172503887

theorem tailTrace_3976664 : CollatzResearch.WordTrace tailWord_3976664 prefixEnd_3976664 680646677810378172503887 := by
  unfold tailWord_3976664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72520425832616481492804523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96693901110155308657072697 72520425832616481492804523)
  ·
    refine ⟨108780638748924722239206785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72520425832616481492804523 108780638748924722239206785)
    ·
      refine ⟨81585479061693541679405089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108780638748924722239206785 81585479061693541679405089)
      ·
        refine ⟨61189109296270156259553817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81585479061693541679405089 61189109296270156259553817)
        ·
          refine ⟨45891831972202617194665363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61189109296270156259553817 45891831972202617194665363)
          ·
            refine ⟨68837747958303925791998045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45891831972202617194665363 68837747958303925791998045)
            ·
              refine ⟨25814155484363972171999267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68837747958303925791998045 25814155484363972171999267)
              ·
                refine ⟨38721233226545958257998901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25814155484363972171999267 38721233226545958257998901)
                ·
                  refine ⟨3630115614988683586687397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38721233226545958257998901 3630115614988683586687397)
                  ·
                    refine ⟨680646677810378172503887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630115614988683586687397 680646677810378172503887)
                    ·
                      rfl

theorem cell23_3976664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_3976664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976664 prefixEnd_3976664 := by exact prefixLift 3976664
  have htrace : WordTrace (prefixWord ++ tailWord_3976664) baseStart_3976664 baseEnd_3976664 := by
    simpa [prefixWord, tailWord_3976664, baseEnd_3976664] using wordTrace_append hprefix tailTrace_3976664
  have hstable : (prefixWord ++ tailWord_3976664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976664).length < 2 ^ (prefixWord ++ tailWord_3976664).sum := by decide
  have hdescent : baseEnd_3976664 < baseStart_3976664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_3976667 : Nat := 118140960795 + 3976667 * 2 ^ 59
def prefixEnd_3976667 : Nat := 4983230072969 + 3 ^ 40 * 3976667 * 2
def baseEnd_3976667 : Nat := 2041941573873098005774147

theorem tailTrace_3976667 : CollatzResearch.WordTrace tailWord_3976667 prefixEnd_3976667 2041941573873098005774147 := by
  unfold tailWord_3976667
  simp only [CollatzResearch.WordTrace]
  refine ⟨145040961084222094497968255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96693974056148062998645503 145040961084222094497968255)
  ·
    refine ⟨217561441626333141746952383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145040961084222094497968255 217561441626333141746952383)
    ·
      refine ⟨326342162439499712620428575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217561441626333141746952383 326342162439499712620428575)
      ·
        refine ⟨489513243659249568930642863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326342162439499712620428575 489513243659249568930642863)
        ·
          refine ⟨734269865488874353395964295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489513243659249568930642863 734269865488874353395964295)
          ·
            refine ⟨1101404798233311530093946443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734269865488874353395964295 1101404798233311530093946443)
            ·
              refine ⟨1652107197349967295140919665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101404798233311530093946443 1652107197349967295140919665)
              ·
                refine ⟨1239080398012475471355689749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652107197349967295140919665 1239080398012475471355689749)
                ·
                  refine ⟨58081893656834787719797957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1239080398012475471355689749 58081893656834787719797957)
                  ·
                    refine ⟨10890355060656522697462117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58081893656834787719797957 10890355060656522697462117)
                    ·
                      refine ⟨2041941573873098005774147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10890355060656522697462117 2041941573873098005774147)
                      ·
                        rfl

theorem cell23_3976667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_3976667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976667 prefixEnd_3976667 := by exact prefixLift 3976667
  have htrace : WordTrace (prefixWord ++ tailWord_3976667) baseStart_3976667 baseEnd_3976667 := by
    simpa [prefixWord, tailWord_3976667, baseEnd_3976667] using wordTrace_append hprefix tailTrace_3976667
  have hstable : (prefixWord ++ tailWord_3976667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976667).length < 2 ^ (prefixWord ++ tailWord_3976667).sum := by decide
  have hdescent : baseEnd_3976667 < baseStart_3976667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976707 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 9]
def baseStart_3976707 : Nat := 118140960795 + 3976707 * 2 ^ 59
def prefixEnd_3976707 : Nat := 4983230072969 + 3 ^ 40 * 3976707 * 2
def baseEnd_3976707 : Nat := 680654037699759283091321

theorem tailTrace_3976707 : CollatzResearch.WordTrace tailWord_3976707 prefixEnd_3976707 680654037699759283091321 := by
  unfold tailWord_3976707
  simp only [CollatzResearch.WordTrace]
  refine ⟨145042420004077181329424375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96694946669384787552949583 145042420004077181329424375)
  ·
    refine ⟨217563630006115771994136563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145042420004077181329424375 217563630006115771994136563)
    ·
      refine ⟨326345445009173657991204845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217563630006115771994136563 326345445009173657991204845)
      ·
        refine ⟨122379541878440121746701817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326345445009173657991204845 122379541878440121746701817)
        ·
          refine ⟨91784656408830091310026363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122379541878440121746701817 91784656408830091310026363)
          ·
            refine ⟨137676984613245136965039545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91784656408830091310026363 137676984613245136965039545)
            ·
              refine ⟨103257738459933852723779659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137676984613245136965039545 103257738459933852723779659)
              ·
                refine ⟨154886607689900779085669489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103257738459933852723779659 154886607689900779085669489)
                ·
                  refine ⟨116164955767425584314252117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154886607689900779085669489 116164955767425584314252117)
                  ·
                    refine ⟨680654037699759283091321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116164955767425584314252117 680654037699759283091321)
                    ·
                      rfl

theorem cell23_3976707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_3976707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976707 prefixEnd_3976707 := by exact prefixLift 3976707
  have htrace : WordTrace (prefixWord ++ tailWord_3976707) baseStart_3976707 baseEnd_3976707 := by
    simpa [prefixWord, tailWord_3976707, baseEnd_3976707] using wordTrace_append hprefix tailTrace_3976707
  have hstable : (prefixWord ++ tailWord_3976707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976707).length < 2 ^ (prefixWord ++ tailWord_3976707).sum := by decide
  have hdescent : baseEnd_3976707 < baseStart_3976707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976721 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_3976721 : Nat := 118140960795 + 3976721 * 2 ^ 59
def prefixEnd_3976721 : Nat := 4983230072969 + 3 ^ 40 * 3976721 * 2
def baseEnd_3976721 : Nat := 2041969301828440794498899

theorem tailTrace_3976721 : CollatzResearch.WordTrace tailWord_3976721 prefixEnd_3976721 2041969301828440794498899 := by
  unfold tailWord_3976721
  simp only [CollatzResearch.WordTrace]
  refine ⟨145042930626026461720434017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96695287084017641146956011 145042930626026461720434017)
  ·
    refine ⟨108782197969519846290325513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145042930626026461720434017 108782197969519846290325513)
    ·
      refine ⟨81586648477139884717744135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108782197969519846290325513 81586648477139884717744135)
      ·
        refine ⟨122379972715709827076616203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81586648477139884717744135 122379972715709827076616203)
        ·
          refine ⟨183569959073564740614924305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122379972715709827076616203 183569959073564740614924305)
          ·
            refine ⟨137677469305173555461193229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183569959073564740614924305 137677469305173555461193229)
            ·
              refine ⟨51629050989440083297947461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137677469305173555461193229 51629050989440083297947461)
              ·
                refine ⟨9680447060520015618365149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51629050989440083297947461 9680447060520015618365149)
                ·
                  refine ⟨3630167647695005856886931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9680447060520015618365149 3630167647695005856886931)
                  ·
                    refine ⟨5445251471542508785330397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630167647695005856886931 5445251471542508785330397)
                    ·
                      refine ⟨2041969301828440794498899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445251471542508785330397 2041969301828440794498899)
                      ·
                        rfl

theorem cell23_3976721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_3976721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976721 prefixEnd_3976721 := by exact prefixLift 3976721
  have htrace : WordTrace (prefixWord ++ tailWord_3976721) baseStart_3976721 baseEnd_3976721 := by
    simpa [prefixWord, tailWord_3976721, baseEnd_3976721] using wordTrace_append hprefix tailTrace_3976721
  have hstable : (prefixWord ++ tailWord_3976721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976721).length < 2 ^ (prefixWord ++ tailWord_3976721).sum := by decide
  have hdescent : baseEnd_3976721 < baseStart_3976721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976775 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 1, 5]
def baseStart_3976775 : Nat := 118140960795 + 3976775 * 2 ^ 59
def prefixEnd_3976775 : Nat := 4983230072969 + 3 ^ 40 * 3976775 * 2
def baseEnd_3976775 : Nat := 680665676594594527741217

theorem tailTrace_3976775 : CollatzResearch.WordTrace tailWord_3976775 prefixEnd_3976775 680665676594594527741217 := by
  unfold tailWord_3976775
  simp only [CollatzResearch.WordTrace]
  refine ⟨145044900167830828942899779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96696600111887219295266519 145044900167830828942899779)
  ·
    refine ⟨217567350251746243414349669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145044900167830828942899779 217567350251746243414349669)
    ·
      refine ⟨40793878172202420640190563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217567350251746243414349669 40793878172202420640190563)
      ·
        refine ⟨61190817258303630960285845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40793878172202420640190563 61190817258303630960285845)
        ·
          refine ⟨2868319558982982701263399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61190817258303630960285845 2868319558982982701263399)
          ·
            refine ⟨4302479338474474051895099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868319558982982701263399 4302479338474474051895099)
            ·
              refine ⟨6453719007711711077842649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302479338474474051895099 6453719007711711077842649)
              ·
                refine ⟨4840289255783783308381987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453719007711711077842649 4840289255783783308381987)
                ·
                  refine ⟨7260433883675674962572981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840289255783783308381987 7260433883675674962572981)
                  ·
                    refine ⟨680665676594594527741217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7260433883675674962572981 680665676594594527741217)
                    ·
                      rfl

theorem cell23_3976775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_3976775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976775 prefixEnd_3976775 := by exact prefixLift 3976775
  have htrace : WordTrace (prefixWord ++ tailWord_3976775) baseStart_3976775 baseEnd_3976775 := by
    simpa [prefixWord, tailWord_3976775, baseEnd_3976775] using wordTrace_append hprefix tailTrace_3976775
  have hstable : (prefixWord ++ tailWord_3976775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976775).length < 2 ^ (prefixWord ++ tailWord_3976775).sum := by decide
  have hdescent : baseEnd_3976775 < baseStart_3976775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976778 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_3976778 : Nat := 118140960795 + 3976778 * 2 ^ 59
def prefixEnd_3976778 : Nat := 4983230072969 + 3 ^ 40 * 3976778 * 2
def baseEnd_3976778 : Nat := 2041998570225747071486137

theorem tailTrace_3976778 : CollatzResearch.WordTrace tailWord_3976778 prefixEnd_3976778 2041998570225747071486137 := by
  unfold tailWord_3976778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261252396704990113814747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96696673057879973636839325 36261252396704990113814747)
  ·
    refine ⟨54391878595057485170722121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36261252396704990113814747 54391878595057485170722121)
    ·
      refine ⟨40793908946293113878041591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54391878595057485170722121 40793908946293113878041591)
      ·
        refine ⟨61190863419439670817062387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40793908946293113878041591 61190863419439670817062387)
        ·
          refine ⟨91786295129159506225593581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61190863419439670817062387 91786295129159506225593581)
          ·
            refine ⟨34419860673434814834597593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91786295129159506225593581 34419860673434814834597593)
            ·
              refine ⟨25814895505076111125948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34419860673434814834597593 25814895505076111125948195)
              ·
                refine ⟨38722343257614166688922293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25814895505076111125948195 38722343257614166688922293)
                ·
                  refine ⟨3630219680401328127086465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38722343257614166688922293 3630219680401328127086465)
                  ·
                    refine ⟨2722664760300996095314849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3630219680401328127086465 2722664760300996095314849)
                    ·
                      refine ⟨2041998570225747071486137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722664760300996095314849 2041998570225747071486137)
                      ·
                        rfl

theorem cell23_3976778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_3976778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976778 prefixEnd_3976778 := by exact prefixLift 3976778
  have htrace : WordTrace (prefixWord ++ tailWord_3976778) baseStart_3976778 baseEnd_3976778 := by
    simpa [prefixWord, tailWord_3976778, baseEnd_3976778] using wordTrace_append hprefix tailTrace_3976778
  have hstable : (prefixWord ++ tailWord_3976778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976778).length < 2 ^ (prefixWord ++ tailWord_3976778).sum := by decide
  have hdescent : baseEnd_3976778 < baseStart_3976778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976791 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3976791 : Nat := 118140960795 + 3976791 * 2 ^ 59
def prefixEnd_3976791 : Nat := 4983230072969 + 3 ^ 40 * 3976791 * 2
def baseEnd_3976791 : Nat := 2042005245474255520623577

theorem tailTrace_3976791 : CollatzResearch.WordTrace tailWord_3976791 prefixEnd_3976791 2042005245474255520623577 := by
  unfold tailWord_3976791
  simp only [CollatzResearch.WordTrace]
  refine ⟨145045483735772863675482227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96696989157181909116988151 145045483735772863675482227)
  ·
    refine ⟨217568225603659295513223341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145045483735772863675482227 217568225603659295513223341)
    ·
      refine ⟨81588084601372235817458753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217568225603659295513223341 81588084601372235817458753)
      ·
        refine ⟨61191063451029176863094065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81588084601372235817458753 61191063451029176863094065)
        ·
          refine ⟨45893297588271882647320549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61191063451029176863094065 45893297588271882647320549)
          ·
            refine ⟨8604993297800977996372603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45893297588271882647320549 8604993297800977996372603)
            ·
              refine ⟨12907489946701466994558905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604993297800977996372603 12907489946701466994558905)
              ·
                refine ⟨9680617460026100245919179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12907489946701466994558905 9680617460026100245919179)
                ·
                  refine ⟨14520926190039150368878769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9680617460026100245919179 14520926190039150368878769)
                  ·
                    refine ⟨10890694642529362776659077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14520926190039150368878769 10890694642529362776659077)
                    ·
                      refine ⟨2042005245474255520623577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10890694642529362776659077 2042005245474255520623577)
                      ·
                        rfl

theorem cell23_3976791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3976791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976791 prefixEnd_3976791 := by exact prefixLift 3976791
  have htrace : WordTrace (prefixWord ++ tailWord_3976791) baseStart_3976791 baseEnd_3976791 := by
    simpa [prefixWord, tailWord_3976791, baseEnd_3976791] using wordTrace_append hprefix tailTrace_3976791
  have hstable : (prefixWord ++ tailWord_3976791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976791).length < 2 ^ (prefixWord ++ tailWord_3976791).sum := by decide
  have hdescent : baseEnd_3976791 < baseStart_3976791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976811 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 3]
def baseStart_3976811 : Nat := 118140960795 + 3976811 * 2 ^ 59
def prefixEnd_3976811 : Nat := 4983230072969 + 3 ^ 40 * 3976811 * 2
def baseEnd_3976811 : Nat := 2042015515087345442373485

theorem tailTrace_3976811 : CollatzResearch.WordTrace tailWord_3976811 prefixEnd_3976811 2042015515087345442373485 := by
  unfold tailWord_3976811
  simp only [CollatzResearch.WordTrace]
  refine ⟨145046213195700407091210287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96697475463800271394140191 145046213195700407091210287)
  ·
    refine ⟨217569319793550610636815431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145046213195700407091210287 217569319793550610636815431)
    ·
      refine ⟨326353979690325915955223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217569319793550610636815431 326353979690325915955223147)
      ·
        refine ⟨489530969535488873932834721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326353979690325915955223147 489530969535488873932834721)
        ·
          refine ⟨367148227151616655449626041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489530969535488873932834721 367148227151616655449626041)
          ·
            refine ⟨275361170363712491587219531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367148227151616655449626041 275361170363712491587219531)
            ·
              refine ⟨413041755545568737380829297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275361170363712491587219531 413041755545568737380829297)
              ·
                refine ⟨309781316659176553035621973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413041755545568737380829297 309781316659176553035621973)
                ·
                  refine ⟨3630249804599725230886195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 309781316659176553035621973 3630249804599725230886195)
                  ·
                    refine ⟨5445374706899587846329293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630249804599725230886195 5445374706899587846329293)
                    ·
                      refine ⟨2042015515087345442373485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445374706899587846329293 2042015515087345442373485)
                      ·
                        rfl

theorem cell23_3976811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 3].length) (baseStart_3976811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976811 prefixEnd_3976811 := by exact prefixLift 3976811
  have htrace : WordTrace (prefixWord ++ tailWord_3976811) baseStart_3976811 baseEnd_3976811 := by
    simpa [prefixWord, tailWord_3976811, baseEnd_3976811] using wordTrace_append hprefix tailTrace_3976811
  have hstable : (prefixWord ++ tailWord_3976811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976811).length < 2 ^ (prefixWord ++ tailWord_3976811).sum := by decide
  have hdescent : baseEnd_3976811 < baseStart_3976811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976844 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_3976844 : Nat := 118140960795 + 3976844 * 2 ^ 59
def prefixEnd_3976844 : Nat := 4983230072969 + 3 ^ 40 * 3976844 * 2
def baseEnd_3976844 : Nat := 680677486649647937753611

theorem tailTrace_3976844 : CollatzResearch.WordTrace tailWord_3976844 prefixEnd_3976844 680677486649647937753611 := by
  unfold tailWord_3976844
  simp only [CollatzResearch.WordTrace]
  refine ⟨72523708402290426863580793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96698277869720569151441057 72523708402290426863580793)
  ·
    refine ⟨54392781301717820147685595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72523708402290426863580793 54392781301717820147685595)
    ·
      refine ⟨81589171952576730221528393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54392781301717820147685595 81589171952576730221528393)
      ·
        refine ⟨61191878964432547666146295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81589171952576730221528393 61191878964432547666146295)
        ·
          refine ⟨91787818446648821499219443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61191878964432547666146295 91787818446648821499219443)
          ·
            refine ⟨137681727669973232248829165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91787818446648821499219443 137681727669973232248829165)
            ·
              refine ⟨51630647876239962093310937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137681727669973232248829165 51630647876239962093310937)
              ·
                refine ⟨38722985907179971569983203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51630647876239962093310937 38722985907179971569983203)
                ·
                  refine ⟨58084478860769957354974805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38722985907179971569983203 58084478860769957354974805)
                  ·
                    refine ⟨680677486649647937753611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58084478860769957354974805 680677486649647937753611)
                    ·
                      rfl

theorem cell23_3976844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_3976844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976844 prefixEnd_3976844 := by exact prefixLift 3976844
  have htrace : WordTrace (prefixWord ++ tailWord_3976844) baseStart_3976844 baseEnd_3976844 := by
    simpa [prefixWord, tailWord_3976844, baseEnd_3976844] using wordTrace_append hprefix tailTrace_3976844
  have hstable : (prefixWord ++ tailWord_3976844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976844).length < 2 ^ (prefixWord ++ tailWord_3976844).sum := by decide
  have hdescent : baseEnd_3976844 < baseStart_3976844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976855 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3976855 : Nat := 118140960795 + 3976855 * 2 ^ 59
def prefixEnd_3976855 : Nat := 4983230072969 + 3 ^ 40 * 3976855 * 2
def baseEnd_3976855 : Nat := 2042038108236143270223283

theorem tailTrace_3976855 : CollatzResearch.WordTrace tailWord_3976855 prefixEnd_3976855 2042038108236143270223283 := by
  unfold tailWord_3976855
  simp only [CollatzResearch.WordTrace]
  refine ⟨145047818007541002605812019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96698545338360668403874679 145047818007541002605812019)
  ·
    refine ⟨217571727011311503908718029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145047818007541002605812019 217571727011311503908718029)
    ·
      refine ⟨81589397629241813965769261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217571727011311503908718029 81589397629241813965769261)
      ·
        refine ⟨30596024110965680237163473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81589397629241813965769261 30596024110965680237163473)
        ·
          refine ⟨22947018083224260177872605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30596024110965680237163473 22947018083224260177872605)
          ·
            refine ⟨8605131781209097566702227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22947018083224260177872605 8605131781209097566702227)
            ·
              refine ⟨12907697671813646350053341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8605131781209097566702227 12907697671813646350053341)
              ·
                refine ⟨4840386626930117381270003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12907697671813646350053341 4840386626930117381270003)
                ·
                  refine ⟨7260579940395176071905005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840386626930117381270003 7260579940395176071905005)
                  ·
                    refine ⟨2722717477648191026964377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7260579940395176071905005 2722717477648191026964377)
                    ·
                      refine ⟨2042038108236143270223283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722717477648191026964377 2042038108236143270223283)
                      ·
                        rfl

theorem cell23_3976855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3976855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976855 prefixEnd_3976855 := by exact prefixLift 3976855
  have htrace : WordTrace (prefixWord ++ tailWord_3976855) baseStart_3976855 baseEnd_3976855 := by
    simpa [prefixWord, tailWord_3976855, baseEnd_3976855] using wordTrace_append hprefix tailTrace_3976855
  have hstable : (prefixWord ++ tailWord_3976855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976855).length < 2 ^ (prefixWord ++ tailWord_3976855).sum := by decide
  have hdescent : baseEnd_3976855 < baseStart_3976855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976862 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3976862 : Nat := 118140960795 + 3976862 * 2 ^ 59
def prefixEnd_3976862 : Nat := 4983230072969 + 3 ^ 40 * 3976862 * 2
def baseEnd_3976862 : Nat := 2042041702600724742835751

theorem tailTrace_3976862 : CollatzResearch.WordTrace tailWord_3976862 prefixEnd_3976862 2042041702600724742835751 := by
  unfold tailWord_3976862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131009164814455350164605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96698715545677095200877893 18131009164814455350164605)
  ·
    refine ⟨6799128436805420756311727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18131009164814455350164605 6799128436805420756311727)
    ·
      refine ⟨10198692655208131134467591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799128436805420756311727 10198692655208131134467591)
      ·
        refine ⟨15298038982812196701701387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198692655208131134467591 15298038982812196701701387)
        ·
          refine ⟨22947058474218295052552081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15298038982812196701701387 22947058474218295052552081)
          ·
            refine ⟨17210293855663721289414061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22947058474218295052552081 17210293855663721289414061)
            ·
              refine ⟨6453860195873895483530273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17210293855663721289414061 6453860195873895483530273)
              ·
                refine ⟨4840395146905421612647705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453860195873895483530273 4840395146905421612647705)
                ·
                  refine ⟨3630296360179066209485779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840395146905421612647705 3630296360179066209485779)
                  ·
                    refine ⟨5445444540268599314228669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630296360179066209485779 5445444540268599314228669)
                    ·
                      refine ⟨2042041702600724742835751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445444540268599314228669 2042041702600724742835751)
                      ·
                        rfl

theorem cell23_3976862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3976862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976862 prefixEnd_3976862 := by exact prefixLift 3976862
  have htrace : WordTrace (prefixWord ++ tailWord_3976862) baseStart_3976862 baseEnd_3976862 := by
    simpa [prefixWord, tailWord_3976862, baseEnd_3976862] using wordTrace_append hprefix tailTrace_3976862
  have hstable : (prefixWord ++ tailWord_3976862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976862).length < 2 ^ (prefixWord ++ tailWord_3976862).sum := by decide
  have hdescent : baseEnd_3976862 < baseStart_3976862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976921 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_3976921 : Nat := 118140960795 + 3976921 * 2 ^ 59
def prefixEnd_3976921 : Nat := 4983230072969 + 3 ^ 40 * 3976921 * 2
def baseEnd_3976921 : Nat := 680690665986446670665993

theorem tailTrace_3976921 : CollatzResearch.WordTrace tailWord_3976921 prefixEnd_3976921 680690665986446670665993 := by
  unfold tailWord_3976921
  simp only [CollatzResearch.WordTrace]
  refine ⟨145050225225301895877714617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96700150150201263918476411 145050225225301895877714617)
  ·
    refine ⟨108787668918976421908285963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145050225225301895877714617 108787668918976421908285963)
    ·
      refine ⟨163181503378464632862428945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108787668918976421908285963 163181503378464632862428945)
      ·
        refine ⟨122386127533848474646821709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163181503378464632862428945 122386127533848474646821709)
        ·
          refine ⟨45894797825193177992558141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122386127533848474646821709 45894797825193177992558141)
          ·
            refine ⟨17210549184447441747209303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45894797825193177992558141 17210549184447441747209303)
            ·
              refine ⟨25815823776671162620813955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17210549184447441747209303 25815823776671162620813955)
              ·
                refine ⟨38723735665006743931220933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25815823776671162620813955 38723735665006743931220933)
                ·
                  refine ⟨7260700437188764487103925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38723735665006743931220933 7260700437188764487103925)
                  ·
                    refine ⟨680690665986446670665993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7260700437188764487103925 680690665986446670665993)
                    ·
                      rfl

theorem cell23_3976921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_3976921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3976921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3976921 prefixEnd_3976921 := by exact prefixLift 3976921
  have htrace : WordTrace (prefixWord ++ tailWord_3976921) baseStart_3976921 baseEnd_3976921 := by
    simpa [prefixWord, tailWord_3976921, baseEnd_3976921] using wordTrace_append hprefix tailTrace_3976921
  have hstable : (prefixWord ++ tailWord_3976921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976921).length < 2 ^ (prefixWord ++ tailWord_3976921).sum := by decide
  have hdescent : baseEnd_3976921 < baseStart_3976921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977012 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3977012 : Nat := 118140960795 + 3977012 * 2 ^ 59
def prefixEnd_3977012 : Nat := 4983230072969 + 3 ^ 40 * 3977012 * 2
def baseEnd_3977012 : Nat := 2042118724698899155960061

theorem tailTrace_3977012 : CollatzResearch.WordTrace tailWord_3977012 prefixEnd_3977012 2042118724698899155960061 := by
  unfold tailWord_3977012
  simp only [CollatzResearch.WordTrace]
  refine ⟨72526772133986109209638645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96702362845314812279518193 72526772133986109209638645)
  ·
    refine ⟨6799384887561197738403623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72526772133986109209638645 6799384887561197738403623)
    ·
      refine ⟨10199077331341796607605435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799384887561197738403623 10199077331341796607605435)
      ·
        refine ⟨15298615997012694911408153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199077331341796607605435 15298615997012694911408153)
        ·
          refine ⟨11473961997759521183556115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15298615997012694911408153 11473961997759521183556115)
          ·
            refine ⟨17210942996639281775334173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473961997759521183556115 17210942996639281775334173)
            ·
              refine ⟨6454103623739730665750315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17210942996639281775334173 6454103623739730665750315)
              ·
                refine ⟨9681155435609595998625473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454103623739730665750315 9681155435609595998625473)
                ·
                  refine ⟨7260866576707196998969105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9681155435609595998625473 7260866576707196998969105)
                  ·
                    refine ⟨5445649932530397749226829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260866576707196998969105 5445649932530397749226829)
                    ·
                      refine ⟨2042118724698899155960061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445649932530397749226829 2042118724698899155960061)
                      ·
                        rfl

theorem cell23_3977012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3977012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977012 prefixEnd_3977012 := by exact prefixLift 3977012
  have htrace : WordTrace (prefixWord ++ tailWord_3977012) baseStart_3977012 baseEnd_3977012 := by
    simpa [prefixWord, tailWord_3977012, baseEnd_3977012] using wordTrace_append hprefix tailTrace_3977012
  have hstable : (prefixWord ++ tailWord_3977012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977012).length < 2 ^ (prefixWord ++ tailWord_3977012).sum := by decide
  have hdescent : baseEnd_3977012 < baseStart_3977012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977042 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_3977042 : Nat := 118140960795 + 3977042 * 2 ^ 59
def prefixEnd_3977042 : Nat := 4983230072969 + 3 ^ 40 * 3977042 * 2
def baseEnd_3977042 : Nat := 2042134129118534038584923

theorem tailTrace_3977042 : CollatzResearch.WordTrace tailWord_3977042 prefixEnd_3977042 2042134129118534038584923 := by
  unfold tailWord_3977042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36263659614465883385717345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96703092305242355695246253 36263659614465883385717345)
  ·
    refine ⟨27197744710849412539288009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36263659614465883385717345 27197744710849412539288009)
    ·
      refine ⟨20398308533137059404466007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27197744710849412539288009 20398308533137059404466007)
      ·
        refine ⟨30597462799705589106699011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20398308533137059404466007 30597462799705589106699011)
        ·
          refine ⟨45896194199558383660048517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30597462799705589106699011 45896194199558383660048517)
          ·
            refine ⟨8605536412417196936259097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45896194199558383660048517 8605536412417196936259097)
            ·
              refine ⟨6454152309312897702194323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605536412417196936259097 6454152309312897702194323)
              ·
                refine ⟨9681228463969346553291485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454152309312897702194323 9681228463969346553291485)
                ·
                  refine ⟨3630460673988504957484307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9681228463969346553291485 3630460673988504957484307)
                  ·
                    refine ⟨5445691010982757436226461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630460673988504957484307 5445691010982757436226461)
                    ·
                      refine ⟨2042134129118534038584923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445691010982757436226461 2042134129118534038584923)
                      ·
                        rfl

theorem cell23_3977042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_3977042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977042 prefixEnd_3977042 := by exact prefixLift 3977042
  have htrace : WordTrace (prefixWord ++ tailWord_3977042) baseStart_3977042 baseEnd_3977042 := by
    simpa [prefixWord, tailWord_3977042, baseEnd_3977042] using wordTrace_append hprefix tailTrace_3977042
  have hstable : (prefixWord ++ tailWord_3977042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977042).length < 2 ^ (prefixWord ++ tailWord_3977042).sum := by decide
  have hdescent : baseEnd_3977042 < baseStart_3977042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977119 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3977119 : Nat := 118140960795 + 3977119 * 2 ^ 59
def prefixEnd_3977119 : Nat := 4983230072969 + 3 ^ 40 * 3977119 * 2
def baseEnd_3977119 : Nat := 2042173667128930237322069

theorem tailTrace_3977119 : CollatzResearch.WordTrace tailWord_3977119 prefixEnd_3977119 2042173667128930237322069 := by
  unfold tailWord_3977119
  simp only [CollatzResearch.WordTrace]
  refine ⟨145057446878584575693422411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96704964585723050462281607 145057446878584575693422411)
  ·
    refine ⟨217586170317876863540133617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145057446878584575693422411 217586170317876863540133617)
    ·
      refine ⟨163189627738407647655100213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217586170317876863540133617 163189627738407647655100213)
      ·
        refine ⟨15299027600475716967665645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163189627738407647655100213 15299027600475716967665645)
        ·
          refine ⟨5737135350178393862874617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15299027600475716967665645 5737135350178393862874617)
          ·
            refine ⟨4302851512633795397155963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737135350178393862874617 4302851512633795397155963)
            ·
              refine ⟨6454277268950693095733945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302851512633795397155963 6454277268950693095733945)
              ·
                refine ⟨4840707951713019821800459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454277268950693095733945 4840707951713019821800459)
                ·
                  refine ⟨7261061927569529732700689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840707951713019821800459 7261061927569529732700689)
                  ·
                    refine ⟨5445796445677147299525517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7261061927569529732700689 5445796445677147299525517)
                    ·
                      refine ⟨2042173667128930237322069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445796445677147299525517 2042173667128930237322069)
                      ·
                        rfl

theorem cell23_3977119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3977119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977119 prefixEnd_3977119 := by exact prefixLift 3977119
  have htrace : WordTrace (prefixWord ++ tailWord_3977119) baseStart_3977119 baseEnd_3977119 := by
    simpa [prefixWord, tailWord_3977119, baseEnd_3977119] using wordTrace_append hprefix tailTrace_3977119
  have hstable : (prefixWord ++ tailWord_3977119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977119).length < 2 ^ (prefixWord ++ tailWord_3977119).sum := by decide
  have hdescent : baseEnd_3977119 < baseStart_3977119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977138 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3977138 : Nat := 118140960795 + 3977138 * 2 ^ 59
def prefixEnd_3977138 : Nat := 4983230072969 + 3 ^ 40 * 3977138 * 2
def baseEnd_3977138 : Nat := 2042183423261365662984481

theorem tailTrace_3977138 : CollatzResearch.WordTrace tailWord_3977138 prefixEnd_3977138 2042183423261365662984481 := by
  unfold tailWord_3977138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36264534966378935484591017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96705426577010494625576045 36264534966378935484591017)
  ·
    refine ⟨27198401224784201613443263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36264534966378935484591017 27198401224784201613443263)
    ·
      refine ⟨40797601837176302420164895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27198401224784201613443263 40797601837176302420164895)
      ·
        refine ⟨61196402755764453630247343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40797601837176302420164895 61196402755764453630247343)
        ·
          refine ⟨91794604133646680445371015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61196402755764453630247343 91794604133646680445371015)
          ·
            refine ⟨137691906200470020668056523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91794604133646680445371015 137691906200470020668056523)
            ·
              refine ⟨206537859300705031002084785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137691906200470020668056523 206537859300705031002084785)
              ·
                refine ⟨154903394475528773251563589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206537859300705031002084785 154903394475528773251563589)
                ·
                  refine ⟨29044386464161644984668173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154903394475528773251563589 29044386464161644984668173)
                  ·
                    refine ⟨10891644924060616869250565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29044386464161644984668173 10891644924060616869250565)
                    ·
                      refine ⟨2042183423261365662984481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10891644924060616869250565 2042183423261365662984481)
                      ·
                        rfl

theorem cell23_3977138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3977138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977138 prefixEnd_3977138 := by exact prefixLift 3977138
  have htrace : WordTrace (prefixWord ++ tailWord_3977138) baseStart_3977138 baseEnd_3977138 := by
    simpa [prefixWord, tailWord_3977138, baseEnd_3977138] using wordTrace_append hprefix tailTrace_3977138
  have hstable : (prefixWord ++ tailWord_3977138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977138).length < 2 ^ (prefixWord ++ tailWord_3977138).sum := by decide
  have hdescent : baseEnd_3977138 < baseStart_3977138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977149 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3977149 : Nat := 118140960795 + 3977149 * 2 ^ 59
def prefixEnd_3977149 : Nat := 4983230072969 + 3 ^ 40 * 3977149 * 2
def baseEnd_3977149 : Nat := 2042189071548565119946931

theorem tailTrace_3977149 : CollatzResearch.WordTrace tailWord_3977149 prefixEnd_3977149 2042189071548565119946931 := by
  unfold tailWord_3977149
  simp only [CollatzResearch.WordTrace]
  refine ⟨145058541068475890817014501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96705694045650593878009667 145058541068475890817014501)
  ·
    refine ⟨27198476450339229528190219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145058541068475890817014501 27198476450339229528190219)
    ·
      refine ⟨40797714675508844292285329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27198476450339229528190219 40797714675508844292285329)
      ·
        refine ⟨30598286006631633219213997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40797714675508844292285329 30598286006631633219213997)
        ·
          refine ⟨11474357252486862457205249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30598286006631633219213997 11474357252486862457205249)
          ·
            refine ⟨8605767939365146842903937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11474357252486862457205249 8605767939365146842903937)
            ·
              refine ⟨6454325954523860132177953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605767939365146842903937 6454325954523860132177953)
              ·
                refine ⟨4840744465892895099133465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454325954523860132177953 4840744465892895099133465)
                ·
                  refine ⟨3630558349419671324350099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840744465892895099133465 3630558349419671324350099)
                  ·
                    refine ⟨5445837524129506986525149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630558349419671324350099 5445837524129506986525149)
                    ·
                      refine ⟨2042189071548565119946931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5445837524129506986525149 2042189071548565119946931)
                      ·
                        rfl

theorem cell23_3977149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3977149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977149 prefixEnd_3977149 := by exact prefixLift 3977149
  have htrace : WordTrace (prefixWord ++ tailWord_3977149) baseStart_3977149 baseEnd_3977149 := by
    simpa [prefixWord, tailWord_3977149, baseEnd_3977149] using wordTrace_append hprefix tailTrace_3977149
  have hstable : (prefixWord ++ tailWord_3977149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977149).length < 2 ^ (prefixWord ++ tailWord_3977149).sum := by decide
  have hdescent : baseEnd_3977149 < baseStart_3977149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977168 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_3977168 : Nat := 118140960795 + 3977168 * 2 ^ 59
def prefixEnd_3977168 : Nat := 4983230072969 + 3 ^ 40 * 3977168 * 2
def baseEnd_3977168 : Nat := 2042198827681000545609343

theorem tailTrace_3977168 : CollatzResearch.WordTrace tailWord_3977168 prefixEnd_3977168 2042198827681000545609343 := by
  unfold tailWord_3977168
  simp only [CollatzResearch.WordTrace]
  refine ⟨72529617027703528530978079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96706156036938038041304105 72529617027703528530978079)
  ·
    refine ⟨108794425541555292796467119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72529617027703528530978079 108794425541555292796467119)
    ·
      refine ⟨163191638312332939194700679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108794425541555292796467119 163191638312332939194700679)
      ·
        refine ⟨244787457468499408792051019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163191638312332939194700679 244787457468499408792051019)
        ·
          refine ⟨367181186202749113188076529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244787457468499408792051019 367181186202749113188076529)
          ·
            refine ⟨275385889652061834891057397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367181186202749113188076529 275385889652061834891057397)
            ·
              refine ⟨25817427154880797021036631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275385889652061834891057397 25817427154880797021036631)
              ·
                refine ⟨38726140732321195531554947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25817427154880797021036631 38726140732321195531554947)
                ·
                  refine ⟨58089211098481793297332421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38726140732321195531554947 58089211098481793297332421)
                  ·
                    refine ⟨10891727080965336243249829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58089211098481793297332421 10891727080965336243249829)
                    ·
                      refine ⟨2042198827681000545609343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10891727080965336243249829 2042198827681000545609343)
                      ·
                        rfl

theorem cell23_3977168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_3977168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977168 prefixEnd_3977168 := by exact prefixLift 3977168
  have htrace : WordTrace (prefixWord ++ tailWord_3977168) baseStart_3977168 baseEnd_3977168 := by
    simpa [prefixWord, tailWord_3977168, baseEnd_3977168] using wordTrace_append hprefix tailTrace_3977168
  have hstable : (prefixWord ++ tailWord_3977168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977168).length < 2 ^ (prefixWord ++ tailWord_3977168).sum := by decide
  have hdescent : baseEnd_3977168 < baseStart_3977168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977206 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3977206 : Nat := 118140960795 + 3977206 * 2 ^ 59
def prefixEnd_3977206 : Nat := 4983230072969 + 3 ^ 40 * 3977206 * 2
def baseEnd_3977206 : Nat := 2042218339945871396934169

theorem tailTrace_3977206 : CollatzResearch.WordTrace tailWord_3977206 prefixEnd_3977206 2042218339945871396934169 := by
  unfold tailWord_3977206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066288751829336846989967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96707080019512926367892981 9066288751829336846989967)
  ·
    refine ⟨13599433127744005270484951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066288751829336846989967 13599433127744005270484951)
    ·
      refine ⟨20399149691616007905727427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13599433127744005270484951 20399149691616007905727427)
      ·
        refine ⟨30598724537424011858591141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20399149691616007905727427 30598724537424011858591141)
        ·
          refine ⟨5737260850767002223485839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30598724537424011858591141 5737260850767002223485839)
          ·
            refine ⟨8605891276150503335228759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737260850767002223485839 8605891276150503335228759)
            ·
              refine ⟨12908836914225755002843139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8605891276150503335228759 12908836914225755002843139)
              ·
                refine ⟨19363255371338632504264709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12908836914225755002843139 19363255371338632504264709)
                ·
                  refine ⟨3630610382125993594549633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19363255371338632504264709 3630610382125993594549633)
                  ·
                    refine ⟨2722957786594495195912225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3630610382125993594549633 2722957786594495195912225)
                    ·
                      refine ⟨2042218339945871396934169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722957786594495195912225 2042218339945871396934169)
                      ·
                        rfl

theorem cell23_3977206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3977206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977206 prefixEnd_3977206 := by exact prefixLift 3977206
  have htrace : WordTrace (prefixWord ++ tailWord_3977206) baseStart_3977206 baseEnd_3977206 := by
    simpa [prefixWord, tailWord_3977206, baseEnd_3977206] using wordTrace_append hprefix tailTrace_3977206
  have hstable : (prefixWord ++ tailWord_3977206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977206).length < 2 ^ (prefixWord ++ tailWord_3977206).sum := by decide
  have hdescent : baseEnd_3977206 < baseStart_3977206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977215 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 7, 2]
def baseStart_3977215 : Nat := 118140960795 + 3977215 * 2 ^ 59
def prefixEnd_3977215 : Nat := 4983230072969 + 3 ^ 40 * 3977215 * 2
def baseEnd_3977215 : Nat := 2042222961271761861721627

theorem tailTrace_3977215 : CollatzResearch.WordTrace tailWord_3977215 prefixEnd_3977215 2042222961271761861721627 := by
  unfold tailWord_3977215
  simp only [CollatzResearch.WordTrace]
  refine ⟨145060948286236784088917099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96707298857491189392611399 145060948286236784088917099)
  ·
    refine ⟨217591422429355176133375649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145060948286236784088917099 217591422429355176133375649)
    ·
      refine ⟨163193566822016382100031737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217591422429355176133375649 163193566822016382100031737)
      ·
        refine ⟨122395175116512286575023803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163193566822016382100031737 122395175116512286575023803)
        ·
          refine ⟨183592762674768429862535705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122395175116512286575023803 183592762674768429862535705)
          ·
            refine ⟨137694572006076322396901779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183592762674768429862535705 137694572006076322396901779)
            ·
              refine ⟨206541858009114483595352669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137694572006076322396901779 206541858009114483595352669)
              ·
                refine ⟨77453196753417931348257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206541858009114483595352669 77453196753417931348257251)
                ·
                  refine ⟨116179795130126897022385877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77453196753417931348257251 116179795130126897022385877)
                  ·
                    refine ⟨2722963948362349148962169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116179795130126897022385877 2722963948362349148962169)
                    ·
                      refine ⟨2042222961271761861721627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2722963948362349148962169 2042222961271761861721627)
                      ·
                        rfl

theorem cell23_3977215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_3977215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977215 prefixEnd_3977215 := by exact prefixLift 3977215
  have htrace : WordTrace (prefixWord ++ tailWord_3977215) baseStart_3977215 baseEnd_3977215 := by
    simpa [prefixWord, tailWord_3977215, baseEnd_3977215] using wordTrace_append hprefix tailTrace_3977215
  have hstable : (prefixWord ++ tailWord_3977215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977215).length < 2 ^ (prefixWord ++ tailWord_3977215).sum := by decide
  have hdescent : baseEnd_3977215 < baseStart_3977215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977262 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3977262 : Nat := 118140960795 + 3977262 * 2 ^ 59
def prefixEnd_3977262 : Nat := 4983230072969 + 3 ^ 40 * 3977262 * 2
def baseEnd_3977262 : Nat := 2042247094862523177833911

theorem tailTrace_3977262 : CollatzResearch.WordTrace tailWord_3977262 prefixEnd_3977262 2042247094862523177833911 := by
  unfold tailWord_3977262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132832814633313889484755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96708441678044340743918693 18132832814633313889484755)
  ·
    refine ⟨27199249221949970834227133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18132832814633313889484755 27199249221949970834227133)
    ·
      refine ⟨10199718458231239062835175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27199249221949970834227133 10199718458231239062835175)
      ·
        refine ⟨15299577687346858594252763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199718458231239062835175 15299577687346858594252763)
        ·
          refine ⟨22949366531020287891379145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299577687346858594252763 22949366531020287891379145)
          ·
            refine ⟨17212024898265215918534359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22949366531020287891379145 17212024898265215918534359)
            ·
              refine ⟨25818037347397823877801539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17212024898265215918534359 25818037347397823877801539)
              ·
                refine ⟨38727056021096735816702309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25818037347397823877801539 38727056021096735816702309)
                ·
                  refine ⟨7261323003955637965631683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38727056021096735816702309 7261323003955637965631683)
                  ·
                    refine ⟨10891984505933456948447525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261323003955637965631683 10891984505933456948447525)
                    ·
                      refine ⟨2042247094862523177833911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10891984505933456948447525 2042247094862523177833911)
                      ·
                        rfl

theorem cell23_3977262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3977262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977262 prefixEnd_3977262 := by exact prefixLift 3977262
  have htrace : WordTrace (prefixWord ++ tailWord_3977262) baseStart_3977262 baseEnd_3977262 := by
    simpa [prefixWord, tailWord_3977262, baseEnd_3977262] using wordTrace_append hprefix tailTrace_3977262
  have hstable : (prefixWord ++ tailWord_3977262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977262).length < 2 ^ (prefixWord ++ tailWord_3977262).sum := by decide
  have hdescent : baseEnd_3977262 < baseStart_3977262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977362 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3977362 : Nat := 118140960795 + 3977362 * 2 ^ 59
def prefixEnd_3977362 : Nat := 4983230072969 + 3 ^ 40 * 3977362 * 2
def baseEnd_3977362 : Nat := 680766147642657595527817

theorem tailTrace_3977362 : CollatzResearch.WordTrace tailWord_3977362 prefixEnd_3977362 680766147642657595527817 := by
  unfold tailWord_3977362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266577454176057048629585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96710873211136152129678893 36266577454176057048629585)
  ·
    refine ⟨27199933090632042786472189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36266577454176057048629585 27199933090632042786472189)
    ·
      refine ⟨10199974908987016044927071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27199933090632042786472189 10199974908987016044927071)
      ·
        refine ⟨15299962363480524067390607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199974908987016044927071 15299962363480524067390607)
        ·
          refine ⟨22949943545220786101085911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299962363480524067390607 22949943545220786101085911)
          ·
            refine ⟨34424915317831179151628867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22949943545220786101085911 34424915317831179151628867)
            ·
              refine ⟨51637372976746768727443301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34424915317831179151628867 51637372976746768727443301)
              ·
                refine ⟨9682007433140019136395619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51637372976746768727443301 9682007433140019136395619)
                ·
                  refine ⟨14523011149710028704593429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682007433140019136395619 14523011149710028704593429)
                  ·
                    refine ⟨680766147642657595527817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14523011149710028704593429 680766147642657595527817)
                    ·
                      rfl

theorem cell23_3977362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3977362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977362 prefixEnd_3977362 := by exact prefixLift 3977362
  have htrace : WordTrace (prefixWord ++ tailWord_3977362) baseStart_3977362 baseEnd_3977362 := by
    simpa [prefixWord, tailWord_3977362, baseEnd_3977362] using wordTrace_append hprefix tailTrace_3977362
  have hstable : (prefixWord ++ tailWord_3977362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977362).length < 2 ^ (prefixWord ++ tailWord_3977362).sum := by decide
  have hdescent : baseEnd_3977362 < baseStart_3977362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977372 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3977372 : Nat := 118140960795 + 3977372 * 2 ^ 59
def prefixEnd_3977372 : Nat := 4983230072969 + 3 ^ 40 * 3977372 * 2
def baseEnd_3977372 : Nat := 2042303577734517747458405

theorem tailTrace_3977372 : CollatzResearch.WordTrace tailWord_3977372 prefixEnd_3977372 2042303577734517747458405 := by
  unfold tailWord_3977372
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533337273333999951191185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96711116364445333268254913 72533337273333999951191185)
  ·
    refine ⟨54400002955000499963393389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72533337273333999951191185 54400002955000499963393389)
    ·
      refine ⟨20400001108125187486272521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54400002955000499963393389 20400001108125187486272521)
      ·
        refine ⟨15300000831093890614704391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20400001108125187486272521 15300000831093890614704391)
        ·
          refine ⟨22950001246640835922056587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300000831093890614704391 22950001246640835922056587)
          ·
            refine ⟨34425001869961253883084881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22950001246640835922056587 34425001869961253883084881)
            ·
              refine ⟨25818751402470940412313661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34425001869961253883084881 25818751402470940412313661)
              ·
                refine ⟨9682031775926602654617623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25818751402470940412313661 9682031775926602654617623)
                ·
                  refine ⟨14523047663889903981926435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682031775926602654617623 14523047663889903981926435)
                  ·
                    refine ⟨21784571495834855972889653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14523047663889903981926435 21784571495834855972889653)
                    ·
                      refine ⟨2042303577734517747458405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21784571495834855972889653 2042303577734517747458405)
                      ·
                        rfl

theorem cell23_3977372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3977372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977372 prefixEnd_3977372 := by exact prefixLift 3977372
  have htrace : WordTrace (prefixWord ++ tailWord_3977372) baseStart_3977372 baseEnd_3977372 := by
    simpa [prefixWord, tailWord_3977372, baseEnd_3977372] using wordTrace_append hprefix tailTrace_3977372
  have hstable : (prefixWord ++ tailWord_3977372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977372).length < 2 ^ (prefixWord ++ tailWord_3977372).sum := by decide
  have hdescent : baseEnd_3977372 < baseStart_3977372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977389 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3977389 : Nat := 118140960795 + 3977389 * 2 ^ 59
def prefixEnd_3977389 : Nat := 4983230072969 + 3 ^ 40 * 3977389 * 2
def baseEnd_3977389 : Nat := 2042312306905644180945827

theorem tailTrace_3977389 : CollatzResearch.WordTrace tailWord_3977389 prefixEnd_3977389 2042312306905644180945827 := by
  unfold tailWord_3977389
  simp only [CollatzResearch.WordTrace]
  refine ⟨145067294587606411805751221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96711529725070941203834147 145067294587606411805751221)
  ·
    refine ⟨13600058867588101106789177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145067294587606411805751221 13600058867588101106789177)
    ·
      refine ⟨10200044150691075830091883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13600058867588101106789177 10200044150691075830091883)
      ·
        refine ⟨15300066226036613745137825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200044150691075830091883 15300066226036613745137825)
        ·
          refine ⟨11475049669527460308853369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300066226036613745137825 11475049669527460308853369)
          ·
            refine ⟨8606287252145595231640027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475049669527460308853369 8606287252145595231640027)
            ·
              refine ⟨12909430878218392847460041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606287252145595231640027 12909430878218392847460041)
              ·
                refine ⟨9682073158663794635595031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12909430878218392847460041 9682073158663794635595031)
                ·
                  refine ⟨14523109737995691953392547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682073158663794635595031 14523109737995691953392547)
                  ·
                    refine ⟨21784664606993537930088821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14523109737995691953392547 21784664606993537930088821)
                    ·
                      refine ⟨2042312306905644180945827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21784664606993537930088821 2042312306905644180945827)
                      ·
                        rfl

theorem cell23_3977389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3977389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977389 prefixEnd_3977389 := by exact prefixLift 3977389
  have htrace : WordTrace (prefixWord ++ tailWord_3977389) baseStart_3977389 baseEnd_3977389 := by
    simpa [prefixWord, tailWord_3977389, baseEnd_3977389] using wordTrace_append hprefix tailTrace_3977389
  have hstable : (prefixWord ++ tailWord_3977389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977389).length < 2 ^ (prefixWord ++ tailWord_3977389).sum := by decide
  have hdescent : baseEnd_3977389 < baseStart_3977389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977399 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_3977399 : Nat := 118140960795 + 3977399 * 2 ^ 59
def prefixEnd_3977399 : Nat := 4983230072969 + 3 ^ 40 * 3977399 * 2
def baseEnd_3977399 : Nat := 2042317441712189141820781

theorem tailTrace_3977399 : CollatzResearch.WordTrace tailWord_3977399 prefixEnd_3977399 2042317441712189141820781 := by
  unfold tailWord_3977399
  simp only [CollatzResearch.WordTrace]
  refine ⟨145067659317570183513615251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96711772878380122342410167 145067659317570183513615251)
  ·
    refine ⟨217601488976355275270422877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145067659317570183513615251 217601488976355275270422877)
    ·
      refine ⟨81600558366133228226408579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217601488976355275270422877 81600558366133228226408579)
      ·
        refine ⟨122400837549199842339612869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81600558366133228226408579 122400837549199842339612869)
        ·
          refine ⟨22950157040474970438677413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122400837549199842339612869 22950157040474970438677413)
          ·
            refine ⟨4303154445089056957252015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22950157040474970438677413 4303154445089056957252015)
            ·
              refine ⟨6454731667633585435878023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303154445089056957252015 6454731667633585435878023)
              ·
                refine ⟨9682097501450378153817035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454731667633585435878023 9682097501450378153817035)
                ·
                  refine ⟨14523146252175567230725553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682097501450378153817035 14523146252175567230725553)
                  ·
                    refine ⟨10892359689131675423044165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14523146252175567230725553 10892359689131675423044165)
                    ·
                      refine ⟨2042317441712189141820781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10892359689131675423044165 2042317441712189141820781)
                      ·
                        rfl

theorem cell23_3977399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_3977399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977399 prefixEnd_3977399 := by exact prefixLift 3977399
  have htrace : WordTrace (prefixWord ++ tailWord_3977399) baseStart_3977399 baseEnd_3977399 := by
    simpa [prefixWord, tailWord_3977399, baseEnd_3977399] using wordTrace_append hprefix tailTrace_3977399
  have hstable : (prefixWord ++ tailWord_3977399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977399).length < 2 ^ (prefixWord ++ tailWord_3977399).sum := by decide
  have hdescent : baseEnd_3977399 < baseStart_3977399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977409 : List Nat := [1, 2, 6, 1, 2, 1, 1, 9]
def baseStart_3977409 : Nat := 118140960795 + 3977409 * 2 ^ 59
def prefixEnd_3977409 : Nat := 4983230072969 + 3 ^ 40 * 3977409 * 2
def baseEnd_3977409 : Nat := 75641576908101263062805

theorem tailTrace_3977409 : CollatzResearch.WordTrace tailWord_3977409 prefixEnd_3977409 75641576908101263062805 := by
  unfold tailWord_3977409
  simp only [CollatzResearch.WordTrace]
  refine ⟨145068024047533955221479281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96712016031689303480986187 145068024047533955221479281)
  ·
    refine ⟨108801018035650466416109461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145068024047533955221479281 108801018035650466416109461)
    ·
      refine ⟨5100047720421115613255131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108801018035650466416109461 5100047720421115613255131)
      ·
        refine ⟨7650071580631673419882697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100047720421115613255131 7650071580631673419882697)
        ·
          refine ⟨5737553685473755064912023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7650071580631673419882697 5737553685473755064912023)
          ·
            refine ⟨8606330528210632597368035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737553685473755064912023 8606330528210632597368035)
            ·
              refine ⟨12909495792315948896052053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606330528210632597368035 12909495792315948896052053)
              ·
                refine ⟨75641576908101263062805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12909495792315948896052053 75641576908101263062805)
                ·
                  rfl

theorem cell23_3977409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 9].length) (baseStart_3977409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977409 prefixEnd_3977409 := by exact prefixLift 3977409
  have htrace : WordTrace (prefixWord ++ tailWord_3977409) baseStart_3977409 baseEnd_3977409 := by
    simpa [prefixWord, tailWord_3977409, baseEnd_3977409] using wordTrace_append hprefix tailTrace_3977409
  have hstable : (prefixWord ++ tailWord_3977409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977409).length < 2 ^ (prefixWord ++ tailWord_3977409).sum := by decide
  have hdescent : baseEnd_3977409 < baseStart_3977409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977437 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3977437 : Nat := 118140960795 + 3977437 * 2 ^ 59
def prefixEnd_3977437 : Nat := 4983230072969 + 3 ^ 40 * 3977437 * 2
def baseEnd_3977437 : Nat := 2042336953977059993145607

theorem tailTrace_3977437 : CollatzResearch.WordTrace tailWord_3977437 prefixEnd_3977437 2042336953977059993145607 := by
  unfold tailWord_3977437
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069045291432516003498565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96712696860955010668999043 145069045291432516003498565)
  ·
    refine ⟨27200445992143596750655981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145069045291432516003498565 27200445992143596750655981)
    ·
      refine ⟨10200167247053848781495993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27200445992143596750655981 10200167247053848781495993)
      ·
        refine ⟨7650125435290386586121995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200167247053848781495993 7650125435290386586121995)
        ·
          refine ⟨11475188152935579879182993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650125435290386586121995 11475188152935579879182993)
          ·
            refine ⟨8606391114701684909387245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475188152935579879182993 8606391114701684909387245)
            ·
              refine ⟨3227396668013131841020217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8606391114701684909387245 3227396668013131841020217)
              ·
                refine ⟨2420547501009848880765163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227396668013131841020217 2420547501009848880765163)
                ·
                  refine ⟨3630821251514773321147745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420547501009848880765163 3630821251514773321147745)
                  ·
                    refine ⟨2723115938636079990860809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3630821251514773321147745 2723115938636079990860809)
                    ·
                      refine ⟨2042336953977059993145607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723115938636079990860809 2042336953977059993145607)
                      ·
                        rfl

theorem cell23_3977437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3977437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977437 prefixEnd_3977437 := by exact prefixLift 3977437
  have htrace : WordTrace (prefixWord ++ tailWord_3977437) baseStart_3977437 baseEnd_3977437 := by
    simpa [prefixWord, tailWord_3977437, baseEnd_3977437] using wordTrace_append hprefix tailTrace_3977437
  have hstable : (prefixWord ++ tailWord_3977437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977437).length < 2 ^ (prefixWord ++ tailWord_3977437).sum := by decide
  have hdescent : baseEnd_3977437 < baseStart_3977437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977453 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3977453 : Nat := 118140960795 + 3977453 * 2 ^ 59
def prefixEnd_3977453 : Nat := 4983230072969 + 3 ^ 40 * 3977453 * 2
def baseEnd_3977453 : Nat := 2042345169667531930545533

theorem tailTrace_3977453 : CollatzResearch.WordTrace tailWord_3977453 prefixEnd_3977453 2042345169667531930545533 := by
  unfold tailWord_3977453
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069628859374550736081013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96713085906249700490720675 145069628859374550736081013)
  ·
    refine ⟨13600277705566364131507595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145069628859374550736081013 13600277705566364131507595)
    ·
      refine ⟨20400416558349546197261393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13600277705566364131507595 20400416558349546197261393)
      ·
        refine ⟨15300312418762159647946045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20400416558349546197261393 15300312418762159647946045)
        ·
          refine ⟨5737617157035809867979767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15300312418762159647946045 5737617157035809867979767)
          ·
            refine ⟨8606425735553714801969651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737617157035809867979767 8606425735553714801969651)
            ·
              refine ⟨12909638603330572202954477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606425735553714801969651 12909638603330572202954477)
              ·
                refine ⟨4841114476248964576107929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12909638603330572202954477 4841114476248964576107929)
                ·
                  refine ⟨3630835857186723432080947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841114476248964576107929 3630835857186723432080947)
                  ·
                    refine ⟨5446253785780085148121421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630835857186723432080947 5446253785780085148121421)
                    ·
                      refine ⟨2042345169667531930545533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446253785780085148121421 2042345169667531930545533)
                      ·
                        rfl

theorem cell23_3977453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3977453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977453 prefixEnd_3977453 := by exact prefixLift 3977453
  have htrace : WordTrace (prefixWord ++ tailWord_3977453) baseStart_3977453 baseEnd_3977453 := by
    simpa [prefixWord, tailWord_3977453, baseEnd_3977453] using wordTrace_append hprefix tailTrace_3977453
  have hstable : (prefixWord ++ tailWord_3977453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977453).length < 2 ^ (prefixWord ++ tailWord_3977453).sum := by decide
  have hdescent : baseEnd_3977453 < baseStart_3977453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977459 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 4, 2]
def baseStart_3977459 : Nat := 118140960795 + 3977459 * 2 ^ 59
def prefixEnd_3977459 : Nat := 4983230072969 + 3 ^ 40 * 3977459 * 2
def baseEnd_3977459 : Nat := 2042348250551458907070505

theorem tailTrace_3977459 : CollatzResearch.WordTrace tailWord_3977459 prefixEnd_3977459 2042348250551458907070505 := by
  unfold tailWord_3977459
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069847697352813760799431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96713231798235209173866287 145069847697352813760799431)
  ·
    refine ⟨217604771546029220641199147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145069847697352813760799431 217604771546029220641199147)
    ·
      refine ⟨326407157319043830961798721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217604771546029220641199147 326407157319043830961798721)
      ·
        refine ⟨244805367989282873221349041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326407157319043830961798721 244805367989282873221349041)
        ·
          refine ⟨183604025991962154916011781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244805367989282873221349041 183604025991962154916011781)
          ·
            refine ⟨34425754873492904046752209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183604025991962154916011781 34425754873492904046752209)
            ·
              refine ⟨25819316155119678035064157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34425754873492904046752209 25819316155119678035064157)
              ·
                refine ⟨9682243558169879263149059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25819316155119678035064157 9682243558169879263149059)
                ·
                  refine ⟨14523365337254818894723589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682243558169879263149059 14523365337254818894723589)
                  ·
                    refine ⟨2723131000735278542760673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14523365337254818894723589 2723131000735278542760673)
                    ·
                      refine ⟨2042348250551458907070505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723131000735278542760673 2042348250551458907070505)
                      ·
                        rfl

theorem cell23_3977459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4, 2].length) (baseStart_3977459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977459 prefixEnd_3977459 := by exact prefixLift 3977459
  have htrace : WordTrace (prefixWord ++ tailWord_3977459) baseStart_3977459 baseEnd_3977459 := by
    simpa [prefixWord, tailWord_3977459, baseEnd_3977459] using wordTrace_append hprefix tailTrace_3977459
  have hstable : (prefixWord ++ tailWord_3977459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977459).length < 2 ^ (prefixWord ++ tailWord_3977459).sum := by decide
  have hdescent : baseEnd_3977459 < baseStart_3977459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977529 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_3977529 : Nat := 118140960795 + 3977529 * 2 ^ 59
def prefixEnd_3977529 : Nat := 4983230072969 + 3 ^ 40 * 3977529 * 2
def baseEnd_3977529 : Nat := 680794731399091211065061

theorem tailTrace_3977529 : CollatzResearch.WordTrace tailWord_3977529 prefixEnd_3977529 680794731399091211065061 := by
  unfold tailWord_3977529
  simp only [CollatzResearch.WordTrace]
  refine ⟨145072400807099215715847641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96714933871399477143898427 145072400807099215715847641)
  ·
    refine ⟨108804300605324411786885731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145072400807099215715847641 108804300605324411786885731)
    ·
      refine ⟨163206450907986617680328597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108804300605324411786885731 163206450907986617680328597)
      ·
        refine ⟨7650302386311872703765403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163206450907986617680328597 7650302386311872703765403)
        ·
          refine ⟨11475453579467809055648105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650302386311872703765403 11475453579467809055648105)
          ·
            refine ⟨8606590184600856791736079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475453579467809055648105 8606590184600856791736079)
            ·
              refine ⟨12909885276901285187604119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606590184600856791736079 12909885276901285187604119)
              ·
                refine ⟨19364827915351927781406179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12909885276901285187604119 19364827915351927781406179)
                ·
                  refine ⟨29047241873027891672109269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19364827915351927781406179 29047241873027891672109269)
                  ·
                    refine ⟨680794731399091211065061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29047241873027891672109269 680794731399091211065061)
                    ·
                      rfl

theorem cell23_3977529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_3977529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977529 prefixEnd_3977529 := by exact prefixLift 3977529
  have htrace : WordTrace (prefixWord ++ tailWord_3977529) baseStart_3977529 baseEnd_3977529 := by
    simpa [prefixWord, tailWord_3977529, baseEnd_3977529] using wordTrace_append hprefix tailTrace_3977529
  have hstable : (prefixWord ++ tailWord_3977529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977529).length < 2 ^ (prefixWord ++ tailWord_3977529).sum := by decide
  have hdescent : baseEnd_3977529 < baseStart_3977529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977562 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3977562 : Nat := 118140960795 + 3977562 * 2 ^ 59
def prefixEnd_3977562 : Nat := 4983230072969 + 3 ^ 40 * 3977562 * 2
def baseEnd_3977562 : Nat := 2042401139058872004082531

theorem tailTrace_3977562 : CollatzResearch.WordTrace tailWord_3977562 prefixEnd_3977562 2042401139058872004082531 := by
  unfold tailWord_3977562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268401103994915587949735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96715736277319774901199293 36268401103994915587949735)
  ·
    refine ⟨54402601655992373381924603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36268401103994915587949735 54402601655992373381924603)
    ·
      refine ⟨81603902483988560072886905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54402601655992373381924603 81603902483988560072886905)
      ·
        refine ⟨61202926862991420054665179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81603902483988560072886905 61202926862991420054665179)
        ·
          refine ⟨91804390294487130081997769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61202926862991420054665179 91804390294487130081997769)
          ·
            refine ⟨68853292720865347561498327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91804390294487130081997769 68853292720865347561498327)
            ·
              refine ⟨103279939081298021342247491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68853292720865347561498327 103279939081298021342247491)
              ·
                refine ⟨154919908621947032013371237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103279939081298021342247491 154919908621947032013371237)
                ·
                  refine ⟨29047482866615068502507107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154919908621947032013371237 29047482866615068502507107)
                  ·
                    refine ⟨43571224299922602753760661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29047482866615068502507107 43571224299922602753760661)
                    ·
                      refine ⟨2042401139058872004082531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43571224299922602753760661 2042401139058872004082531)
                      ·
                        rfl

theorem cell23_3977562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3977562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977562 prefixEnd_3977562 := by exact prefixLift 3977562
  have htrace : WordTrace (prefixWord ++ tailWord_3977562) baseStart_3977562 baseEnd_3977562 := by
    simpa [prefixWord, tailWord_3977562, baseEnd_3977562] using wordTrace_append hprefix tailTrace_3977562
  have hstable : (prefixWord ++ tailWord_3977562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977562).length < 2 ^ (prefixWord ++ tailWord_3977562).sum := by decide
  have hdescent : baseEnd_3977562 < baseStart_3977562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977576 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_3977576 : Nat := 118140960795 + 3977576 * 2 ^ 59
def prefixEnd_3977576 : Nat := 4983230072969 + 3 ^ 40 * 3977576 * 2
def baseEnd_3977576 : Nat := 680802775929344983102489

theorem tailTrace_3977576 : CollatzResearch.WordTrace tailWord_3977576 prefixEnd_3977576 680802775929344983102489 := by
  unfold tailWord_3977576
  simp only [CollatzResearch.WordTrace]
  refine ⟨72537057518964471371404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96716076691952628495205721 72537057518964471371404291)
  ·
    refine ⟨108805586278446707057106437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72537057518964471371404291 108805586278446707057106437)
    ·
      refine ⟨20401047427208757573207457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108805586278446707057106437 20401047427208757573207457)
      ·
        refine ⟨15300785570406568179905593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20401047427208757573207457 15300785570406568179905593)
        ·
          refine ⟨11475589177804926134929195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300785570406568179905593 11475589177804926134929195)
          ·
            refine ⟨17213383766707389202393793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475589177804926134929195 17213383766707389202393793)
            ·
              refine ⟨12910037825030541901795345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17213383766707389202393793 12910037825030541901795345)
              ·
                refine ⟨9682528368772906426346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12910037825030541901795345 9682528368772906426346509)
                ·
                  refine ⟨3630948138289839909879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9682528368772906426346509 3630948138289839909879941)
                  ·
                    refine ⟨680802775929344983102489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630948138289839909879941 680802775929344983102489)
                    ·
                      rfl

theorem cell23_3977576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_3977576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977576 prefixEnd_3977576 := by exact prefixLift 3977576
  have htrace : WordTrace (prefixWord ++ tailWord_3977576) baseStart_3977576 baseEnd_3977576 := by
    simpa [prefixWord, tailWord_3977576, baseEnd_3977576] using wordTrace_append hprefix tailTrace_3977576
  have hstable : (prefixWord ++ tailWord_3977576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977576).length < 2 ^ (prefixWord ++ tailWord_3977576).sum := by decide
  have hdescent : baseEnd_3977576 < baseStart_3977576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977589 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 8]
def baseStart_3977589 : Nat := 118140960795 + 3977589 * 2 ^ 59
def prefixEnd_3977589 : Nat := 4983230072969 + 3 ^ 40 * 3977589 * 2
def baseEnd_3977589 : Nat := 226935000337393710938323

theorem tailTrace_3977589 : CollatzResearch.WordTrace tailWord_3977589 prefixEnd_3977589 226935000337393710938323 := by
  unfold tailWord_3977589
  simp only [CollatzResearch.WordTrace]
  refine ⟨145074589186881845963031821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96716392791254563975354547 145074589186881845963031821)
  ·
    refine ⟨54402970945080692236136933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145074589186881845963031821 54402970945080692236136933)
    ·
      refine ⟨10200557052202629794275675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54402970945080692236136933 10200557052202629794275675)
      ·
        refine ⟨15300835578303944691413513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200557052202629794275675 15300835578303944691413513)
        ·
          refine ⟨11475626683727958518560135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300835578303944691413513 11475626683727958518560135)
          ·
            refine ⟨17213440025591937777840203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475626683727958518560135 17213440025591937777840203)
            ·
              refine ⟨25820160038387906666760305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17213440025591937777840203 25820160038387906666760305)
              ·
                refine ⟨19365120028790930000070229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25820160038387906666760305 19365120028790930000070229)
                ·
                  refine ⟨226935000337393710938323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19365120028790930000070229 226935000337393710938323)
                  ·
                    rfl

theorem cell23_3977589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_3977589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977589 prefixEnd_3977589 := by exact prefixLift 3977589
  have htrace : WordTrace (prefixWord ++ tailWord_3977589) baseStart_3977589 baseEnd_3977589 := by
    simpa [prefixWord, tailWord_3977589, baseEnd_3977589] using wordTrace_append hprefix tailTrace_3977589
  have hstable : (prefixWord ++ tailWord_3977589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977589).length < 2 ^ (prefixWord ++ tailWord_3977589).sum := by decide
  have hdescent : baseEnd_3977589 < baseStart_3977589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977610 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_3977610 : Nat := 118140960795 + 3977610 * 2 ^ 59
def prefixEnd_3977610 : Nat := 4983230072969 + 3 ^ 40 * 3977610 * 2
def baseEnd_3977610 : Nat := 680808595376762605427437

theorem tailTrace_3977610 : CollatzResearch.WordTrace tailWord_3977610 prefixEnd_3977610 680808595376762605427437 := by
  unfold tailWord_3977610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268838779951441637386571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96716903413203844366364189 36268838779951441637386571)
  ·
    refine ⟨54403258169927162456079857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36268838779951441637386571 54403258169927162456079857)
    ·
      refine ⟨40802443627445371842059893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54403258169927162456079857 40802443627445371842059893)
      ·
        refine ⟨3825229090073003610193115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40802443627445371842059893 3825229090073003610193115)
        ·
          refine ⟨5737843635109505415289673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825229090073003610193115 5737843635109505415289673)
          ·
            refine ⟨4303382726332129061467255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737843635109505415289673 4303382726332129061467255)
            ·
              refine ⟨6455074089498193592200883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303382726332129061467255 6455074089498193592200883)
              ·
                refine ⟨9682611134247290388301325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455074089498193592200883 9682611134247290388301325)
                ·
                  refine ⟨3630979175342733895612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9682611134247290388301325 3630979175342733895612997)
                  ·
                    refine ⟨680808595376762605427437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630979175342733895612997 680808595376762605427437)
                    ·
                      rfl

theorem cell23_3977610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_3977610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977610 prefixEnd_3977610 := by exact prefixLift 3977610
  have htrace : WordTrace (prefixWord ++ tailWord_3977610) baseStart_3977610 baseEnd_3977610 := by
    simpa [prefixWord, tailWord_3977610, baseEnd_3977610] using wordTrace_append hprefix tailTrace_3977610
  have hstable : (prefixWord ++ tailWord_3977610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977610).length < 2 ^ (prefixWord ++ tailWord_3977610).sum := by decide
  have hdescent : baseEnd_3977610 < baseStart_3977610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977636 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_3977636 : Nat := 118140960795 + 3977636 * 2 ^ 59
def prefixEnd_3977636 : Nat := 4983230072969 + 3 ^ 40 * 3977636 * 2
def baseEnd_3977636 : Nat := 680813045542434904852397

theorem tailTrace_3977636 : CollatzResearch.WordTrace tailWord_3977636 prefixEnd_3977636 680813045542434904852397 := by
  unfold tailWord_3977636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72538151708855786494996381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96717535611807715326661841 72538151708855786494996381)
  ·
    refine ⟨27201806890820919935623643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72538151708855786494996381 27201806890820919935623643)
    ·
      refine ⟨40802710336231379903435465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201806890820919935623643 40802710336231379903435465)
      ·
        refine ⟨30602032752173534927576599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40802710336231379903435465 30602032752173534927576599)
        ·
          refine ⟨45903049128260302391364899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30602032752173534927576599 45903049128260302391364899)
          ·
            refine ⟨68854573692390453587047349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45903049128260302391364899 68854573692390453587047349)
            ·
              refine ⟨6455116283661605023785689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68854573692390453587047349 6455116283661605023785689)
              ·
                refine ⟨4841337212746203767839267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455116283661605023785689 4841337212746203767839267)
                ·
                  refine ⟨7262005819119305651758901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841337212746203767839267 7262005819119305651758901)
                  ·
                    refine ⟨680813045542434904852397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262005819119305651758901 680813045542434904852397)
                    ·
                      rfl

theorem cell23_3977636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_3977636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977636 prefixEnd_3977636 := by exact prefixLift 3977636
  have htrace : WordTrace (prefixWord ++ tailWord_3977636) baseStart_3977636 baseEnd_3977636 := by
    simpa [prefixWord, tailWord_3977636, baseEnd_3977636] using wordTrace_append hprefix tailTrace_3977636
  have hstable : (prefixWord ++ tailWord_3977636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977636).length < 2 ^ (prefixWord ++ tailWord_3977636).sum := by decide
  have hdescent : baseEnd_3977636 < baseStart_3977636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977649 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_3977649 : Nat := 118140960795 + 3977649 * 2 ^ 59
def prefixEnd_3977649 : Nat := 4983230072969 + 3 ^ 40 * 3977649 * 2
def baseEnd_3977649 : Nat := 680815270625271054564877

theorem tailTrace_3977649 : CollatzResearch.WordTrace tailWord_3977649 prefixEnd_3977649 680815270625271054564877 := by
  unfold tailWord_3977649
  simp only [CollatzResearch.WordTrace]
  refine ⟨145076777566664476210216001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96717851711109650806810667 145076777566664476210216001)
  ·
    refine ⟨108807583174998357157662001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145076777566664476210216001 108807583174998357157662001)
    ·
      refine ⟨81605687381248767868246501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108807583174998357157662001 81605687381248767868246501)
      ·
        refine ⟨15301066383984143975296219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81605687381248767868246501 15301066383984143975296219)
        ·
          refine ⟨22951599575976215962944329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301066383984143975296219 22951599575976215962944329)
          ·
            refine ⟨17213699681982161972208247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22951599575976215962944329 17213699681982161972208247)
            ·
              refine ⟨25820549522973242958312371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17213699681982161972208247 25820549522973242958312371)
              ·
                refine ⟨38730824284459864437468557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25820549522973242958312371 38730824284459864437468557)
                ·
                  refine ⟨14524059106672449164050709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38730824284459864437468557 14524059106672449164050709)
                  ·
                    refine ⟨680815270625271054564877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14524059106672449164050709 680815270625271054564877)
                    ·
                      rfl

theorem cell23_3977649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_3977649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977649 prefixEnd_3977649 := by exact prefixLift 3977649
  have htrace : WordTrace (prefixWord ++ tailWord_3977649) baseStart_3977649 baseEnd_3977649 := by
    simpa [prefixWord, tailWord_3977649, baseEnd_3977649] using wordTrace_append hprefix tailTrace_3977649
  have hstable : (prefixWord ++ tailWord_3977649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977649).length < 2 ^ (prefixWord ++ tailWord_3977649).sum := by decide
  have hdescent : baseEnd_3977649 < baseStart_3977649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977693 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3977693 : Nat := 118140960795 + 3977693 * 2 ^ 59
def prefixEnd_3977693 : Nat := 4983230072969 + 3 ^ 40 * 3977693 * 2
def baseEnd_3977693 : Nat := 2042468405024610991544429

theorem tailTrace_3977693 : CollatzResearch.WordTrace tailWord_3977693 prefixEnd_3977693 2042468405024610991544429 := by
  unfold tailWord_3977693
  simp only [CollatzResearch.WordTrace]
  refine ⟨145078382378505071724817733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96718921585670047816545155 145078382378505071724817733)
  ·
    refine ⟨27202196695969700948403325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145078382378505071724817733 27202196695969700948403325)
    ·
      refine ⟨10200823760988637855651247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27202196695969700948403325 10200823760988637855651247)
      ·
        refine ⟨15301235641482956783476871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200823760988637855651247 15301235641482956783476871)
        ·
          refine ⟨22951853462224435175215307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301235641482956783476871 22951853462224435175215307)
          ·
            refine ⟨34427780193336652762822961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22951853462224435175215307 34427780193336652762822961)
            ·
              refine ⟨25820835145002489572117221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34427780193336652762822961 25820835145002489572117221)
              ·
                refine ⟨4841406589687966794771979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25820835145002489572117221 4841406589687966794771979)
                ·
                  refine ⟨7262109884531950192157969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841406589687966794771979 7262109884531950192157969)
                  ·
                    refine ⟨5446582413398962644118477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262109884531950192157969 5446582413398962644118477)
                    ·
                      refine ⟨2042468405024610991544429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446582413398962644118477 2042468405024610991544429)
                      ·
                        rfl

theorem cell23_3977693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3977693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977693 prefixEnd_3977693 := by exact prefixLift 3977693
  have htrace : WordTrace (prefixWord ++ tailWord_3977693) baseStart_3977693 baseEnd_3977693 := by
    simpa [prefixWord, tailWord_3977693, baseEnd_3977693] using wordTrace_append hprefix tailTrace_3977693
  have hstable : (prefixWord ++ tailWord_3977693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977693).length < 2 ^ (prefixWord ++ tailWord_3977693).sum := by decide
  have hdescent : baseEnd_3977693 < baseStart_3977693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977710 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_3977710 : Nat := 118140960795 + 3977710 * 2 ^ 59
def prefixEnd_3977710 : Nat := 4983230072969 + 3 ^ 40 * 3977710 * 2
def baseEnd_3977710 : Nat := 2042477134195737425031851

theorem tailTrace_3977710 : CollatzResearch.WordTrace tailWord_3977710 prefixEnd_3977710 2042477134195737425031851 := by
  unfold tailWord_3977710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134875302430435453523323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96719334946295655752124389 18134875302430435453523323)
  ·
    refine ⟨27202312953645653180284985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18134875302430435453523323 27202312953645653180284985)
    ·
      refine ⟨20401734715234239885213739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27202312953645653180284985 20401734715234239885213739)
      ·
        refine ⟨30602602072851359827820609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20401734715234239885213739 30602602072851359827820609)
        ·
          refine ⟨22951951554638519870865457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30602602072851359827820609 22951951554638519870865457)
          ·
            refine ⟨17213963665978889903149093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22951951554638519870865457 17213963665978889903149093)
            ·
              refine ⟨3227618187371041856840455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17213963665978889903149093 3227618187371041856840455)
              ·
                refine ⟨4841427281056562785260683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227618187371041856840455 4841427281056562785260683)
                ·
                  refine ⟨7262140921584844177891025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841427281056562785260683 7262140921584844177891025)
                  ·
                    refine ⟨5446605691188633133418269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262140921584844177891025 5446605691188633133418269)
                    ·
                      refine ⟨2042477134195737425031851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446605691188633133418269 2042477134195737425031851)
                      ·
                        rfl

theorem cell23_3977710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_3977710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977710 prefixEnd_3977710 := by exact prefixLift 3977710
  have htrace : WordTrace (prefixWord ++ tailWord_3977710) baseStart_3977710 baseEnd_3977710 := by
    simpa [prefixWord, tailWord_3977710, baseEnd_3977710] using wordTrace_append hprefix tailTrace_3977710
  have hstable : (prefixWord ++ tailWord_3977710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977710).length < 2 ^ (prefixWord ++ tailWord_3977710).sum := by decide
  have hdescent : baseEnd_3977710 < baseStart_3977710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977717 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3977717 : Nat := 118140960795 + 3977717 * 2 ^ 59
def prefixEnd_3977717 : Nat := 4983230072969 + 3 ^ 40 * 3977717 * 2
def baseEnd_3977717 : Nat := 680826909520106299214773

theorem tailTrace_3977717 : CollatzResearch.WordTrace tailWord_3977717 prefixEnd_3977717 680826909520106299214773 := by
  unfold tailWord_3977717
  simp only [CollatzResearch.WordTrace]
  refine ⟨145079257730418123823691405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96719505153612082549127603 145079257730418123823691405)
  ·
    refine ⟨54404721648906796433884277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145079257730418123823691405 54404721648906796433884277)
    ·
      refine ⟨5100442654585012165676651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54404721648906796433884277 5100442654585012165676651)
      ·
        refine ⟨7650663981877518248514977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100442654585012165676651 7650663981877518248514977)
        ·
          refine ⟨5737997986408138686386233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7650663981877518248514977 5737997986408138686386233)
          ·
            refine ⟨4303498489806104014789675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737997986408138686386233 4303498489806104014789675)
            ·
              refine ⟨6455247734709156022184513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303498489806104014789675 6455247734709156022184513)
              ·
                refine ⟨4841435801031867016638385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455247734709156022184513 4841435801031867016638385)
                ·
                  refine ⟨3631076850773900262478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841435801031867016638385 3631076850773900262478789)
                  ·
                    refine ⟨680826909520106299214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3631076850773900262478789 680826909520106299214773)
                    ·
                      rfl

theorem cell23_3977717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3977717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977717 prefixEnd_3977717 := by exact prefixLift 3977717
  have htrace : WordTrace (prefixWord ++ tailWord_3977717) baseStart_3977717 baseEnd_3977717 := by
    simpa [prefixWord, tailWord_3977717, baseEnd_3977717] using wordTrace_append hprefix tailTrace_3977717
  have hstable : (prefixWord ++ tailWord_3977717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977717).length < 2 ^ (prefixWord ++ tailWord_3977717).sum := by decide
  have hdescent : baseEnd_3977717 < baseStart_3977717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977779 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_3977779 : Nat := 118140960795 + 3977779 * 2 ^ 59
def prefixEnd_3977779 : Nat := 4983230072969 + 3 ^ 40 * 3977779 * 2
def baseEnd_3977779 : Nat := 2042512564360897655069033

theorem tailTrace_3977779 : CollatzResearch.WordTrace tailWord_3977779 prefixEnd_3977779 2042512564360897655069033 := by
  unfold tailWord_3977779
  simp only [CollatzResearch.WordTrace]
  refine ⟨145081519056193508412448391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96721012704129005608298927 145081519056193508412448391)
  ·
    refine ⟨217622278584290262618672587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145081519056193508412448391 217622278584290262618672587)
    ·
      refine ⟨326433417876435393928008881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217622278584290262618672587 326433417876435393928008881)
      ·
        refine ⟨244825063407326545446006661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326433417876435393928008881 244825063407326545446006661)
        ·
          refine ⟨45904699388873727271126249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244825063407326545446006661 45904699388873727271126249)
          ·
            refine ⟨34428524541655295453344687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45904699388873727271126249 34428524541655295453344687)
            ·
              refine ⟨51642786812482943180017031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34428524541655295453344687 51642786812482943180017031)
              ·
                refine ⟨77464180218724414770025547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51642786812482943180017031 77464180218724414770025547)
                ·
                  refine ⟨116196270328086622155038321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77464180218724414770025547 116196270328086622155038321)
                  ·
                    refine ⟨87147202746064966616278741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116196270328086622155038321 87147202746064966616278741)
                    ·
                      refine ⟨2042512564360897655069033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87147202746064966616278741 2042512564360897655069033)
                      ·
                        rfl

theorem cell23_3977779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_3977779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977779 prefixEnd_3977779 := by exact prefixLift 3977779
  have htrace : WordTrace (prefixWord ++ tailWord_3977779) baseStart_3977779 baseEnd_3977779 := by
    simpa [prefixWord, tailWord_3977779, baseEnd_3977779] using wordTrace_append hprefix tailTrace_3977779
  have hstable : (prefixWord ++ tailWord_3977779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977779).length < 2 ^ (prefixWord ++ tailWord_3977779).sum := by decide
  have hdescent : baseEnd_3977779 < baseStart_3977779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977786 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_3977786 : Nat := 118140960795 + 3977786 * 2 ^ 59
def prefixEnd_3977786 : Nat := 4983230072969 + 3 ^ 40 * 3977786 * 2
def baseEnd_3977786 : Nat := 226946239858386569742389

theorem tailTrace_3977786 : CollatzResearch.WordTrace tailWord_3977786 prefixEnd_3977786 226946239858386569742389 := by
  unfold tailWord_3977786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270443591792037151988303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96721182911445432405302141 36270443591792037151988303)
  ·
    refine ⟨54405665387688055727982455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270443591792037151988303 54405665387688055727982455)
    ·
      refine ⟨81608498081532083591973683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405665387688055727982455 81608498081532083591973683)
      ·
        refine ⟨122412747122298125387960525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81608498081532083591973683 122412747122298125387960525)
        ·
          refine ⟨45904780170861797020485197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122412747122298125387960525 45904780170861797020485197)
          ·
            refine ⟨17214292564073173882681949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45904780170861797020485197 17214292564073173882681949)
            ·
              refine ⟨6455359711527440206005731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17214292564073173882681949 6455359711527440206005731)
              ·
                refine ⟨9683039567291160309008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455359711527440206005731 9683039567291160309008597)
                ·
                  refine ⟨226946239858386569742389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9683039567291160309008597 226946239858386569742389)
                  ·
                    rfl

theorem cell23_3977786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_3977786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977786 prefixEnd_3977786 := by exact prefixLift 3977786
  have htrace : WordTrace (prefixWord ++ tailWord_3977786) baseStart_3977786 baseEnd_3977786 := by
    simpa [prefixWord, tailWord_3977786, baseEnd_3977786] using wordTrace_append hprefix tailTrace_3977786
  have hstable : (prefixWord ++ tailWord_3977786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977786).length < 2 ^ (prefixWord ++ tailWord_3977786).sum := by decide
  have hdescent : baseEnd_3977786 < baseStart_3977786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977797 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_3977797 : Nat := 118140960795 + 3977797 * 2 ^ 59
def prefixEnd_3977797 : Nat := 4983230072969 + 3 ^ 40 * 3977797 * 2
def baseEnd_3977797 : Nat := 2042521807012678584643951

theorem tailTrace_3977797 : CollatzResearch.WordTrace tailWord_3977797 prefixEnd_3977797 2042521807012678584643951 := by
  unfold tailWord_3977797
  simp only [CollatzResearch.WordTrace]
  refine ⟨145082175570128297486603645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96721450380085531657735763 145082175570128297486603645)
  ·
    refine ⟨54405815838798111557476367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145082175570128297486603645 54405815838798111557476367)
    ·
      refine ⟨81608723758197167336214551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405815838798111557476367 81608723758197167336214551)
      ·
        refine ⟨122413085637295751004321827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81608723758197167336214551 122413085637295751004321827)
        ·
          refine ⟨183619628455943626506482741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122413085637295751004321827 183619628455943626506482741)
          ·
            refine ⟨17214340167744714984982757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183619628455943626506482741 17214340167744714984982757)
            ·
              refine ⟨3227688781452134059684267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17214340167744714984982757 3227688781452134059684267)
              ·
                refine ⟨4841533172178201089526401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227688781452134059684267 4841533172178201089526401)
                ·
                  refine ⟨3631149879133650817144801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841533172178201089526401 3631149879133650817144801)
                  ·
                    refine ⟨2723362409350238112858601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3631149879133650817144801 2723362409350238112858601)
                    ·
                      refine ⟨2042521807012678584643951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723362409350238112858601 2042521807012678584643951)
                      ·
                        rfl

theorem cell23_3977797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_3977797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977797 prefixEnd_3977797 := by exact prefixLift 3977797
  have htrace : WordTrace (prefixWord ++ tailWord_3977797) baseStart_3977797 baseEnd_3977797 := by
    simpa [prefixWord, tailWord_3977797, baseEnd_3977797] using wordTrace_append hprefix tailTrace_3977797
  have hstable : (prefixWord ++ tailWord_3977797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977797).length < 2 ^ (prefixWord ++ tailWord_3977797).sum := by decide
  have hdescent : baseEnd_3977797 < baseStart_3977797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977816 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_3977816 : Nat := 118140960795 + 3977816 * 2 ^ 59
def prefixEnd_3977816 : Nat := 4983230072969 + 3 ^ 40 * 3977816 * 2
def baseEnd_3977816 : Nat := 680843854381704670102121

theorem tailTrace_3977816 : CollatzResearch.WordTrace tailWord_3977816 prefixEnd_3977816 680843854381704670102121 := by
  unfold tailWord_3977816
  simp only [CollatzResearch.WordTrace]
  refine ⟨72541434278529731865772651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96721912371372975821030201 72541434278529731865772651)
  ·
    refine ⟨108812151417794597798658977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72541434278529731865772651 108812151417794597798658977)
    ·
      refine ⟨81609113563345948348994233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108812151417794597798658977 81609113563345948348994233)
      ·
        refine ⟨61206835172509461261745675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81609113563345948348994233 61206835172509461261745675)
        ·
          refine ⟨91810252758764191892618513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61206835172509461261745675 91810252758764191892618513)
          ·
            refine ⟨68857689569073143919463885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91810252758764191892618513 68857689569073143919463885)
            ·
              refine ⟨25821633588402428969798957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68857689569073143919463885 25821633588402428969798957)
              ·
                refine ⟨9683112595650910863674609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25821633588402428969798957 9683112595650910863674609)
                ·
                  refine ⟨7262334446738183147755957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683112595650910863674609 7262334446738183147755957)
                  ·
                    refine ⟨680843854381704670102121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262334446738183147755957 680843854381704670102121)
                    ·
                      rfl

theorem cell23_3977816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_3977816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977816 prefixEnd_3977816 := by exact prefixLift 3977816
  have htrace : WordTrace (prefixWord ++ tailWord_3977816) baseStart_3977816 baseEnd_3977816 := by
    simpa [prefixWord, tailWord_3977816, baseEnd_3977816] using wordTrace_append hprefix tailTrace_3977816
  have hstable : (prefixWord ++ tailWord_3977816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977816).length < 2 ^ (prefixWord ++ tailWord_3977816).sum := by decide
  have hdescent : baseEnd_3977816 < baseStart_3977816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977837 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3977837 : Nat := 118140960795 + 3977837 * 2 ^ 59
def prefixEnd_3977837 : Nat := 4983230072969 + 3 ^ 40 * 3977837 * 2
def baseEnd_3977837 : Nat := 226949149582095380904863

theorem tailTrace_3977837 : CollatzResearch.WordTrace tailWord_3977837 prefixEnd_3977837 226949149582095380904863 := by
  unfold tailWord_3977837
  simp only [CollatzResearch.WordTrace]
  refine ⟨145083634489983384318059765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96722422993322256212039843 145083634489983384318059765)
  ·
    refine ⟨13601590733435942279818103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145083634489983384318059765 13601590733435942279818103)
    ·
      refine ⟨20402386100153913419727155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13601590733435942279818103 20402386100153913419727155)
      ·
        refine ⟨30603579150230870129590733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20402386100153913419727155 30603579150230870129590733)
        ·
          refine ⟨11476342181336576298596525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30603579150230870129590733 11476342181336576298596525)
          ·
            refine ⟨4303628318001216111973697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11476342181336576298596525 4303628318001216111973697)
            ·
              refine ⟨3227721238500912083980273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303628318001216111973697 3227721238500912083980273)
              ·
                refine ⟨2420790928875684062985205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227721238500912083980273 2420790928875684062985205)
                ·
                  refine ⟨226949149582095380904863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2420790928875684062985205 226949149582095380904863)
                  ·
                    rfl

theorem cell23_3977837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3977837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977837 prefixEnd_3977837 := by exact prefixLift 3977837
  have htrace : WordTrace (prefixWord ++ tailWord_3977837) baseStart_3977837 baseEnd_3977837 := by
    simpa [prefixWord, tailWord_3977837, baseEnd_3977837] using wordTrace_append hprefix tailTrace_3977837
  have hstable : (prefixWord ++ tailWord_3977837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977837).length < 2 ^ (prefixWord ++ tailWord_3977837).sum := by decide
  have hdescent : baseEnd_3977837 < baseStart_3977837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977863 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 3, 4]
def baseStart_3977863 : Nat := 118140960795 + 3977863 * 2 ^ 59
def prefixEnd_3977863 : Nat := 4983230072969 + 3 ^ 40 * 3977863 * 2
def baseEnd_3977863 : Nat := 680851898911958442139549

theorem tailTrace_3977863 : CollatzResearch.WordTrace tailWord_3977863 prefixEnd_3977863 680851898911958442139549 := by
  unfold tailWord_3977863
  simp only [CollatzResearch.WordTrace]
  refine ⟨145084582787889190758506243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96723055191926127172337495 145084582787889190758506243)
  ·
    refine ⟨217626874181833786137759365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145084582787889190758506243 217626874181833786137759365)
    ·
      refine ⟨40805038909093834900829881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217626874181833786137759365 40805038909093834900829881)
      ·
        refine ⟨30603779181820376175622411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40805038909093834900829881 30603779181820376175622411)
        ·
          refine ⟨45905668772730564263433617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30603779181820376175622411 45905668772730564263433617)
          ·
            refine ⟨34429251579547923197575213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45905668772730564263433617 34429251579547923197575213)
            ·
              refine ⟨12910969342330471199090705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34429251579547923197575213 12910969342330471199090705)
              ·
                refine ⟨9683227006747853399318029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12910969342330471199090705 9683227006747853399318029)
                ·
                  refine ⟨3631210127530445024744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9683227006747853399318029 3631210127530445024744261)
                  ·
                    refine ⟨680851898911958442139549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3631210127530445024744261 680851898911958442139549)
                    ·
                      rfl

theorem cell23_3977863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_3977863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977863 prefixEnd_3977863 := by exact prefixLift 3977863
  have htrace : WordTrace (prefixWord ++ tailWord_3977863) baseStart_3977863 baseEnd_3977863 := by
    simpa [prefixWord, tailWord_3977863, baseEnd_3977863] using wordTrace_append hprefix tailTrace_3977863
  have hstable : (prefixWord ++ tailWord_3977863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977863).length < 2 ^ (prefixWord ++ tailWord_3977863).sum := by decide
  have hdescent : baseEnd_3977863 < baseStart_3977863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977920 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_3977920 : Nat := 118140960795 + 3977920 * 2 ^ 59
def prefixEnd_3977920 : Nat := 4983230072969 + 3 ^ 40 * 3977920 * 2
def baseEnd_3977920 : Nat := 2042584965133181603405885

theorem tailTrace_3977920 : CollatzResearch.WordTrace tailWord_3977920 prefixEnd_3977920 2042584965133181603405885 := by
  unfold tailWord_3977920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72543330874341344746665607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96724441165788459662220809 72543330874341344746665607)
  ·
    refine ⟨108814996311512017119998411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72543330874341344746665607 108814996311512017119998411)
    ·
      refine ⟨163222494467268025679997617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108814996311512017119998411 163222494467268025679997617)
      ·
        refine ⟨122416870850451019259998213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163222494467268025679997617 122416870850451019259998213)
        ·
          refine ⟨22953163284459566111249665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122416870850451019259998213 22953163284459566111249665)
          ·
            refine ⟨17214872463344674583437249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22953163284459566111249665 17214872463344674583437249)
            ·
              refine ⟨12911154347508505937577937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17214872463344674583437249 12911154347508505937577937)
              ·
                refine ⟨9683365760631379453183453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12911154347508505937577937 9683365760631379453183453)
                ·
                  refine ⟨3631262160236767294943795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9683365760631379453183453 3631262160236767294943795)
                  ·
                    refine ⟨5446893240355150942415693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631262160236767294943795 5446893240355150942415693)
                    ·
                      refine ⟨2042584965133181603405885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446893240355150942415693 2042584965133181603405885)
                      ·
                        rfl

theorem cell23_3977920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_3977920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977920 prefixEnd_3977920 := by exact prefixLift 3977920
  have htrace : WordTrace (prefixWord ++ tailWord_3977920) baseStart_3977920 baseEnd_3977920 := by
    simpa [prefixWord, tailWord_3977920, baseEnd_3977920] using wordTrace_append hprefix tailTrace_3977920
  have hstable : (prefixWord ++ tailWord_3977920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977920).length < 2 ^ (prefixWord ++ tailWord_3977920).sum := by decide
  have hdescent : baseEnd_3977920 < baseStart_3977920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977930 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_3977930 : Nat := 118140960795 + 3977930 * 2 ^ 59
def prefixEnd_3977930 : Nat := 4983230072969 + 3 ^ 40 * 3977930 * 2
def baseEnd_3977930 : Nat := 2042590099939726564280839

theorem tailTrace_3977930 : CollatzResearch.WordTrace tailWord_3977930 prefixEnd_3977930 2042590099939726564280839 := by
  unfold tailWord_3977930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36271756619661615300298811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96724684319097640800796829 36271756619661615300298811)
  ·
    refine ⟨54407634929492422950448217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36271756619661615300298811 54407634929492422950448217)
    ·
      refine ⟨40805726197119317212836163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54407634929492422950448217 40805726197119317212836163)
      ·
        refine ⟨61208589295678975819254245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40805726197119317212836163 61208589295678975819254245)
        ·
          refine ⟨11476610492939807966110171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61208589295678975819254245 11476610492939807966110171)
          ·
            refine ⟨17214915739409711949165257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476610492939807966110171 17214915739409711949165257)
            ·
              refine ⟨12911186804557283961873943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17214915739409711949165257 12911186804557283961873943)
              ·
                refine ⟨19366780206835925942810915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911186804557283961873943 19366780206835925942810915)
                ·
                  refine ⟨29050170310253888914216373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19366780206835925942810915 29050170310253888914216373)
                  ·
                    refine ⟨2723453466586302085707785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29050170310253888914216373 2723453466586302085707785)
                    ·
                      refine ⟨2042590099939726564280839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723453466586302085707785 2042590099939726564280839)
                      ·
                        rfl

theorem cell23_3977930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_3977930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977930 prefixEnd_3977930 := by exact prefixLift 3977930
  have htrace : WordTrace (prefixWord ++ tailWord_3977930) baseStart_3977930 baseEnd_3977930 := by
    simpa [prefixWord, tailWord_3977930, baseEnd_3977930] using wordTrace_append hprefix tailTrace_3977930
  have hstable : (prefixWord ++ tailWord_3977930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977930).length < 2 ^ (prefixWord ++ tailWord_3977930).sum := by decide
  have hdescent : baseEnd_3977930 < baseStart_3977930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977963 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3]
def baseStart_3977963 : Nat := 118140960795 + 3977963 * 2 ^ 59
def prefixEnd_3977963 : Nat := 4983230072969 + 3 ^ 40 * 3977963 * 2
def baseEnd_3977963 : Nat := 2042607044801324935168187

theorem tailTrace_3977963 : CollatzResearch.WordTrace tailWord_3977963 prefixEnd_3977963 2042607044801324935168187 := by
  unfold tailWord_3977963
  simp only [CollatzResearch.WordTrace]
  refine ⟨145088230087526907837146543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96725486725017938558097695 145088230087526907837146543)
  ·
    refine ⟨217632345131290361755719815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145088230087526907837146543 217632345131290361755719815)
    ·
      refine ⟨326448517696935542633579723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217632345131290361755719815 326448517696935542633579723)
      ·
        refine ⟨489672776545403313950369585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326448517696935542633579723 489672776545403313950369585)
        ·
          refine ⟨367254582409052485462777189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489672776545403313950369585 367254582409052485462777189)
          ·
            refine ⟨68860234201697341024270723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367254582409052485462777189 68860234201697341024270723)
            ·
              refine ⟨103290351302546011536406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68860234201697341024270723 103290351302546011536406085)
              ·
                refine ⟨19366940869227377163076141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103290351302546011536406085 19366940869227377163076141)
                ·
                  refine ⟨7262602825960266436153553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19366940869227377163076141 7262602825960266436153553)
                  ·
                    refine ⟨5446952119470199827115165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262602825960266436153553 5446952119470199827115165)
                    ·
                      refine ⟨2042607044801324935168187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446952119470199827115165 2042607044801324935168187)
                      ·
                        rfl

theorem cell23_3977963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].length) (baseStart_3977963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977963 prefixEnd_3977963 := by exact prefixLift 3977963
  have htrace : WordTrace (prefixWord ++ tailWord_3977963) baseStart_3977963 baseEnd_3977963 := by
    simpa [prefixWord, tailWord_3977963, baseEnd_3977963] using wordTrace_append hprefix tailTrace_3977963
  have hstable : (prefixWord ++ tailWord_3977963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977963).length < 2 ^ (prefixWord ++ tailWord_3977963).sum := by decide
  have hdescent : baseEnd_3977963 < baseStart_3977963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977980 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_3977980 : Nat := 118140960795 + 3977980 * 2 ^ 59
def prefixEnd_3977980 : Nat := 4983230072969 + 3 ^ 40 * 3977980 * 2
def baseEnd_3977980 : Nat := 2042615773972451368655609

theorem tailTrace_3977980 : CollatzResearch.WordTrace tailWord_3977980 prefixEnd_3977980 2042615773972451368655609 := by
  unfold tailWord_3977980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72544425064232659870257697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96725900085643546493676929 72544425064232659870257697)
  ·
    refine ⟨54408318798174494902693273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72544425064232659870257697 54408318798174494902693273)
    ·
      refine ⟨40806239098630871177019955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54408318798174494902693273 40806239098630871177019955)
      ·
        refine ⟨61209358647946306765529933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40806239098630871177019955 61209358647946306765529933)
        ·
          refine ⟨22953509492979865037073725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61209358647946306765529933 22953509492979865037073725)
          ·
            refine ⟨8607566059867449388902647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22953509492979865037073725 8607566059867449388902647)
            ·
              refine ⟨12911349089801174083353971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8607566059867449388902647 12911349089801174083353971)
              ·
                refine ⟨19367023634701761125030957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911349089801174083353971 19367023634701761125030957)
                ·
                  refine ⟨7262633863013160421886609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19367023634701761125030957 7262633863013160421886609)
                  ·
                    refine ⟨5446975397259870316414957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262633863013160421886609 5446975397259870316414957)
                    ·
                      refine ⟨2042615773972451368655609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446975397259870316414957 2042615773972451368655609)
                      ·
                        rfl

theorem cell23_3977980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_3977980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977980 prefixEnd_3977980 := by exact prefixLift 3977980
  have htrace : WordTrace (prefixWord ++ tailWord_3977980) baseStart_3977980 baseEnd_3977980 := by
    simpa [prefixWord, tailWord_3977980, baseEnd_3977980] using wordTrace_append hprefix tailTrace_3977980
  have hstable : (prefixWord ++ tailWord_3977980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977980).length < 2 ^ (prefixWord ++ tailWord_3977980).sum := by decide
  have hdescent : baseEnd_3977980 < baseStart_3977980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977993 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_3977993 : Nat := 118140960795 + 3977993 * 2 ^ 59
def prefixEnd_3977993 : Nat := 4983230072969 + 3 ^ 40 * 3977993 * 2
def baseEnd_3977993 : Nat := 2042622449220959817793049

theorem tailTrace_3977993 : CollatzResearch.WordTrace tailWord_3977993 prefixEnd_3977993 2042622449220959817793049 := by
  unfold tailWord_3977993
  simp only [CollatzResearch.WordTrace]
  refine ⟨145089324277418222960738633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96726216184945481973825755 145089324277418222960738633)
  ·
    refine ⟨108816993208063667220553975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145089324277418222960738633 108816993208063667220553975)
    ·
      refine ⟨163225489812095500830830963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108816993208063667220553975 163225489812095500830830963)
      ·
        refine ⟨244838234718143251246246445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163225489812095500830830963 244838234718143251246246445)
        ·
          refine ⟨91814338019303719217342417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244838234718143251246246445 91814338019303719217342417)
          ·
            refine ⟨68860753514477789413006813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91814338019303719217342417 68860753514477789413006813)
            ·
              refine ⟨25822782567929171029877555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68860753514477789413006813 25822782567929171029877555)
              ·
                refine ⟨38734173851893756544816333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25822782567929171029877555 38734173851893756544816333)
                ·
                  refine ⟨14525315194460158704306125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38734173851893756544816333 14525315194460158704306125)
                  ·
                    refine ⟨5446993197922559514114797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14525315194460158704306125 5446993197922559514114797)
                    ·
                      refine ⟨2042622449220959817793049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5446993197922559514114797 2042622449220959817793049)
                      ·
                        rfl

theorem cell23_3977993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_3977993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977993 prefixEnd_3977993 := by exact prefixLift 3977993
  have htrace : WordTrace (prefixWord ++ tailWord_3977993) baseStart_3977993 baseEnd_3977993 := by
    simpa [prefixWord, tailWord_3977993, baseEnd_3977993] using wordTrace_append hprefix tailTrace_3977993
  have hstable : (prefixWord ++ tailWord_3977993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977993).length < 2 ^ (prefixWord ++ tailWord_3977993).sum := by decide
  have hdescent : baseEnd_3977993 < baseStart_3977993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977994 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3977994 : Nat := 118140960795 + 3977994 * 2 ^ 59
def prefixEnd_3977994 : Nat := 4983230072969 + 3 ^ 40 * 3977994 * 2
def baseEnd_3977994 : Nat := 2042622962701614313880545

theorem tailTrace_3977994 : CollatzResearch.WordTrace tailWord_3977994 prefixEnd_3977994 2042622962701614313880545 := by
  unfold tailWord_3977994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36272340187603650032881259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96726240500276400087683357 36272340187603650032881259)
  ·
    refine ⟨54408510281405475049321889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36272340187603650032881259 54408510281405475049321889)
    ·
      refine ⟨40806382711054106286991417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54408510281405475049321889 40806382711054106286991417)
      ·
        refine ⟨30604787033290579715243563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40806382711054106286991417 30604787033290579715243563)
        ·
          refine ⟨45907180549935869572865345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30604787033290579715243563 45907180549935869572865345)
          ·
            refine ⟨34430385412451902179649009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45907180549935869572865345 34430385412451902179649009)
            ·
              refine ⟨25822789059338926634736757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34430385412451902179649009 25822789059338926634736757)
              ·
                refine ⟨2420886474313024372006571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25822789059338926634736757 2420886474313024372006571)
                ·
                  refine ⟨3631329711469536558009857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420886474313024372006571 3631329711469536558009857)
                  ·
                    refine ⟨2723497283602152418507393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3631329711469536558009857 2723497283602152418507393)
                    ·
                      refine ⟨2042622962701614313880545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723497283602152418507393 2042622962701614313880545)
                      ·
                        rfl

theorem cell23_3977994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3977994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3977994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3977994 prefixEnd_3977994 := by exact prefixLift 3977994
  have htrace : WordTrace (prefixWord ++ tailWord_3977994) baseStart_3977994 baseEnd_3977994 := by
    simpa [prefixWord, tailWord_3977994, baseEnd_3977994] using wordTrace_append hprefix tailTrace_3977994
  have hstable : (prefixWord ++ tailWord_3977994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977994).length < 2 ^ (prefixWord ++ tailWord_3977994).sum := by decide
  have hdescent : baseEnd_3977994 < baseStart_3977994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978033 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3978033 : Nat := 118140960795 + 3978033 * 2 ^ 59
def prefixEnd_3978033 : Nat := 4983230072969 + 3 ^ 40 * 3978033 * 2
def baseEnd_3978033 : Nat := 2042642988447139661292865

theorem tailTrace_3978033 : CollatzResearch.WordTrace tailWord_3978033 prefixEnd_3978033 2042642988447139661292865 := by
  unfold tailWord_3978033
  simp only [CollatzResearch.WordTrace]
  refine ⟨145090783197273309792194753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96727188798182206528129835 145090783197273309792194753)
  ·
    refine ⟨108818087397954982344146065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145090783197273309792194753 108818087397954982344146065)
    ·
      refine ⟨81613565548466236758109549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108818087397954982344146065 81613565548466236758109549)
      ·
        refine ⟨30605087080674838784291081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81613565548466236758109549 30605087080674838784291081)
        ·
          refine ⟨22953815310506129088218311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30605087080674838784291081 22953815310506129088218311)
          ·
            refine ⟨34430722965759193632327467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22953815310506129088218311 34430722965759193632327467)
            ·
              refine ⟨51646084448638790448491201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34430722965759193632327467 51646084448638790448491201)
              ·
                refine ⟨38734563336479092836368401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51646084448638790448491201 38734563336479092836368401)
                ·
                  refine ⟨29050922502359319627276301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38734563336479092836368401 29050922502359319627276301)
                  ·
                    refine ⟨10894095938384744860228613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29050922502359319627276301 10894095938384744860228613)
                    ·
                      refine ⟨2042642988447139661292865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10894095938384744860228613 2042642988447139661292865)
                      ·
                        rfl

theorem cell23_3978033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3978033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978033 prefixEnd_3978033 := by exact prefixLift 3978033
  have htrace : WordTrace (prefixWord ++ tailWord_3978033) baseStart_3978033 baseEnd_3978033 := by
    simpa [prefixWord, tailWord_3978033, baseEnd_3978033] using wordTrace_append hprefix tailTrace_3978033
  have hstable : (prefixWord ++ tailWord_3978033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978033).length < 2 ^ (prefixWord ++ tailWord_3978033).sum := by decide
  have hdescent : baseEnd_3978033 < baseStart_3978033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978037 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_3978037 : Nat := 118140960795 + 3978037 * 2 ^ 59
def prefixEnd_3978037 : Nat := 4983230072969 + 3 ^ 40 * 3978037 * 2
def baseEnd_3978037 : Nat := 2042645042369757645642847

theorem tailTrace_3978037 : CollatzResearch.WordTrace tailWord_3978037 prefixEnd_3978037 2042645042369757645642847 := by
  unfold tailWord_3978037
  simp only [CollatzResearch.WordTrace]
  refine ⟨145090929089258818475340365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96727286059505878983560243 145090929089258818475340365)
  ·
    refine ⟨54409098408472056928252637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145090929089258818475340365 54409098408472056928252637)
    ·
      refine ⟨20403411903177021348094739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54409098408472056928252637 20403411903177021348094739)
      ·
        refine ⟨30605117854765532022142109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20403411903177021348094739 30605117854765532022142109)
        ·
          refine ⟨11476919195537074508303291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30605117854765532022142109 11476919195537074508303291)
          ·
            refine ⟨17215378793305611762454937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476919195537074508303291 17215378793305611762454937)
            ·
              refine ⟨12911534094979208821841203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17215378793305611762454937 12911534094979208821841203)
              ·
                refine ⟨19367301142468813232761805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911534094979208821841203 19367301142468813232761805)
                ·
                  refine ⟨7262737928425804962285677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19367301142468813232761805 7262737928425804962285677)
                  ·
                    refine ⟨2723526723159676860857129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7262737928425804962285677 2723526723159676860857129)
                    ·
                      refine ⟨2042645042369757645642847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723526723159676860857129 2042645042369757645642847)
                      ·
                        rfl

theorem cell23_3978037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_3978037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978037 prefixEnd_3978037 := by exact prefixLift 3978037
  have htrace : WordTrace (prefixWord ++ tailWord_3978037) baseStart_3978037 baseEnd_3978037 := by
    simpa [prefixWord, tailWord_3978037, baseEnd_3978037] using wordTrace_append hprefix tailTrace_3978037
  have hstable : (prefixWord ++ tailWord_3978037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978037).length < 2 ^ (prefixWord ++ tailWord_3978037).sum := by decide
  have hdescent : baseEnd_3978037 < baseStart_3978037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978053 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_3978053 : Nat := 118140960795 + 3978053 * 2 ^ 59
def prefixEnd_3978053 : Nat := 4983230072969 + 3 ^ 40 * 3978053 * 2
def baseEnd_3978053 : Nat := 2042653258060229583042773

theorem tailTrace_3978053 : CollatzResearch.WordTrace tailWord_3978053 prefixEnd_3978053 2042653258060229583042773 := by
  unfold tailWord_3978053
  simp only [CollatzResearch.WordTrace]
  refine ⟨145091512657200853207922813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96727675104800568805281875 145091512657200853207922813)
  ·
    refine ⟨54409317246450319952971055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145091512657200853207922813 54409317246450319952971055)
    ·
      refine ⟨81613975869675479929456583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54409317246450319952971055 81613975869675479929456583)
      ·
        refine ⟨122420963804513219894184875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81613975869675479929456583 122420963804513219894184875)
        ·
          refine ⟨183631445706769829841277313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122420963804513219894184875 183631445706769829841277313)
          ·
            refine ⟨137723584280077372380957985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183631445706769829841277313 137723584280077372380957985)
            ·
              refine ⟨103292688210058029285718489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137723584280077372380957985 103292688210058029285718489)
              ·
                refine ⟨77469516157543521964288867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103292688210058029285718489 77469516157543521964288867)
                ·
                  refine ⟨116204274236315282946433301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77469516157543521964288867 116204274236315282946433301)
                  ·
                    refine ⟨5447075354827278888114061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116204274236315282946433301 5447075354827278888114061)
                    ·
                      refine ⟨2042653258060229583042773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5447075354827278888114061 2042653258060229583042773)
                      ·
                        rfl

theorem cell23_3978053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_3978053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978053 prefixEnd_3978053 := by exact prefixLift 3978053
  have htrace : WordTrace (prefixWord ++ tailWord_3978053) baseStart_3978053 baseEnd_3978053 := by
    simpa [prefixWord, tailWord_3978053, baseEnd_3978053] using wordTrace_append hprefix tailTrace_3978053
  have hstable : (prefixWord ++ tailWord_3978053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978053).length < 2 ^ (prefixWord ++ tailWord_3978053).sum := by decide
  have hdescent : baseEnd_3978053 < baseStart_3978053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978073 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 7]
def baseStart_3978073 : Nat := 118140960795 + 3978073 * 2 ^ 59
def prefixEnd_3978073 : Nat := 4983230072969 + 3 ^ 40 * 3978073 * 2
def baseEnd_3978073 : Nat := 226962614185924389421409

theorem tailTrace_3978073 : CollatzResearch.WordTrace tailWord_3978073 prefixEnd_3978073 226962614185924389421409 := by
  unfold tailWord_3978073
  simp only [CollatzResearch.WordTrace]
  refine ⟨145092242117128396623650873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96728161411418931082433915 145092242117128396623650873)
  ·
    refine ⟨108819181587846297467738155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145092242117128396623650873 108819181587846297467738155)
    ·
      refine ⟨163228772381769446201607233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108819181587846297467738155 163228772381769446201607233)
      ·
        refine ⟨122421579286327084651205425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163228772381769446201607233 122421579286327084651205425)
        ·
          refine ⟨91816184464745313488404069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122421579286327084651205425 91816184464745313488404069)
          ·
            refine ⟨17215534587139746279075763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91816184464745313488404069 17215534587139746279075763)
            ·
              refine ⟨25823301880709619418613645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17215534587139746279075763 25823301880709619418613645)
              ·
                refine ⟨9683738205266107281980117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25823301880709619418613645 9683738205266107281980117)
                ·
                  refine ⟨226962614185924389421409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9683738205266107281980117 226962614185924389421409)
                  ·
                    rfl

theorem cell23_3978073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_3978073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978073 prefixEnd_3978073 := by exact prefixLift 3978073
  have htrace : WordTrace (prefixWord ++ tailWord_3978073) baseStart_3978073 baseEnd_3978073 := by
    simpa [prefixWord, tailWord_3978073, baseEnd_3978073] using wordTrace_append hprefix tailTrace_3978073
  have hstable : (prefixWord ++ tailWord_3978073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978073).length < 2 ^ (prefixWord ++ tailWord_3978073).sum := by decide
  have hdescent : baseEnd_3978073 < baseStart_3978073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978084 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_3978084 : Nat := 118140960795 + 3978084 * 2 ^ 59
def prefixEnd_3978084 : Nat := 4983230072969 + 3 ^ 40 * 3978084 * 2
def baseEnd_3978084 : Nat := 2042669175960518961755131

theorem tailTrace_3978084 : CollatzResearch.WordTrace tailWord_3978084 prefixEnd_3978084 2042669175960518961755131 := by
  unfold tailWord_3978084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546321660044272751150653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96728428880059030334867537 72546321660044272751150653)
  ·
    refine ⟨27204870622516602281681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72546321660044272751150653 27204870622516602281681495)
    ·
      refine ⟨40807305933774903422522243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27204870622516602281681495 40807305933774903422522243)
      ·
        refine ⟨61210958900662355133783365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40807305933774903422522243 61210958900662355133783365)
        ·
          refine ⟨11477054793874191587584381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61210958900662355133783365 11477054793874191587584381)
          ·
            refine ⟨4303895547702821845344143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11477054793874191587584381 4303895547702821845344143)
            ·
              refine ⟨6455843321554232768016215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303895547702821845344143 6455843321554232768016215)
              ·
                refine ⟨9683764982331349152024323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455843321554232768016215 9683764982331349152024323)
                ·
                  refine ⟨14525647473497023728036485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683764982331349152024323 14525647473497023728036485)
                  ·
                    refine ⟨2723558901280691949006841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14525647473497023728036485 2723558901280691949006841)
                    ·
                      refine ⟨2042669175960518961755131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723558901280691949006841 2042669175960518961755131)
                      ·
                        rfl

theorem cell23_3978084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_3978084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978084 prefixEnd_3978084 := by exact prefixLift 3978084
  have htrace : WordTrace (prefixWord ++ tailWord_3978084) baseStart_3978084 baseEnd_3978084 := by
    simpa [prefixWord, tailWord_3978084, baseEnd_3978084] using wordTrace_append hprefix tailTrace_3978084
  have hstable : (prefixWord ++ tailWord_3978084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978084).length < 2 ^ (prefixWord ++ tailWord_3978084).sum := by decide
  have hdescent : baseEnd_3978084 < baseStart_3978084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978103 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 6, 5]
def baseStart_3978103 : Nat := 118140960795 + 3978103 * 2 ^ 59
def prefixEnd_3978103 : Nat := 4983230072969 + 3 ^ 40 * 3978103 * 2
def baseEnd_3978103 : Nat := 680892977364318129139181

theorem tailTrace_3978103 : CollatzResearch.WordTrace tailWord_3978103 prefixEnd_3978103 680892977364318129139181 := by
  unfold tailWord_3978103
  simp only [CollatzResearch.WordTrace]
  refine ⟨145093336307019711747242963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96728890871346474498161975 145093336307019711747242963)
  ·
    refine ⟨217640004460529567620864445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145093336307019711747242963 217640004460529567620864445)
    ·
      refine ⟨81615001672698587857824167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217640004460529567620864445 81615001672698587857824167)
      ·
        refine ⟨122422502509047881786736251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81615001672698587857824167 122422502509047881786736251)
        ·
          refine ⟨183633753763571822680104377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122422502509047881786736251 183633753763571822680104377)
          ·
            refine ⟨137725315322678867010078283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183633753763571822680104377 137725315322678867010078283)
            ·
              refine ⟨206587972984018300515117425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137725315322678867010078283 206587972984018300515117425)
              ·
                refine ⟨154940979738013725386338069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206587972984018300515117425 154940979738013725386338069)
                ·
                  refine ⟨7262858425219393377484597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154940979738013725386338069 7262858425219393377484597)
                  ·
                    refine ⟨680892977364318129139181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262858425219393377484597 680892977364318129139181)
                    ·
                      rfl

theorem cell23_3978103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_3978103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978103 prefixEnd_3978103 := by exact prefixLift 3978103
  have htrace : WordTrace (prefixWord ++ tailWord_3978103) baseStart_3978103 baseEnd_3978103 := by
    simpa [prefixWord, tailWord_3978103, baseEnd_3978103] using wordTrace_append hprefix tailTrace_3978103
  have hstable : (prefixWord ++ tailWord_3978103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978103).length < 2 ^ (prefixWord ++ tailWord_3978103).sum := by decide
  have hdescent : baseEnd_3978103 < baseStart_3978103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978120 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_3978120 : Nat := 118140960795 + 3978120 * 2 ^ 59
def prefixEnd_3978120 : Nat := 4983230072969 + 3 ^ 40 * 3978120 * 2
def baseEnd_3978120 : Nat := 680895887088026940301655

theorem tailTrace_3978120 : CollatzResearch.WordTrace tailWord_3978120 prefixEnd_3978120 680895887088026940301655 := by
  unfold tailWord_3978120
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546978173979061825305907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96729304231972082433741209 72546978173979061825305907)
  ·
    refine ⟨108820467260968592737958861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72546978173979061825305907 108820467260968592737958861)
    ·
      refine ⟨40807675222863222276734573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108820467260968592737958861 40807675222863222276734573)
      ·
        refine ⟨15302878208573708353775465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40807675222863222276734573 15302878208573708353775465)
        ·
          refine ⟨11477158656430281265331599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15302878208573708353775465 11477158656430281265331599)
          ·
            refine ⟨17215737984645421897997399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477158656430281265331599 17215737984645421897997399)
            ·
              refine ⟨25823606976968132846996099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17215737984645421897997399 25823606976968132846996099)
              ·
                refine ⟨38735410465452199270494149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25823606976968132846996099 38735410465452199270494149)
                ·
                  refine ⟨7262889462272287363217653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38735410465452199270494149 7262889462272287363217653)
                  ·
                    refine ⟨680895887088026940301655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262889462272287363217653 680895887088026940301655)
                    ·
                      rfl

theorem cell23_3978120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_3978120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978120 prefixEnd_3978120 := by exact prefixLift 3978120
  have htrace : WordTrace (prefixWord ++ tailWord_3978120) baseStart_3978120 baseEnd_3978120 := by
    simpa [prefixWord, tailWord_3978120, baseEnd_3978120] using wordTrace_append hprefix tailTrace_3978120
  have hstable : (prefixWord ++ tailWord_3978120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978120).length < 2 ^ (prefixWord ++ tailWord_3978120).sum := by decide
  have hdescent : baseEnd_3978120 < baseStart_3978120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978163 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 8]
def baseStart_3978163 : Nat := 118140960795 + 3978163 * 2 ^ 59
def prefixEnd_3978163 : Nat := 4983230072969 + 3 ^ 40 * 3978163 * 2
def baseEnd_3978163 : Nat := 226967748992469350296363

theorem tailTrace_3978163 : CollatzResearch.WordTrace tailWord_3978163 prefixEnd_3978163 226967748992469350296363 := by
  unfold tailWord_3978163
  simp only [CollatzResearch.WordTrace]
  refine ⟨145095524686802341994427143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96730349791201561329618095 145095524686802341994427143)
  ·
    refine ⟨217643287030203512991640715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145095524686802341994427143 217643287030203512991640715)
    ·
      refine ⟨326464930545305269487461073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217643287030203512991640715 326464930545305269487461073)
      ·
        refine ⟨244848697908978952115595805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326464930545305269487461073 244848697908978952115595805)
        ·
          refine ⟨91818261715867107043348427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244848697908978952115595805 91818261715867107043348427)
          ·
            refine ⟨137727392573800660565022641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91818261715867107043348427 137727392573800660565022641)
            ·
              refine ⟨103295544430350495423766981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137727392573800660565022641 103295544430350495423766981)
              ·
                refine ⟨19367914580690717891956309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103295544430350495423766981 19367914580690717891956309)
                ·
                  refine ⟨226967748992469350296363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19367914580690717891956309 226967748992469350296363)
                  ·
                    rfl

theorem cell23_3978163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 8].length) (baseStart_3978163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978163 prefixEnd_3978163 := by exact prefixLift 3978163
  have htrace : WordTrace (prefixWord ++ tailWord_3978163) baseStart_3978163 baseEnd_3978163 := by
    simpa [prefixWord, tailWord_3978163, baseEnd_3978163] using wordTrace_append hprefix tailTrace_3978163
  have hstable : (prefixWord ++ tailWord_3978163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978163).length < 2 ^ (prefixWord ++ tailWord_3978163).sum := by decide
  have hdescent : baseEnd_3978163 < baseStart_3978163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978241 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3978241 : Nat := 118140960795 + 3978241 * 2 ^ 59
def prefixEnd_3978241 : Nat := 4983230072969 + 3 ^ 40 * 3978241 * 2
def baseEnd_3978241 : Nat := 2042749792423274847491909

theorem tailTrace_3978241 : CollatzResearch.WordTrace tailWord_3978241 prefixEnd_3978241 2042749792423274847491909 := by
  unfold tailWord_3978241
  simp only [CollatzResearch.WordTrace]
  refine ⟨145098369580519761315766577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96732246387013174210511051 145098369580519761315766577)
  ·
    refine ⟨108823777185389820986824933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145098369580519761315766577 108823777185389820986824933)
    ·
      refine ⟨20404458222260591435029675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108823777185389820986824933 20404458222260591435029675)
      ·
        refine ⟨30606687333390887152544513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20404458222260591435029675 30606687333390887152544513)
        ·
          refine ⟨22955015500043165364408385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30606687333390887152544513 22955015500043165364408385)
          ·
            refine ⟨17216261625032374023306289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22955015500043165364408385 17216261625032374023306289)
            ·
              refine ⟨12912196218774280517479717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17216261625032374023306289 12912196218774280517479717)
              ·
                refine ⟨2421036791020177597027447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12912196218774280517479717 2421036791020177597027447)
                ·
                  refine ⟨3631555186530266395541171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421036791020177597027447 3631555186530266395541171)
                  ·
                    refine ⟨5447332779795399593311757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631555186530266395541171 5447332779795399593311757)
                    ·
                      refine ⟨2042749792423274847491909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5447332779795399593311757 2042749792423274847491909)
                      ·
                        rfl

theorem cell23_3978241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3978241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978241 prefixEnd_3978241 := by exact prefixLift 3978241
  have htrace : WordTrace (prefixWord ++ tailWord_3978241) baseStart_3978241 baseEnd_3978241 := by
    simpa [prefixWord, tailWord_3978241, baseEnd_3978241] using wordTrace_append hprefix tailTrace_3978241
  have hstable : (prefixWord ++ tailWord_3978241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978241).length < 2 ^ (prefixWord ++ tailWord_3978241).sum := by decide
  have hdescent : baseEnd_3978241 < baseStart_3978241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978257 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_3978257 : Nat := 118140960795 + 3978257 * 2 ^ 59
def prefixEnd_3978257 : Nat := 4983230072969 + 3 ^ 40 * 3978257 * 2
def baseEnd_3978257 : Nat := 680919336037915594963945

theorem tailTrace_3978257 : CollatzResearch.WordTrace tailWord_3978257 prefixEnd_3978257 680919336037915594963945 := by
  unfold tailWord_3978257
  simp only [CollatzResearch.WordTrace]
  refine ⟨145098953148461796048349025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96732635432307864032232683 145098953148461796048349025)
  ·
    refine ⟨108824214861346347036261769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145098953148461796048349025 108824214861346347036261769)
    ·
      refine ⟨81618161146009760277196327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108824214861346347036261769 81618161146009760277196327)
      ·
        refine ⟨122427241719014640415794491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81618161146009760277196327 122427241719014640415794491)
        ·
          refine ⟨183640862578521960623691737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122427241719014640415794491 183640862578521960623691737)
          ·
            refine ⟨137730646933891470467768803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183640862578521960623691737 137730646933891470467768803)
            ·
              refine ⟨206595970400837205701653205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137730646933891470467768803 206595970400837205701653205)
              ·
                refine ⟨4842093056269622008632497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206595970400837205701653205 4842093056269622008632497)
                ·
                  refine ⟨3631569792202216506474373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842093056269622008632497 3631569792202216506474373)
                  ·
                    refine ⟨680919336037915594963945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3631569792202216506474373 680919336037915594963945)
                    ·
                      rfl

theorem cell23_3978257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_3978257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978257 prefixEnd_3978257 := by exact prefixLift 3978257
  have htrace : WordTrace (prefixWord ++ tailWord_3978257) baseStart_3978257 baseEnd_3978257 := by
    simpa [prefixWord, tailWord_3978257, baseEnd_3978257] using wordTrace_append hprefix tailTrace_3978257
  have hstable : (prefixWord ++ tailWord_3978257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978257).length < 2 ^ (prefixWord ++ tailWord_3978257).sum := by decide
  have hdescent : baseEnd_3978257 < baseStart_3978257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978264 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3978264 : Nat := 118140960795 + 3978264 * 2 ^ 59
def prefixEnd_3978264 : Nat := 4983230072969 + 3 ^ 40 * 3978264 * 2
def baseEnd_3978264 : Nat := 2042761602478328257504303

theorem tailTrace_3978264 : CollatzResearch.WordTrace tailWord_3978264 prefixEnd_3978264 2042761602478328257504303 := by
  unfold tailWord_3978264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72549604229718218121926923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96732805639624290829235897 72549604229718218121926923)
  ·
    refine ⟨108824406344577327182890385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72549604229718218121926923 108824406344577327182890385)
    ·
      refine ⟨81618304758432995387167789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108824406344577327182890385 81618304758432995387167789)
      ·
        refine ⟨30606864284412373270187921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81618304758432995387167789 30606864284412373270187921)
        ·
          refine ⟨22955148213309279952640941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30606864284412373270187921 22955148213309279952640941)
          ·
            refine ⟨8608180579990979982240353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22955148213309279952640941 8608180579990979982240353)
            ·
              refine ⟨6456135434993234986680265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608180579990979982240353 6456135434993234986680265)
              ·
                refine ⟨4842101576244926240010199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456135434993234986680265 4842101576244926240010199)
                ·
                  refine ⟨7263152364367389360015299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842101576244926240010199 7263152364367389360015299)
                  ·
                    refine ⟨10894728546551084040022949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263152364367389360015299 10894728546551084040022949)
                    ·
                      refine ⟨2042761602478328257504303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10894728546551084040022949 2042761602478328257504303)
                      ·
                        rfl

theorem cell23_3978264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3978264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978264 prefixEnd_3978264 := by exact prefixLift 3978264
  have htrace : WordTrace (prefixWord ++ tailWord_3978264) baseStart_3978264 baseEnd_3978264 := by
    simpa [prefixWord, tailWord_3978264, baseEnd_3978264] using wordTrace_append hprefix tailTrace_3978264
  have hstable : (prefixWord ++ tailWord_3978264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978264).length < 2 ^ (prefixWord ++ tailWord_3978264).sum := by decide
  have hdescent : baseEnd_3978264 < baseStart_3978264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978330 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_3978330 : Nat := 118140960795 + 3978330 * 2 ^ 59
def prefixEnd_3978330 : Nat := 4983230072969 + 3 ^ 40 * 3978330 * 2
def baseEnd_3978330 : Nat := 680931830733841666426333

theorem tailTrace_3978330 : CollatzResearch.WordTrace tailWord_3978330 prefixEnd_3978330 680931830733841666426333 := by
  unfold tailWord_3978330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275403919299332378939111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96734410451464886343837629 36275403919299332378939111)
  ·
    refine ⟨54413105878948998568408667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36275403919299332378939111 54413105878948998568408667)
    ·
      refine ⟨81619658818423497852613001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54413105878948998568408667 81619658818423497852613001)
      ·
        refine ⟨61214744113817623389459751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81619658818423497852613001 61214744113817623389459751)
        ·
          refine ⟨91822116170726435084189627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61214744113817623389459751 91822116170726435084189627)
          ·
            refine ⟨137733174256089652626284441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91822116170726435084189627 137733174256089652626284441)
            ·
              refine ⟨103299880692067239469713331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137733174256089652626284441 103299880692067239469713331)
              ·
                refine ⟨154949821038100859204569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103299880692067239469713331 154949821038100859204569997)
                ·
                  refine ⟨58106182889287822201713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154949821038100859204569997 58106182889287822201713749)
                  ·
                    refine ⟨680931830733841666426333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58106182889287822201713749 680931830733841666426333)
                    ·
                      rfl

theorem cell23_3978330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_3978330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978330 prefixEnd_3978330 := by exact prefixLift 3978330
  have htrace : WordTrace (prefixWord ++ tailWord_3978330) baseStart_3978330 baseEnd_3978330 := by
    simpa [prefixWord, tailWord_3978330, baseEnd_3978330] using wordTrace_append hprefix tailTrace_3978330
  have hstable : (prefixWord ++ tailWord_3978330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978330).length < 2 ^ (prefixWord ++ tailWord_3978330).sum := by decide
  have hdescent : baseEnd_3978330 < baseStart_3978330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978354 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_3978354 : Nat := 118140960795 + 3978354 * 2 ^ 59
def prefixEnd_3978354 : Nat := 4983230072969 + 3 ^ 40 * 3978354 * 2
def baseEnd_3978354 : Nat := 2042807815737232905378889

theorem tailTrace_3978354 : CollatzResearch.WordTrace tailWord_3978354 prefixEnd_3978354 2042807815737232905378889 := by
  unfold tailWord_3978354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275622757277595403657529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96734994019406921076420077 36275622757277595403657529)
  ·
    refine ⟨27206717067958196552743147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36275622757277595403657529 27206717067958196552743147)
    ·
      refine ⟨40810075601937294829114721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27206717067958196552743147 40810075601937294829114721)
      ·
        refine ⟨30607556701452971121836041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40810075601937294829114721 30607556701452971121836041)
        ·
          refine ⟨22955667526089728341377031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30607556701452971121836041 22955667526089728341377031)
          ·
            refine ⟨34433501289134592512065547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22955667526089728341377031 34433501289134592512065547)
            ·
              refine ⟨51650251933701888768098321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34433501289134592512065547 51650251933701888768098321)
              ·
                refine ⟨38737688950276416576073741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51650251933701888768098321 38737688950276416576073741)
                ·
                  refine ⟨14526633356353656216027653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38737688950276416576073741 14526633356353656216027653)
                  ·
                    refine ⟨2723743754316310540505185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14526633356353656216027653 2723743754316310540505185)
                    ·
                      refine ⟨2042807815737232905378889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723743754316310540505185 2042807815737232905378889)
                      ·
                        rfl

theorem cell23_3978354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_3978354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978354 prefixEnd_3978354 := by exact prefixLift 3978354
  have htrace : WordTrace (prefixWord ++ tailWord_3978354) baseStart_3978354 baseEnd_3978354 := by
    simpa [prefixWord, tailWord_3978354, baseEnd_3978354] using wordTrace_append hprefix tailTrace_3978354
  have hstable : (prefixWord ++ tailWord_3978354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978354).length < 2 ^ (prefixWord ++ tailWord_3978354).sum := by decide
  have hdescent : baseEnd_3978354 < baseStart_3978354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978371 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 2, 2, 2]
def baseStart_3978371 : Nat := 118140960795 + 3978371 * 2 ^ 59
def prefixEnd_3978371 : Nat := 4983230072969 + 3 ^ 40 * 3978371 * 2
def baseEnd_3978371 : Nat := 2042816544908359338866311

theorem tailTrace_3978371 : CollatzResearch.WordTrace tailWord_3978371 prefixEnd_3978371 2042816544908359338866311 := by
  unfold tailWord_3978371
  simp only [CollatzResearch.WordTrace]
  refine ⟨145103111070048793517998967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96735407380032529011999311 145103111070048793517998967)
  ·
    refine ⟨217654666605073190276998451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145103111070048793517998967 217654666605073190276998451)
    ·
      refine ⟨326481999907609785415497677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217654666605073190276998451 326481999907609785415497677)
      ·
        refine ⟨122430749965353669530811629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326481999907609785415497677 122430749965353669530811629)
        ·
          refine ⟨45911531237007626074054361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122430749965353669530811629 45911531237007626074054361)
          ·
            refine ⟨34433648427755719555540771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45911531237007626074054361 34433648427755719555540771)
            ·
              refine ⟨51650472641633579333311157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34433648427755719555540771 51650472641633579333311157)
              ·
                refine ⟨4842231810153148062497921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51650472641633579333311157 4842231810153148062497921)
                ·
                  refine ⟨3631673857614861046873441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842231810153148062497921 3631673857614861046873441)
                  ·
                    refine ⟨2723755393211145785155081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3631673857614861046873441 2723755393211145785155081)
                    ·
                      refine ⟨2042816544908359338866311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723755393211145785155081 2042816544908359338866311)
                      ·
                        rfl

theorem cell23_3978371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_3978371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978371 prefixEnd_3978371 := by exact prefixLift 3978371
  have htrace : WordTrace (prefixWord ++ tailWord_3978371) baseStart_3978371 baseEnd_3978371 := by
    simpa [prefixWord, tailWord_3978371, baseEnd_3978371] using wordTrace_append hprefix tailTrace_3978371
  have hstable : (prefixWord ++ tailWord_3978371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978371).length < 2 ^ (prefixWord ++ tailWord_3978371).sum := by decide
  have hdescent : baseEnd_3978371 < baseStart_3978371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978377 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 7]
def baseStart_3978377 : Nat := 118140960795 + 3978377 * 2 ^ 59
def prefixEnd_3978377 : Nat := 4983230072969 + 3 ^ 40 * 3978377 * 2
def baseEnd_3978377 : Nat := 226979958421365146154587

theorem tailTrace_3978377 : CollatzResearch.WordTrace tailWord_3978377 prefixEnd_3978377 226979958421365146154587 := by
  unfold tailWord_3978377
  simp only [CollatzResearch.WordTrace]
  refine ⟨145103329908027056542717385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96735553272018037695144923 145103329908027056542717385)
  ·
    refine ⟨108827497431020292407038039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145103329908027056542717385 108827497431020292407038039)
    ·
      refine ⟨163241246146530438610557059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108827497431020292407038039 163241246146530438610557059)
      ·
        refine ⟨244861869219795657915835589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163241246146530438610557059 244861869219795657915835589)
        ·
          refine ⟨45911600478711685859219173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244861869219795657915835589 45911600478711685859219173)
          ·
            refine ⟨8608425089758441098603595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45911600478711685859219173 8608425089758441098603595)
            ·
              refine ⟨12912637634637661647905393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608425089758441098603595 12912637634637661647905393)
              ·
                refine ⟨9684478225978246235929045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12912637634637661647905393 9684478225978246235929045)
                ·
                  refine ⟨226979958421365146154587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9684478225978246235929045 226979958421365146154587)
                  ·
                    rfl

theorem cell23_3978377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_3978377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978377 prefixEnd_3978377 := by exact prefixLift 3978377
  have htrace : WordTrace (prefixWord ++ tailWord_3978377) baseStart_3978377 baseEnd_3978377 := by
    simpa [prefixWord, tailWord_3978377, baseEnd_3978377] using wordTrace_append hprefix tailTrace_3978377
  have hstable : (prefixWord ++ tailWord_3978377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978377).length < 2 ^ (prefixWord ++ tailWord_3978377).sum := by decide
  have hdescent : baseEnd_3978377 < baseStart_3978377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978404 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3978404 : Nat := 118140960795 + 3978404 * 2 ^ 59
def prefixEnd_3978404 : Nat := 4983230072969 + 3 ^ 40 * 3978404 * 2
def baseEnd_3978404 : Nat := 2042833489769957709753659

theorem tailTrace_3978404 : CollatzResearch.WordTrace tailWord_3978404 prefixEnd_3978404 2042833489769957709753659 := by
  unfold tailWord_3978404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72552157339464620076975133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96736209785952826769300177 72552157339464620076975133)
  ·
    refine ⟨27207059002299232528865675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72552157339464620076975133 27207059002299232528865675)
    ·
      refine ⟨40810588503448848793298513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27207059002299232528865675 40810588503448848793298513)
      ·
        refine ⟨30607941377586636594973885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40810588503448848793298513 30607941377586636594973885)
        ·
          refine ⟨11477978016594988723115207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30607941377586636594973885 11477978016594988723115207)
          ·
            refine ⟨17216967024892483084672811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477978016594988723115207 17216967024892483084672811)
            ·
              refine ⟨25825450537338724627009217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216967024892483084672811 25825450537338724627009217)
              ·
                refine ⟨19369087903004043470256913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25825450537338724627009217 19369087903004043470256913)
                ·
                  refine ⟨14526815927253032602692685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19369087903004043470256913 14526815927253032602692685)
                  ·
                    refine ⟨5447555972719887226009757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14526815927253032602692685 5447555972719887226009757)
                    ·
                      refine ⟨2042833489769957709753659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5447555972719887226009757 2042833489769957709753659)
                      ·
                        rfl

theorem cell23_3978404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3978404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978404 prefixEnd_3978404 := by exact prefixLift 3978404
  have htrace : WordTrace (prefixWord ++ tailWord_3978404) baseStart_3978404 baseEnd_3978404 := by
    simpa [prefixWord, tailWord_3978404, baseEnd_3978404] using wordTrace_append hprefix tailTrace_3978404
  have hstable : (prefixWord ++ tailWord_3978404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978404).length < 2 ^ (prefixWord ++ tailWord_3978404).sum := by decide
  have hdescent : baseEnd_3978404 < baseStart_3978404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978422 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3978422 : Nat := 118140960795 + 3978422 * 2 ^ 59
def prefixEnd_3978422 : Nat := 4983230072969 + 3 ^ 40 * 3978422 * 2
def baseEnd_3978422 : Nat := 2042842732421738639328577

theorem tailTrace_3978422 : CollatzResearch.WordTrace tailWord_3978422 prefixEnd_3978422 2042842732421738639328577 := by
  unfold tailWord_3978422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069060699554001826756595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96736647461909352818737013 9069060699554001826756595)
  ·
    refine ⟨13603591049331002740134893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069060699554001826756595 13603591049331002740134893)
    ·
      refine ⟨5101346643499126027550585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13603591049331002740134893 5101346643499126027550585)
      ·
        refine ⟨3826009982624344520662939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5101346643499126027550585 3826009982624344520662939)
        ·
          refine ⟨5739014973936516780994409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826009982624344520662939 5739014973936516780994409)
          ·
            refine ⟨4304261230452387585745807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739014973936516780994409 4304261230452387585745807)
            ·
              refine ⟨6456391845678581378618711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304261230452387585745807 6456391845678581378618711)
              ·
                refine ⟨9684587768517872067928067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456391845678581378618711 9684587768517872067928067)
                ·
                  refine ⟨14526881652776808101892101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684587768517872067928067 14526881652776808101892101)
                  ·
                    refine ⟨2723790309895651519104769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14526881652776808101892101 2723790309895651519104769)
                    ·
                      refine ⟨2042842732421738639328577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723790309895651519104769 2042842732421738639328577)
                      ·
                        rfl

theorem cell23_3978422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3978422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978422 prefixEnd_3978422 := by exact prefixLift 3978422
  have htrace : WordTrace (prefixWord ++ tailWord_3978422) baseStart_3978422 baseEnd_3978422 := by
    simpa [prefixWord, tailWord_3978422, baseEnd_3978422] using wordTrace_append hprefix tailTrace_3978422
  have hstable : (prefixWord ++ tailWord_3978422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978422).length < 2 ^ (prefixWord ++ tailWord_3978422).sum := by decide
  have hdescent : baseEnd_3978422 < baseStart_3978422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978427 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4]
def baseStart_3978427 : Nat := 118140960795 + 3978427 * 2 ^ 59
def prefixEnd_3978427 : Nat := 4983230072969 + 3 ^ 40 * 3978427 * 2
def baseEnd_3978427 : Nat := 2042845299825011119766053

theorem tailTrace_3978427 : CollatzResearch.WordTrace tailWord_3978427 prefixEnd_3978427 2042845299825011119766053 := by
  unfold tailWord_3978427
  simp only [CollatzResearch.WordTrace]
  refine ⟨145105153557845915082037535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96736769038563943388025023 145105153557845915082037535)
  ·
    refine ⟨217657730336768872623056303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145105153557845915082037535 217657730336768872623056303)
    ·
      refine ⟨326486595505153308934584455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217657730336768872623056303 326486595505153308934584455)
      ·
        refine ⟨489729893257729963401876683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326486595505153308934584455 489729893257729963401876683)
        ·
          refine ⟨734594839886594945102815025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489729893257729963401876683 734594839886594945102815025)
          ·
            refine ⟨550946129914946208827111269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734594839886594945102815025 550946129914946208827111269)
            ·
              refine ⟨103302399359052414155083363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550946129914946208827111269 103302399359052414155083363)
              ·
                refine ⟨154953599038578621232625045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103302399359052414155083363 154953599038578621232625045)
                ·
                  refine ⟨7263449954933372870279299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154953599038578621232625045 7263449954933372870279299)
                  ·
                    refine ⟨10895174932400059305418949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263449954933372870279299 10895174932400059305418949)
                    ·
                      refine ⟨2042845299825011119766053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10895174932400059305418949 2042845299825011119766053)
                      ·
                        rfl

theorem cell23_3978427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_3978427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978427 prefixEnd_3978427 := by exact prefixLift 3978427
  have htrace : WordTrace (prefixWord ++ tailWord_3978427) baseStart_3978427 baseEnd_3978427 := by
    simpa [prefixWord, tailWord_3978427, baseEnd_3978427] using wordTrace_append hprefix tailTrace_3978427
  have hstable : (prefixWord ++ tailWord_3978427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978427).length < 2 ^ (prefixWord ++ tailWord_3978427).sum := by decide
  have hdescent : baseEnd_3978427 < baseStart_3978427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978464 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3978464 : Nat := 118140960795 + 3978464 * 2 ^ 59
def prefixEnd_3978464 : Nat := 4983230072969 + 3 ^ 40 * 3978464 * 2
def baseEnd_3978464 : Nat := 2042864298609227475003383

theorem tailTrace_3978464 : CollatzResearch.WordTrace tailWord_3978464 prefixEnd_3978464 2042864298609227475003383 := by
  unfold tailWord_3978464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72553251529355935200567223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96737668705807913600756297 72553251529355935200567223)
  ·
    refine ⟨108829877294033902800850835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72553251529355935200567223 108829877294033902800850835)
    ·
      refine ⟨163244815941050854201276253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108829877294033902800850835 163244815941050854201276253)
      ·
        refine ⟨61216805977894070325478595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163244815941050854201276253 61216805977894070325478595)
        ·
          refine ⟨91825208966841105488217893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61216805977894070325478595 91825208966841105488217893)
          ·
            refine ⟨17217226681282707279040855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91825208966841105488217893 17217226681282707279040855)
            ·
              refine ⟨25825840021924060918561283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17217226681282707279040855 25825840021924060918561283)
              ·
                refine ⟨38738760032886091377841925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25825840021924060918561283 38738760032886091377841925)
                ·
                  refine ⟨7263517506166142133345361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38738760032886091377841925 7263517506166142133345361)
                  ·
                    refine ⟨5447638129624606600009021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7263517506166142133345361 5447638129624606600009021)
                    ·
                      refine ⟨2042864298609227475003383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5447638129624606600009021 2042864298609227475003383)
                      ·
                        rfl

theorem cell23_3978464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3978464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978464 prefixEnd_3978464 := by exact prefixLift 3978464
  have htrace : WordTrace (prefixWord ++ tailWord_3978464) baseStart_3978464 baseEnd_3978464 := by
    simpa [prefixWord, tailWord_3978464, baseEnd_3978464] using wordTrace_append hprefix tailTrace_3978464
  have hstable : (prefixWord ++ tailWord_3978464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978464).length < 2 ^ (prefixWord ++ tailWord_3978464).sum := by decide
  have hdescent : baseEnd_3978464 < baseStart_3978464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978544 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_3978544 : Nat := 118140960795 + 3978544 * 2 ^ 59
def prefixEnd_3978544 : Nat := 4983230072969 + 3 ^ 40 * 3978544 * 2
def baseEnd_3978544 : Nat := 680968459020529054001005

theorem tailTrace_3978544 : CollatzResearch.WordTrace tailWord_3978544 prefixEnd_3978544 680968459020529054001005 := by
  unfold tailWord_3978544
  simp only [CollatzResearch.WordTrace]
  refine ⟨72554710449211022032023343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96739613932281362709364457 72554710449211022032023343)
  ·
    refine ⟨108832065673816533048035015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72554710449211022032023343 108832065673816533048035015)
    ·
      refine ⟨163248098510724799572052523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108832065673816533048035015 163248098510724799572052523)
      ·
        refine ⟨244872147766087199358078785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163248098510724799572052523 244872147766087199358078785)
        ·
          refine ⟨183654110824565399518559089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244872147766087199358078785 183654110824565399518559089)
          ·
            refine ⟨137740583118424049638919317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183654110824565399518559089 137740583118424049638919317)
            ·
              refine ⟨6456589833676127326824343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137740583118424049638919317 6456589833676127326824343)
              ·
                refine ⟨9684884750514190990236515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456589833676127326824343 9684884750514190990236515)
                ·
                  refine ⟨14527327125771286485354773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684884750514190990236515 14527327125771286485354773)
                  ·
                    refine ⟨680968459020529054001005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14527327125771286485354773 680968459020529054001005)
                    ·
                      rfl

theorem cell23_3978544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_3978544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978544 prefixEnd_3978544 := by exact prefixLift 3978544
  have htrace : WordTrace (prefixWord ++ tailWord_3978544) baseStart_3978544 baseEnd_3978544 := by
    simpa [prefixWord, tailWord_3978544, baseEnd_3978544] using wordTrace_append hprefix tailTrace_3978544
  have hstable : (prefixWord ++ tailWord_3978544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978544).length < 2 ^ (prefixWord ++ tailWord_3978544).sum := by decide
  have hdescent : baseEnd_3978544 < baseStart_3978544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978561 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3978561 : Nat := 118140960795 + 3978561 * 2 ^ 59
def prefixEnd_3978561 : Nat := 4983230072969 + 3 ^ 40 * 3978561 * 2
def baseEnd_3978561 : Nat := 680971368744237865163479

theorem tailTrace_3978561 : CollatzResearch.WordTrace tailWord_3978561 prefixEnd_3978561 680971368744237865163479 := by
  unfold tailWord_3978561
  simp only [CollatzResearch.WordTrace]
  refine ⟨145110040939360455967415537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96740027292906970644943691 145110040939360455967415537)
  ·
    refine ⟨108832530704520341975561653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145110040939360455967415537 108832530704520341975561653)
    ·
      refine ⟨10203049753548782060208905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108832530704520341975561653 10203049753548782060208905)
      ·
        refine ⟨7652287315161586545156679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203049753548782060208905 7652287315161586545156679)
        ·
          refine ⟨11478430972742379817735019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652287315161586545156679 11478430972742379817735019)
          ·
            refine ⟨17217646459113569726602529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11478430972742379817735019 17217646459113569726602529)
            ·
              refine ⟨12913234844335177294951897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17217646459113569726602529 12913234844335177294951897)
              ·
                refine ⟨9684926133251382971213923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12913234844335177294951897 9684926133251382971213923)
                ·
                  refine ⟨14527389199877074456820885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684926133251382971213923 14527389199877074456820885)
                  ·
                    refine ⟨680971368744237865163479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14527389199877074456820885 680971368744237865163479)
                    ·
                      rfl

theorem cell23_3978561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3978561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978561 prefixEnd_3978561 := by exact prefixLift 3978561
  have htrace : WordTrace (prefixWord ++ tailWord_3978561) baseStart_3978561 baseEnd_3978561 := by
    simpa [prefixWord, tailWord_3978561, baseEnd_3978561] using wordTrace_append hprefix tailTrace_3978561
  have hstable : (prefixWord ++ tailWord_3978561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978561).length < 2 ^ (prefixWord ++ tailWord_3978561).sum := by decide
  have hdescent : baseEnd_3978561 < baseStart_3978561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978585 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 1, 2, 2]
def baseStart_3978585 : Nat := 118140960795 + 3978585 * 2 ^ 59
def prefixEnd_3978585 : Nat := 4983230072969 + 3 ^ 40 * 3978585 * 2
def baseEnd_3978585 : Nat := 2042926429768421501590327

theorem tailTrace_3978585 : CollatzResearch.WordTrace tailWord_3978585 prefixEnd_3978585 2042926429768421501590327 := by
  unfold tailWord_3978585
  simp only [CollatzResearch.WordTrace]
  refine ⟨145110916291273508066289209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96740610860849005377526139 145110916291273508066289209)
  ·
    refine ⟨108833187218455131049716907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145110916291273508066289209 108833187218455131049716907)
    ·
      refine ⟨163249780827682696574575361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108833187218455131049716907 163249780827682696574575361)
      ·
        refine ⟨122437335620762022430931521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163249780827682696574575361 122437335620762022430931521)
        ·
          refine ⟨91828001715571516823198641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122437335620762022430931521 91828001715571516823198641)
          ·
            refine ⟨68871001286678637617398981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91828001715571516823198641 68871001286678637617398981)
            ·
              refine ⟨12913312741252244553262309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68871001286678637617398981 12913312741252244553262309)
              ·
                refine ⟨2421246138984795853736683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12913312741252244553262309 2421246138984795853736683)
                ·
                  refine ⟨3631869208477193780605025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421246138984795853736683 3631869208477193780605025)
                  ·
                    refine ⟨2723901906357895335453769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3631869208477193780605025 2723901906357895335453769)
                    ·
                      refine ⟨2042926429768421501590327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723901906357895335453769 2042926429768421501590327)
                      ·
                        rfl

theorem cell23_3978585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_3978585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978585 prefixEnd_3978585 := by exact prefixLift 3978585
  have htrace : WordTrace (prefixWord ++ tailWord_3978585) baseStart_3978585 baseEnd_3978585 := by
    simpa [prefixWord, tailWord_3978585, baseEnd_3978585] using wordTrace_append hprefix tailTrace_3978585
  have hstable : (prefixWord ++ tailWord_3978585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978585).length < 2 ^ (prefixWord ++ tailWord_3978585).sum := by decide
  have hdescent : baseEnd_3978585 < baseStart_3978585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978641 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_3978641 : Nat := 118140960795 + 3978641 * 2 ^ 59
def prefixEnd_3978641 : Nat := 4983230072969 + 3 ^ 40 * 3978641 * 2
def baseEnd_3978641 : Nat := 2042955184685073282490069

theorem tailTrace_3978641 : CollatzResearch.WordTrace tailWord_3978641 prefixEnd_3978641 2042955184685073282490069 := by
  unfold tailWord_3978641
  simp only [CollatzResearch.WordTrace]
  refine ⟨145112958779070629630327777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96741972519380419753551851 145112958779070629630327777)
  ·
    refine ⟨108834719084302972222745833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145112958779070629630327777 108834719084302972222745833)
    ·
      refine ⟨81626039313227229167059375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108834719084302972222745833 81626039313227229167059375)
      ·
        refine ⟨122439058969840843750589063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81626039313227229167059375 122439058969840843750589063)
        ·
          refine ⟨183658588454761265625883595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122439058969840843750589063 183658588454761265625883595)
          ·
            refine ⟨275487882682141898438825393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183658588454761265625883595 275487882682141898438825393)
            ·
              refine ⟨206615912011606423829119045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275487882682141898438825393 206615912011606423829119045)
              ·
                refine ⟨38740483502176204467959821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206615912011606423829119045 38740483502176204467959821)
                ·
                  refine ⟨14527681313316076675484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38740483502176204467959821 14527681313316076675484933)
                  ·
                    refine ⟨2723940246246764376653425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14527681313316076675484933 2723940246246764376653425)
                    ·
                      refine ⟨2042955184685073282490069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723940246246764376653425 2042955184685073282490069)
                      ·
                        rfl

theorem cell23_3978641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_3978641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978641 prefixEnd_3978641 := by exact prefixLift 3978641
  have htrace : WordTrace (prefixWord ++ tailWord_3978641) baseStart_3978641 baseEnd_3978641 := by
    simpa [prefixWord, tailWord_3978641, baseEnd_3978641] using wordTrace_append hprefix tailTrace_3978641
  have hstable : (prefixWord ++ tailWord_3978641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978641).length < 2 ^ (prefixWord ++ tailWord_3978641).sum := by decide
  have hdescent : baseEnd_3978641 < baseStart_3978641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978652 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3978652 : Nat := 118140960795 + 3978652 * 2 ^ 59
def prefixEnd_3978652 : Nat := 4983230072969 + 3 ^ 40 * 3978652 * 2
def baseEnd_3978652 : Nat := 2042960832972272739452519

theorem tailTrace_3978652 : CollatzResearch.WordTrace tailWord_3978652 prefixEnd_3978652 2042960832972272739452519 := by
  unfold tailWord_3978652
  simp only [CollatzResearch.WordTrace]
  refine ⟨72556679991015389254489105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96742239988020519005985473 72556679991015389254489105)
  ·
    refine ⟨54417509993261541940866829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72556679991015389254489105 54417509993261541940866829)
    ·
      refine ⟨20406566247473078227825061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54417509993261541940866829 20406566247473078227825061)
      ·
        refine ⟨3826231171401202167717199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20406566247473078227825061 3826231171401202167717199)
        ·
          refine ⟨5739346757101803251575799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826231171401202167717199 5739346757101803251575799)
          ·
            refine ⟨8609020135652704877363699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739346757101803251575799 8609020135652704877363699)
            ·
              refine ⟨12913530203479057316045549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609020135652704877363699 12913530203479057316045549)
              ·
                refine ⟨4842573826304646493517081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12913530203479057316045549 4842573826304646493517081)
                ·
                  refine ⟨3631930369728484870137811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842573826304646493517081 3631930369728484870137811)
                  ·
                    refine ⟨5447895554592727305206717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3631930369728484870137811 5447895554592727305206717)
                    ·
                      refine ⟨2042960832972272739452519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5447895554592727305206717 2042960832972272739452519)
                      ·
                        rfl

theorem cell23_3978652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3978652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978652 prefixEnd_3978652 := by exact prefixLift 3978652
  have htrace : WordTrace (prefixWord ++ tailWord_3978652) baseStart_3978652 baseEnd_3978652 := by
    simpa [prefixWord, tailWord_3978652, baseEnd_3978652] using wordTrace_append hprefix tailTrace_3978652
  have hstable : (prefixWord ++ tailWord_3978652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978652).length < 2 ^ (prefixWord ++ tailWord_3978652).sum := by decide
  have hdescent : baseEnd_3978652 < baseStart_3978652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3978674 : Nat := 118140960795 + 3978674 * 2 ^ 59
def prefixEnd_3978674 : Nat := 4983230072969 + 3 ^ 40 * 3978674 * 2
def baseEnd_3978674 : Nat := 2042972129546671653377417

theorem tailTrace_3978674 : CollatzResearch.WordTrace tailWord_3978674 prefixEnd_3978674 2042972129546671653377417 := by
  unfold tailWord_3978674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278540596987769066569769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96742774925300717510852717 36278540596987769066569769)
  ·
    refine ⟨27208905447740826799927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36278540596987769066569769 27208905447740826799927327)
    ·
      refine ⟨40813358171611240199890991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27208905447740826799927327 40813358171611240199890991)
      ·
        refine ⟨61220037257416860299836487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40813358171611240199890991 61220037257416860299836487)
        ·
          refine ⟨91830055886125290449754731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61220037257416860299836487 91830055886125290449754731)
          ·
            refine ⟨137745083829187935674632097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91830055886125290449754731 137745083829187935674632097)
            ·
              refine ⟨103308812871890951755974073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137745083829187935674632097 103308812871890951755974073)
              ·
                refine ⟨77481609653918213816980555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103308812871890951755974073 77481609653918213816980555)
                ·
                  refine ⟨116222414480877320725470833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77481609653918213816980555 116222414480877320725470833)
                  ·
                    refine ⟨87166810860657990544103125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116222414480877320725470833 87166810860657990544103125)
                    ·
                      refine ⟨2042972129546671653377417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87166810860657990544103125 2042972129546671653377417)
                      ·
                        rfl

theorem cell23_3978674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3978674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978674 prefixEnd_3978674 := by exact prefixLift 3978674
  have htrace : WordTrace (prefixWord ++ tailWord_3978674) baseStart_3978674 baseEnd_3978674 := by
    simpa [prefixWord, tailWord_3978674, baseEnd_3978674] using wordTrace_append hprefix tailTrace_3978674
  have hstable : (prefixWord ++ tailWord_3978674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978674).length < 2 ^ (prefixWord ++ tailWord_3978674).sum := by decide
  have hdescent : baseEnd_3978674 < baseStart_3978674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978692 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3978692 : Nat := 118140960795 + 3978692 * 2 ^ 59
def prefixEnd_3978692 : Nat := 4983230072969 + 3 ^ 40 * 3978692 * 2
def baseEnd_3978692 : Nat := 2042981372198452582952335

theorem tailTrace_3978692 : CollatzResearch.WordTrace tailWord_3978692 prefixEnd_3978692 2042981372198452582952335 := by
  unfold tailWord_3978692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72557409450942932670217165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96743212601257243560289553 72557409450942932670217165)
  ·
    refine ⟨27209028544103599751331437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72557409450942932670217165 27209028544103599751331437)
    ·
      refine ⟨10203385704038849906749289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27209028544103599751331437 10203385704038849906749289)
      ·
        refine ⟨7652539278029137430061967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203385704038849906749289 7652539278029137430061967)
        ·
          refine ⟨11478808917043706145092951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652539278029137430061967 11478808917043706145092951)
          ·
            refine ⟨17218213375565559217639427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11478808917043706145092951 17218213375565559217639427)
            ·
              refine ⟨25827320063348338826459141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17218213375565559217639427 25827320063348338826459141)
              ·
                refine ⟨4842622511877813529961089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25827320063348338826459141 4842622511877813529961089)
                ·
                  refine ⟨3631966883908360147470817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842622511877813529961089 3631966883908360147470817)
                  ·
                    refine ⟨2723975162931270110603113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3631966883908360147470817 2723975162931270110603113)
                    ·
                      refine ⟨2042981372198452582952335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2723975162931270110603113 2042981372198452582952335)
                      ·
                        rfl

theorem cell23_3978692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3978692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978692 prefixEnd_3978692 := by exact prefixLift 3978692
  have htrace : WordTrace (prefixWord ++ tailWord_3978692) baseStart_3978692 baseEnd_3978692 := by
    simpa [prefixWord, tailWord_3978692, baseEnd_3978692] using wordTrace_append hprefix tailTrace_3978692
  have hstable : (prefixWord ++ tailWord_3978692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978692).length < 2 ^ (prefixWord ++ tailWord_3978692).sum := by decide
  have hdescent : baseEnd_3978692 < baseStart_3978692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978698 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_3978698 : Nat := 118140960795 + 3978698 * 2 ^ 59
def prefixEnd_3978698 : Nat := 4983230072969 + 3 ^ 40 * 3978698 * 2
def baseEnd_3978698 : Nat := 226998272564708839941923

theorem tailTrace_3978698 : CollatzResearch.WordTrace tailWord_3978698 prefixEnd_3978698 226998272564708839941923 := by
  unfold tailWord_3978698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278759434966032091288187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96743358493242752243435165 36278759434966032091288187)
  ·
    refine ⟨54418139152449048136932281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36278759434966032091288187 54418139152449048136932281)
    ·
      refine ⟨40813604364336786102699211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54418139152449048136932281 40813604364336786102699211)
      ·
        refine ⟨61220406546505179154048817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40813604364336786102699211 61220406546505179154048817)
        ·
          refine ⟨45915304909878884365536613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61220406546505179154048817 45915304909878884365536613)
          ·
            refine ⟨8609119670602290818538115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45915304909878884365536613 8609119670602290818538115)
            ·
              refine ⟨12913679505903436227807173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609119670602290818538115 12913679505903436227807173)
              ·
                refine ⟨2421314907356894292713845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12913679505903436227807173 2421314907356894292713845)
                ·
                  refine ⟨226998272564708839941923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2421314907356894292713845 226998272564708839941923)
                  ·
                    rfl

theorem cell23_3978698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_3978698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978698 prefixEnd_3978698 := by exact prefixLift 3978698
  have htrace : WordTrace (prefixWord ++ tailWord_3978698) baseStart_3978698 baseEnd_3978698 := by
    simpa [prefixWord, tailWord_3978698, baseEnd_3978698] using wordTrace_append hprefix tailTrace_3978698
  have hstable : (prefixWord ++ tailWord_3978698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978698).length < 2 ^ (prefixWord ++ tailWord_3978698).sum := by decide
  have hdescent : baseEnd_3978698 < baseStart_3978698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978731 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4]
def baseStart_3978731 : Nat := 118140960795 + 3978731 * 2 ^ 59
def prefixEnd_3978731 : Nat := 4983230072969 + 3 ^ 40 * 3978731 * 2
def baseEnd_3978731 : Nat := 2043001397943977930364655

theorem tailTrace_3978731 : CollatzResearch.WordTrace tailWord_3978731 prefixEnd_3978731 2043001397943977930364655 := by
  unfold tailWord_3978731
  simp only [CollatzResearch.WordTrace]
  refine ⟨145116241348744575001104047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96744160899163050000736031 145116241348744575001104047)
  ·
    refine ⟨217674362023116862501656071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145116241348744575001104047 217674362023116862501656071)
    ·
      refine ⟨326511543034675293752484107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217674362023116862501656071 326511543034675293752484107)
      ·
        refine ⟨489767314552012940628726161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326511543034675293752484107 489767314552012940628726161)
        ·
          refine ⟨367325485914009705471544621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489767314552012940628726161 367325485914009705471544621)
          ·
            refine ⟨137747057217753639551829233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367325485914009705471544621 137747057217753639551829233)
            ·
              refine ⟨103310292913315229663871925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137747057217753639551829233 103310292913315229663871925)
              ·
                refine ⟨9685339960623302780987993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103310292913315229663871925 9685339960623302780987993)
                ·
                  refine ⟨7264004970467477085740995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9685339960623302780987993 7264004970467477085740995)
                  ·
                    refine ⟨10896007455701215628611493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264004970467477085740995 10896007455701215628611493)
                    ·
                      refine ⟨2043001397943977930364655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10896007455701215628611493 2043001397943977930364655)
                      ·
                        rfl

theorem cell23_3978731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_3978731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978731 prefixEnd_3978731 := by exact prefixLift 3978731
  have htrace : WordTrace (prefixWord ++ tailWord_3978731) baseStart_3978731 baseEnd_3978731 := by
    simpa [prefixWord, tailWord_3978731, baseEnd_3978731] using wordTrace_append hprefix tailTrace_3978731
  have hstable : (prefixWord ++ tailWord_3978731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978731).length < 2 ^ (prefixWord ++ tailWord_3978731).sum := by decide
  have hdescent : baseEnd_3978731 < baseStart_3978731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978748 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_3978748 : Nat := 118140960795 + 3978748 * 2 ^ 59
def prefixEnd_3978748 : Nat := 4983230072969 + 3 ^ 40 * 3978748 * 2
def baseEnd_3978748 : Nat := 2043010127115104363852077

theorem tailTrace_3978748 : CollatzResearch.WordTrace tailWord_3978748 prefixEnd_3978748 2043010127115104363852077 := by
  unfold tailWord_3978748
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558430694841493452236449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96744574259788657936315265 72558430694841493452236449)
  ·
    refine ⟨54418823021131120089177337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72558430694841493452236449 54418823021131120089177337)
    ·
      refine ⟨40814117265848340066883003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54418823021131120089177337 40814117265848340066883003)
      ·
        refine ⟨61221175898772510100324505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40814117265848340066883003 61221175898772510100324505)
        ·
          refine ⟨45915881924079382575243379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61221175898772510100324505 45915881924079382575243379)
          ·
            refine ⟨68873822886119073862865069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45915881924079382575243379 68873822886119073862865069)
            ·
              refine ⟨25827683582294652698574401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68873822886119073862865069 25827683582294652698574401)
              ·
                refine ⟨19370762686720989523930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25827683582294652698574401 19370762686720989523930801)
                ·
                  refine ⟨14528072015040742142948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19370762686720989523930801 14528072015040742142948101)
                  ·
                    refine ⟨2724013502820139151802769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14528072015040742142948101 2724013502820139151802769)
                    ·
                      refine ⟨2043010127115104363852077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724013502820139151802769 2043010127115104363852077)
                      ·
                        rfl

theorem cell23_3978748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_3978748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978748 prefixEnd_3978748 := by exact prefixLift 3978748
  have htrace : WordTrace (prefixWord ++ tailWord_3978748) baseStart_3978748 baseEnd_3978748 := by
    simpa [prefixWord, tailWord_3978748, baseEnd_3978748] using wordTrace_append hprefix tailTrace_3978748
  have hstable : (prefixWord ++ tailWord_3978748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978748).length < 2 ^ (prefixWord ++ tailWord_3978748).sum := by decide
  have hdescent : baseEnd_3978748 < baseStart_3978748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978801 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_3978801 : Nat := 118140960795 + 3978801 * 2 ^ 59
def prefixEnd_3978801 : Nat := 4983230072969 + 3 ^ 40 * 3978801 * 2
def baseEnd_3978801 : Nat := 681012447196597552163111

theorem tailTrace_3978801 : CollatzResearch.WordTrace tailWord_3978801 prefixEnd_3978801 681012447196597552163111 := by
  unfold tailWord_3978801
  simp only [CollatzResearch.WordTrace]
  refine ⟨145118794458490976956152257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96745862972327317970768171 145118794458490976956152257)
  ·
    refine ⟨108839095843868232717114193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145118794458490976956152257 108839095843868232717114193)
    ·
      refine ⟨81629321882901174537835645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108839095843868232717114193 81629321882901174537835645)
      ·
        refine ⟨30610995706087940451688367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81629321882901174537835645 30610995706087940451688367)
        ·
          refine ⟨45916493559131910677532551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30610995706087940451688367 45916493559131910677532551)
          ·
            refine ⟨68874740338697866016298827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45916493559131910677532551 68874740338697866016298827)
            ·
              refine ⟨103312110508046799024448241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68874740338697866016298827 103312110508046799024448241)
              ·
                refine ⟨77484082881035099268336181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103312110508046799024448241 77484082881035099268336181)
                ·
                  refine ⟨7264132770097040556406517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77484082881035099268336181 7264132770097040556406517)
                  ·
                    refine ⟨681012447196597552163111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7264132770097040556406517 681012447196597552163111)
                    ·
                      rfl

theorem cell23_3978801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_3978801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978801 prefixEnd_3978801 := by exact prefixLift 3978801
  have htrace : WordTrace (prefixWord ++ tailWord_3978801) baseStart_3978801 baseEnd_3978801 := by
    simpa [prefixWord, tailWord_3978801, baseEnd_3978801] using wordTrace_append hprefix tailTrace_3978801
  have hstable : (prefixWord ++ tailWord_3978801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978801).length < 2 ^ (prefixWord ++ tailWord_3978801).sum := by decide
  have hdescent : baseEnd_3978801 < baseStart_3978801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978815 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_3978815 : Nat := 118140960795 + 3978815 * 2 ^ 59
def prefixEnd_3978815 : Nat := 4983230072969 + 3 ^ 40 * 3978815 * 2
def baseEnd_3978815 : Nat := 2043044530318955601714269

theorem tailTrace_3978815 : CollatzResearch.WordTrace tailWord_3978815 prefixEnd_3978815 2043044530318955601714269 := by
  unfold tailWord_3978815
  simp only [CollatzResearch.WordTrace]
  refine ⟨145119305080440257347161899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96746203386960171564774599 145119305080440257347161899)
  ·
    refine ⟨217678957620660386020742849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145119305080440257347161899 217678957620660386020742849)
    ·
      refine ⟨163259218215495289515557137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217678957620660386020742849 163259218215495289515557137)
      ·
        refine ⟨122444413661621467136667853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163259218215495289515557137 122444413661621467136667853)
        ·
          refine ⟨45916655123108050176250445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122444413661621467136667853 45916655123108050176250445)
          ·
            refine ⟨17218745671165518816093917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45916655123108050176250445 17218745671165518816093917)
            ·
              refine ⟨6457029626687069556035219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17218745671165518816093917 6457029626687069556035219)
              ·
                refine ⟨9685544440030604334052829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457029626687069556035219 9685544440030604334052829)
                ·
                  refine ⟨3632079165011476625269811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9685544440030604334052829 3632079165011476625269811)
                  ·
                    refine ⟨5448118747517214937904717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3632079165011476625269811 5448118747517214937904717)
                    ·
                      refine ⟨2043044530318955601714269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5448118747517214937904717 2043044530318955601714269)
                      ·
                        rfl

theorem cell23_3978815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_3978815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978815 prefixEnd_3978815 := by exact prefixLift 3978815
  have htrace : WordTrace (prefixWord ++ tailWord_3978815) baseStart_3978815 baseEnd_3978815 := by
    simpa [prefixWord, tailWord_3978815, baseEnd_3978815] using wordTrace_append hprefix tailTrace_3978815
  have hstable : (prefixWord ++ tailWord_3978815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978815).length < 2 ^ (prefixWord ++ tailWord_3978815).sum := by decide
  have hdescent : baseEnd_3978815 < baseStart_3978815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978822 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3978822 : Nat := 118140960795 + 3978822 * 2 ^ 59
def prefixEnd_3978822 : Nat := 4983230072969 + 3 ^ 40 * 3978822 * 2
def baseEnd_3978822 : Nat := 227005347187059674925193

theorem tailTrace_3978822 : CollatzResearch.WordTrace tailWord_3978822 prefixEnd_3978822 227005347187059674925193 := by
  unfold tailWord_3978822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534986262231715548208335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96746373594276598361777813 4534986262231715548208335)
  ·
    refine ⟨6802479393347573322312503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534986262231715548208335 6802479393347573322312503)
    ·
      refine ⟨10203719090021359983468755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6802479393347573322312503 10203719090021359983468755)
      ·
        refine ⟨15305578635032039975203133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203719090021359983468755 15305578635032039975203133)
        ·
          refine ⟨5739591988137014990701175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15305578635032039975203133 5739591988137014990701175)
          ·
            refine ⟨8609387982205522486051763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739591988137014990701175 8609387982205522486051763)
            ·
              refine ⟨12914081973308283729077645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609387982205522486051763 12914081973308283729077645)
              ·
                refine ⟨4842780739990606398404117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12914081973308283729077645 4842780739990606398404117)
                ·
                  refine ⟨227005347187059674925193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4842780739990606398404117 227005347187059674925193)
                  ·
                    rfl

theorem cell23_3978822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3978822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978822 prefixEnd_3978822 := by exact prefixLift 3978822
  have htrace : WordTrace (prefixWord ++ tailWord_3978822) baseStart_3978822 baseEnd_3978822 := by
    simpa [prefixWord, tailWord_3978822, baseEnd_3978822] using wordTrace_append hprefix tailTrace_3978822
  have hstable : (prefixWord ++ tailWord_3978822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978822).length < 2 ^ (prefixWord ++ tailWord_3978822).sum := by decide
  have hdescent : baseEnd_3978822 < baseStart_3978822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978831 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 6]
def baseStart_3978831 : Nat := 118140960795 + 3978831 * 2 ^ 59
def prefixEnd_3978831 : Nat := 4983230072969 + 3 ^ 40 * 3978831 * 2
def baseEnd_3978831 : Nat := 681017582003142513038065

theorem tailTrace_3978831 : CollatzResearch.WordTrace tailWord_3978831 prefixEnd_3978831 681017582003142513038065 := by
  unfold tailWord_3978831
  simp only [CollatzResearch.WordTrace]
  refine ⟨145119888648382292079744347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96746592432254861386496231 145119888648382292079744347)
  ·
    refine ⟨217679832972573438119616521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145119888648382292079744347 217679832972573438119616521)
    ·
      refine ⟨163259874729430078589712391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217679832972573438119616521 163259874729430078589712391)
      ·
        refine ⟨244889812094145117884568587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163259874729430078589712391 244889812094145117884568587)
        ·
          refine ⟨367334718141217676826852881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244889812094145117884568587 367334718141217676826852881)
          ·
            refine ⟨275501038605913257620139661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367334718141217676826852881 275501038605913257620139661)
            ·
              refine ⟨103312889477217471607552373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275501038605913257620139661 103312889477217471607552373)
              ·
                refine ⟨9685583388489137963208035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103312889477217471607552373 9685583388489137963208035)
                ·
                  refine ⟨14528375082733706944812053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9685583388489137963208035 14528375082733706944812053)
                  ·
                    refine ⟨681017582003142513038065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14528375082733706944812053 681017582003142513038065)
                    ·
                      rfl

theorem cell23_3978831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_3978831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978831 prefixEnd_3978831 := by exact prefixLift 3978831
  have htrace : WordTrace (prefixWord ++ tailWord_3978831) baseStart_3978831 baseEnd_3978831 := by
    simpa [prefixWord, tailWord_3978831, baseEnd_3978831] using wordTrace_append hprefix tailTrace_3978831
  have hstable : (prefixWord ++ tailWord_3978831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978831).length < 2 ^ (prefixWord ++ tailWord_3978831).sum := by decide
  have hdescent : baseEnd_3978831 < baseStart_3978831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978841 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_3978841 : Nat := 118140960795 + 3978841 * 2 ^ 59
def prefixEnd_3978841 : Nat := 4983230072969 + 3 ^ 40 * 3978841 * 2
def baseEnd_3978841 : Nat := 2043057880815972499989149

theorem tailTrace_3978841 : CollatzResearch.WordTrace tailWord_3978841 prefixEnd_3978841 2043057880815972499989149 := by
  unfold tailWord_3978841
  simp only [CollatzResearch.WordTrace]
  refine ⟨145120253378346063787608377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96746835585564042525072251 145120253378346063787608377)
  ·
    refine ⟨108840190033759547840706283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145120253378346063787608377 108840190033759547840706283)
    ·
      refine ⟨163260285050639321761059425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108840190033759547840706283 163260285050639321761059425)
      ·
        refine ⟨122445213787979491320794569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163260285050639321761059425 122445213787979491320794569)
        ·
          refine ⟨91833910340984618490595927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122445213787979491320794569 91833910340984618490595927)
          ·
            refine ⟨137750865511476927735893891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91833910340984618490595927 137750865511476927735893891)
            ·
              refine ⟨206626298267215391603840837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137750865511476927735893891 206626298267215391603840837)
              ·
                refine ⟨38742430925102885925720157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206626298267215391603840837 38742430925102885925720157)
                ·
                  refine ⟨14528411596913582222145059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38742430925102885925720157 14528411596913582222145059)
                  ·
                    refine ⟨21792617395370373333217589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14528411596913582222145059 21792617395370373333217589)
                    ·
                      refine ⟨2043057880815972499989149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21792617395370373333217589 2043057880815972499989149)
                      ·
                        rfl

theorem cell23_3978841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_3978841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978841 prefixEnd_3978841 := by exact prefixLift 3978841
  have htrace : WordTrace (prefixWord ++ tailWord_3978841) baseStart_3978841 baseEnd_3978841 := by
    simpa [prefixWord, tailWord_3978841, baseEnd_3978841] using wordTrace_append hprefix tailTrace_3978841
  have hstable : (prefixWord ++ tailWord_3978841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978841).length < 2 ^ (prefixWord ++ tailWord_3978841).sum := by decide
  have hdescent : baseEnd_3978841 < baseStart_3978841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978861 : List Nat := [1, 5, 1, 1, 15]
def baseStart_3978861 : Nat := 118140960795 + 3978861 * 2 ^ 59
def prefixEnd_3978861 : Nat := 4983230072969 + 3 ^ 40 * 3978861 * 2
def baseEnd_3978861 : Nat := 2802562620615997835033

theorem tailTrace_3978861 : CollatzResearch.WordTrace tailWord_3978861 prefixEnd_3978861 2802562620615997835033 := by
  unfold tailWord_3978861
  simp only [CollatzResearch.WordTrace]
  refine ⟨145120982838273607203336437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96747321892182404802224291 145120982838273607203336437)
  ·
    refine ⟨13605092141088150675312791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145120982838273607203336437 13605092141088150675312791)
    ·
      refine ⟨20407638211632226012969187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13605092141088150675312791 20407638211632226012969187)
      ·
        refine ⟨30611457317448339019453781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20407638211632226012969187 30611457317448339019453781)
        ·
          refine ⟨2802562620615997835033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 30611457317448339019453781 2802562620615997835033)
          ·
            rfl

theorem cell23_3978861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 15].length) (baseStart_3978861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978861 prefixEnd_3978861 := by exact prefixLift 3978861
  have htrace : WordTrace (prefixWord ++ tailWord_3978861) baseStart_3978861 baseEnd_3978861 := by
    simpa [prefixWord, tailWord_3978861, baseEnd_3978861] using wordTrace_append hprefix tailTrace_3978861
  have hstable : (prefixWord ++ tailWord_3978861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978861).length < 2 ^ (prefixWord ++ tailWord_3978861).sum := by decide
  have hdescent : baseEnd_3978861 < baseStart_3978861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978866 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_3978866 : Nat := 118140960795 + 3978866 * 2 ^ 59
def prefixEnd_3978866 : Nat := 4983230072969 + 3 ^ 40 * 3978866 * 2
def baseEnd_3978866 : Nat := 2043070717832334902176535

theorem tailTrace_3978866 : CollatzResearch.WordTrace tailWord_3978866 prefixEnd_3978866 2043070717832334902176535 := by
  unfold tailWord_3978866
  simp only [CollatzResearch.WordTrace]
  refine ⟨36280291300813873264317113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96747443468836995371512301 36280291300813873264317113)
  ·
    refine ⟨27210218475610404948237835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36280291300813873264317113 27210218475610404948237835)
    ·
      refine ⟨40815327713415607422356753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27210218475610404948237835 40815327713415607422356753)
      ·
        refine ⟨30611495785061705566767565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40815327713415607422356753 30611495785061705566767565)
        ·
          refine ⟨11479310919398139587537837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30611495785061705566767565 11479310919398139587537837)
          ·
            refine ⟨4304741594774302345326689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11479310919398139587537837 4304741594774302345326689)
            ·
              refine ⟨3228556196080726758995017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304741594774302345326689 3228556196080726758995017)
              ·
                refine ⟨2421417147060545069246263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228556196080726758995017 2421417147060545069246263)
                ·
                  refine ⟨3632125720590817603869395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421417147060545069246263 3632125720590817603869395)
                  ·
                    refine ⟨5448188580886226405804093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3632125720590817603869395 5448188580886226405804093)
                    ·
                      refine ⟨2043070717832334902176535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5448188580886226405804093 2043070717832334902176535)
                      ·
                        rfl

theorem cell23_3978866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_3978866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978866 prefixEnd_3978866 := by exact prefixLift 3978866
  have htrace : WordTrace (prefixWord ++ tailWord_3978866) baseStart_3978866 baseEnd_3978866 := by
    simpa [prefixWord, tailWord_3978866, baseEnd_3978866] using wordTrace_append hprefix tailTrace_3978866
  have hstable : (prefixWord ++ tailWord_3978866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978866).length < 2 ^ (prefixWord ++ tailWord_3978866).sum := by decide
  have hdescent : baseEnd_3978866 < baseStart_3978866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978891 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 7]
def baseStart_3978891 : Nat := 118140960795 + 3978891 * 2 ^ 59
def prefixEnd_3978891 : Nat := 4983230072969 + 3 ^ 40 * 3978891 * 2
def baseEnd_3978891 : Nat := 681027851616232434787973

theorem tailTrace_3978891 : CollatzResearch.WordTrace tailWord_3978891 prefixEnd_3978891 681027851616232434787973 := by
  unfold tailWord_3978891
  simp only [CollatzResearch.WordTrace]
  refine ⟨145122077028164922326928527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96748051352109948217952351 145122077028164922326928527)
  ·
    refine ⟨217683115542247383490392791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145122077028164922326928527 217683115542247383490392791)
    ·
      refine ⟨326524673313371075235589187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217683115542247383490392791 326524673313371075235589187)
      ·
        refine ⟨489787009970056612853383781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326524673313371075235589187 489787009970056612853383781)
        ·
          refine ⟨91835064369385614910009459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489787009970056612853383781 91835064369385614910009459)
          ·
            refine ⟨137752596554078422365014189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91835064369385614910009459 137752596554078422365014189)
            ·
              refine ⟨51657223707779408386880321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137752596554078422365014189 51657223707779408386880321)
              ·
                refine ⟨38742917780834556290160241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51657223707779408386880321 38742917780834556290160241)
                ·
                  refine ⟨29057188335625917217620181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38742917780834556290160241 29057188335625917217620181)
                  ·
                    refine ⟨681027851616232434787973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29057188335625917217620181 681027851616232434787973)
                    ·
                      rfl

theorem cell23_3978891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_3978891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978891 prefixEnd_3978891 := by exact prefixLift 3978891
  have htrace : WordTrace (prefixWord ++ tailWord_3978891) baseStart_3978891 baseEnd_3978891 := by
    simpa [prefixWord, tailWord_3978891, baseEnd_3978891] using wordTrace_append hprefix tailTrace_3978891
  have hstable : (prefixWord ++ tailWord_3978891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978891).length < 2 ^ (prefixWord ++ tailWord_3978891).sum := by decide
  have hdescent : baseEnd_3978891 < baseStart_3978891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978938 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_3978938 : Nat := 118140960795 + 3978938 * 2 ^ 59
def prefixEnd_3978938 : Nat := 4983230072969 + 3 ^ 40 * 3978938 * 2
def baseEnd_3978938 : Nat := 681035896146486206825401

theorem tailTrace_3978938 : CollatzResearch.WordTrace tailWord_3978938 prefixEnd_3978938 681035896146486206825401 := by
  unfold tailWord_3978938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36280947814748662338472367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96749194172663099569259645 36280947814748662338472367)
  ·
    refine ⟨54421421722122993507708551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36280947814748662338472367 54421421722122993507708551)
    ·
      refine ⟨81632132583184490261562827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54421421722122993507708551 81632132583184490261562827)
      ·
        refine ⟨122448198874776735392344241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81632132583184490261562827 122448198874776735392344241)
        ·
          refine ⟨91836149156082551544258181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122448198874776735392344241 91836149156082551544258181)
          ·
            refine ⟨17219277966765478414548409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91836149156082551544258181 17219277966765478414548409)
            ·
              refine ⟨12914458475074108810911307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17219277966765478414548409 12914458475074108810911307)
              ·
                refine ⟨19371687712611163216366961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914458475074108810911307 19371687712611163216366961)
                ·
                  refine ⟨14528765784458372412275221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19371687712611163216366961 14528765784458372412275221)
                  ·
                    refine ⟨681035896146486206825401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14528765784458372412275221 681035896146486206825401)
                    ·
                      rfl

theorem cell23_3978938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_3978938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978938 prefixEnd_3978938 := by exact prefixLift 3978938
  have htrace : WordTrace (prefixWord ++ tailWord_3978938) baseStart_3978938 baseEnd_3978938 := by
    simpa [prefixWord, tailWord_3978938, baseEnd_3978938] using wordTrace_append hprefix tailTrace_3978938
  have hstable : (prefixWord ++ tailWord_3978938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978938).length < 2 ^ (prefixWord ++ tailWord_3978938).sum := by decide
  have hdescent : baseEnd_3978938 < baseStart_3978938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978946 : List Nat := [3, 5, 1, 2, 1, 2, 2, 7]
def baseStart_3978946 : Nat := 118140960795 + 3978946 * 2 ^ 59
def prefixEnd_3978946 : Nat := 4983230072969 + 3 ^ 40 * 3978946 * 2
def baseEnd_3978946 : Nat := 75670807269803503302821

theorem tailTrace_3978946 : CollatzResearch.WordTrace tailWord_3978946 prefixEnd_3978946 75670807269803503302821 := by
  unfold tailWord_3978946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281020760741416680045173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96749388695310444480120461 36281020760741416680045173)
  ·
    refine ⟨3401345696319507813754235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36281020760741416680045173 3401345696319507813754235)
    ·
      refine ⟨5102018544479261720631353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3401345696319507813754235 5102018544479261720631353)
      ·
        refine ⟨3826513908359446290473515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102018544479261720631353 3826513908359446290473515)
        ·
          refine ⟨5739770862539169435710273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826513908359446290473515 5739770862539169435710273)
          ·
            refine ⟨4304828146904377076782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739770862539169435710273 4304828146904377076782705)
            ·
              refine ⟨3228621110178282807587029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304828146904377076782705 3228621110178282807587029)
              ·
                refine ⟨75670807269803503302821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3228621110178282807587029 75670807269803503302821)
                ·
                  rfl

theorem cell23_3978946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_3978946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3978946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3978946 prefixEnd_3978946 := by exact prefixLift 3978946
  have htrace : WordTrace (prefixWord ++ tailWord_3978946) baseStart_3978946 baseEnd_3978946 := by
    simpa [prefixWord, tailWord_3978946, baseEnd_3978946] using wordTrace_append hprefix tailTrace_3978946
  have hstable : (prefixWord ++ tailWord_3978946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978946).length < 2 ^ (prefixWord ++ tailWord_3978946).sum := by decide
  have hdescent : baseEnd_3978946 < baseStart_3978946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979005 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_3979005 : Nat := 118140960795 + 3979005 * 2 ^ 59
def prefixEnd_3979005 : Nat := 4983230072969 + 3 ^ 40 * 3979005 * 2
def baseEnd_3979005 : Nat := 2043142091643309858338395

theorem tailTrace_3979005 : CollatzResearch.WordTrace tailWord_3979005 prefixEnd_3979005 2043142091643309858338395 := by
  unfold tailWord_3979005
  simp only [CollatzResearch.WordTrace]
  refine ⟨145126234949751919796578469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96750823299834613197718979 145126234949751919796578469)
  ·
    refine ⟨27211169053078484961858463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145126234949751919796578469 27211169053078484961858463)
    ·
      refine ⟨40816753579617727442787695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211169053078484961858463 40816753579617727442787695)
      ·
        refine ⟨61225130369426591164181543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40816753579617727442787695 61225130369426591164181543)
        ·
          refine ⟨91837695554139886746272315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61225130369426591164181543 91837695554139886746272315)
          ·
            refine ⟨137756543331209830119408473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91837695554139886746272315 137756543331209830119408473)
            ·
              refine ⟨103317407498407372589556355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137756543331209830119408473 103317407498407372589556355)
              ·
                refine ⟨154976111247611058884334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103317407498407372589556355 154976111247611058884334533)
                ·
                  refine ⟨29058020858927073540812725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154976111247611058884334533 29058020858927073540812725)
                  ·
                    refine ⟨2724189455524413144451193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29058020858927073540812725 2724189455524413144451193)
                    ·
                      refine ⟨2043142091643309858338395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724189455524413144451193 2043142091643309858338395)
                      ·
                        rfl

theorem cell23_3979005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_3979005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979005 prefixEnd_3979005 := by exact prefixLift 3979005
  have htrace : WordTrace (prefixWord ++ tailWord_3979005) baseStart_3979005 baseEnd_3979005 := by
    simpa [prefixWord, tailWord_3979005, baseEnd_3979005] using wordTrace_append hprefix tailTrace_3979005
  have hstable : (prefixWord ++ tailWord_3979005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979005).length < 2 ^ (prefixWord ++ tailWord_3979005).sum := by decide
  have hdescent : baseEnd_3979005 < baseStart_3979005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 4, 2]
def baseStart_3979035 : Nat := 118140960795 + 3979035 * 2 ^ 59
def prefixEnd_3979035 : Nat := 4983230072969 + 3 ^ 40 * 3979035 * 2
def baseEnd_3979035 : Nat := 2043157496062944740963257

theorem tailTrace_3979035 : CollatzResearch.WordTrace tailWord_3979035 prefixEnd_3979035 2043157496062944740963257 := by
  unfold tailWord_3979035
  simp only [CollatzResearch.WordTrace]
  refine ⟨145127329139643234920170559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96751552759762156613447039 145127329139643234920170559)
  ·
    refine ⟨217690993709464852380255839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145127329139643234920170559 217690993709464852380255839)
    ·
      refine ⟨326536490564197278570383759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217690993709464852380255839 326536490564197278570383759)
      ·
        refine ⟨489804735846295917855575639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326536490564197278570383759 489804735846295917855575639)
        ·
          refine ⟨734707103769443876783363459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489804735846295917855575639 734707103769443876783363459)
          ·
            refine ⟨1102060655654165815175045189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734707103769443876783363459 1102060655654165815175045189)
            ·
              refine ⟨206636372935156090345320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1102060655654165815175045189 206636372935156090345320973)
              ·
                refine ⟨77488639850683533879495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206636372935156090345320973 77488639850683533879495365)
                ·
                  refine ⟨14529119972003162602405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77488639850683533879495365 14529119972003162602405381)
                  ·
                    refine ⟨2724209994750592987951009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14529119972003162602405381 2724209994750592987951009)
                    ·
                      refine ⟨2043157496062944740963257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724209994750592987951009 2043157496062944740963257)
                      ·
                        rfl

theorem cell23_3979035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4, 2].length) (baseStart_3979035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979035 prefixEnd_3979035 := by exact prefixLift 3979035
  have htrace : WordTrace (prefixWord ++ tailWord_3979035) baseStart_3979035 baseEnd_3979035 := by
    simpa [prefixWord, tailWord_3979035, baseEnd_3979035] using wordTrace_append hprefix tailTrace_3979035
  have hstable : (prefixWord ++ tailWord_3979035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979035).length < 2 ^ (prefixWord ++ tailWord_3979035).sum := by decide
  have hdescent : baseEnd_3979035 < baseStart_3979035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979052 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_3979052 : Nat := 118140960795 + 3979052 * 2 ^ 59
def prefixEnd_3979052 : Nat := 4983230072969 + 3 ^ 40 * 3979052 * 2
def baseEnd_3979052 : Nat := 2043166225234071174450679

theorem tailTrace_3979052 : CollatzResearch.WordTrace tailWord_3979052 prefixEnd_3979052 2043166225234071174450679 := by
  unfold tailWord_3979052
  simp only [CollatzResearch.WordTrace]
  refine ⟨72563974590290823411769705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96751966120387764549026273 72563974590290823411769705)
  ·
    refine ⟨54422980942718117558827279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72563974590290823411769705 54422980942718117558827279)
    ·
      refine ⟨81634471414077176338240919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54422980942718117558827279 81634471414077176338240919)
      ·
        refine ⟨122451707121115764507361379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81634471414077176338240919 122451707121115764507361379)
        ·
          refine ⟨183677560681673646761042069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122451707121115764507361379 183677560681673646761042069)
          ·
            refine ⟨8609885656953452191923847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183677560681673646761042069 8609885656953452191923847)
            ·
              refine ⟨12914828485430178287885771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609885656953452191923847 12914828485430178287885771)
              ·
                refine ⟨19372242728145267431828657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914828485430178287885771 19372242728145267431828657)
                ·
                  refine ⟨14529182046108950573871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19372242728145267431828657 14529182046108950573871493)
                  ·
                    refine ⟨2724221633645428232600905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14529182046108950573871493 2724221633645428232600905)
                    ·
                      refine ⟨2043166225234071174450679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724221633645428232600905 2043166225234071174450679)
                      ·
                        rfl

theorem cell23_3979052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_3979052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979052 prefixEnd_3979052 := by exact prefixLift 3979052
  have htrace : WordTrace (prefixWord ++ tailWord_3979052) baseStart_3979052 baseEnd_3979052 := by
    simpa [prefixWord, tailWord_3979052, baseEnd_3979052] using wordTrace_append hprefix tailTrace_3979052
  have hstable : (prefixWord ++ tailWord_3979052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979052).length < 2 ^ (prefixWord ++ tailWord_3979052).sum := by decide
  have hdescent : baseEnd_3979052 < baseStart_3979052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979069 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3979069 : Nat := 118140960795 + 3979069 * 2 ^ 59
def prefixEnd_3979069 : Nat := 4983230072969 + 3 ^ 40 * 3979069 * 2
def baseEnd_3979069 : Nat := 2043174954405197607938101

theorem tailTrace_3979069 : CollatzResearch.WordTrace tailWord_3979069 prefixEnd_3979069 2043174954405197607938101 := by
  unfold tailWord_3979069
  simp only [CollatzResearch.WordTrace]
  refine ⟨145128569221520058726908261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96752379481013372484605507 145128569221520058726908261)
  ·
    refine ⟨27211606729035011011295299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145128569221520058726908261 27211606729035011011295299)
    ·
      refine ⟨40817410093552516516942949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211606729035011011295299 40817410093552516516942949)
      ·
        refine ⟨7653264392541096846926803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40817410093552516516942949 7653264392541096846926803)
        ·
          refine ⟨11479896588811645270390205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7653264392541096846926803 11479896588811645270390205)
          ·
            refine ⟨4304961220804366976396327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11479896588811645270390205 4304961220804366976396327)
            ·
              refine ⟨6457441831206550464594491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304961220804366976396327 6457441831206550464594491)
              ·
                refine ⟨9686162746809825696891737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457441831206550464594491 9686162746809825696891737)
                ·
                  refine ⟨7264622060107369272668803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686162746809825696891737 7264622060107369272668803)
                  ·
                    refine ⟨10896933090161053909003205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264622060107369272668803 10896933090161053909003205)
                    ·
                      refine ⟨2043174954405197607938101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10896933090161053909003205 2043174954405197607938101)
                      ·
                        rfl

theorem cell23_3979069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3979069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979069 prefixEnd_3979069 := by exact prefixLift 3979069
  have htrace : WordTrace (prefixWord ++ tailWord_3979069) baseStart_3979069 baseEnd_3979069 := by
    simpa [prefixWord, tailWord_3979069, baseEnd_3979069] using wordTrace_append hprefix tailTrace_3979069
  have hstable : (prefixWord ++ tailWord_3979069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979069).length < 2 ^ (prefixWord ++ tailWord_3979069).sum := by decide
  have hdescent : baseEnd_3979069 < baseStart_3979069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979092 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3979092 : Nat := 118140960795 + 3979092 * 2 ^ 59
def prefixEnd_3979092 : Nat := 4983230072969 + 3 ^ 40 * 3979092 * 2
def baseEnd_3979092 : Nat := 227020751606694557550055

theorem tailTrace_3979092 : CollatzResearch.WordTrace tailWord_3979092 prefixEnd_3979092 227020751606694557550055 := by
  unfold tailWord_3979092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72564704050218366827497765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96752938733624489103330353 72564704050218366827497765)
  ·
    refine ⟨13605882009415943780155831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72564704050218366827497765 13605882009415943780155831)
    ·
      refine ⟨20408823014123915670233747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13605882009415943780155831 20408823014123915670233747)
      ·
        refine ⟨30613234521185873505350621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20408823014123915670233747 30613234521185873505350621)
        ·
          refine ⟨11479962945444702564506483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30613234521185873505350621 11479962945444702564506483)
          ·
            refine ⟨17219944418167053846759725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479962945444702564506483 17219944418167053846759725)
            ·
              refine ⟨6457479156812645192534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17219944418167053846759725 6457479156812645192534897)
              ·
                refine ⟨4843109367609483894401173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457479156812645192534897 4843109367609483894401173)
                ·
                  refine ⟨227020751606694557550055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4843109367609483894401173 227020751606694557550055)
                  ·
                    rfl

theorem cell23_3979092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3979092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979092 prefixEnd_3979092 := by exact prefixLift 3979092
  have htrace : WordTrace (prefixWord ++ tailWord_3979092) baseStart_3979092 baseEnd_3979092 := by
    simpa [prefixWord, tailWord_3979092, baseEnd_3979092] using wordTrace_append hprefix tailTrace_3979092
  have hstable : (prefixWord ++ tailWord_3979092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979092).length < 2 ^ (prefixWord ++ tailWord_3979092).sum := by decide
  have hdescent : baseEnd_3979092 < baseStart_3979092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979112 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3979112 : Nat := 118140960795 + 3979112 * 2 ^ 59
def prefixEnd_3979112 : Nat := 4983230072969 + 3 ^ 40 * 3979112 * 2
def baseEnd_3979112 : Nat := 2043197034073340939700403

theorem tailTrace_3979112 : CollatzResearch.WordTrace tailWord_3979112 prefixEnd_3979112 2043197034073340939700403 := by
  unfold tailWord_3979112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72565068780182138535361795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96753425040242851380482393 72565068780182138535361795)
  ·
    refine ⟨108847603170273207803042693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72565068780182138535361795 108847603170273207803042693)
    ·
      refine ⟨20408925594426226463070505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108847603170273207803042693 20408925594426226463070505)
      ·
        refine ⟨15306694195819669847302879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20408925594426226463070505 15306694195819669847302879)
        ·
          refine ⟨22960041293729504770954319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306694195819669847302879 22960041293729504770954319)
          ·
            refine ⟨34440061940594257156431479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22960041293729504770954319 34440061940594257156431479)
            ·
              refine ⟨51660092910891385734647219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34440061940594257156431479 51660092910891385734647219)
              ·
                refine ⟨77490139366337078601970829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51660092910891385734647219 77490139366337078601970829)
                ·
                  refine ⟨29058802262376404475739061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77490139366337078601970829 29058802262376404475739061)
                  ·
                    refine ⟨2724262712097787919600537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29058802262376404475739061 2724262712097787919600537)
                    ·
                      refine ⟨2043197034073340939700403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724262712097787919600537 2043197034073340939700403)
                      ·
                        rfl

theorem cell23_3979112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3979112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979112 prefixEnd_3979112 := by exact prefixLift 3979112
  have htrace : WordTrace (prefixWord ++ tailWord_3979112) baseStart_3979112 baseEnd_3979112 := by
    simpa [prefixWord, tailWord_3979112, baseEnd_3979112] using wordTrace_append hprefix tailTrace_3979112
  have hstable : (prefixWord ++ tailWord_3979112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979112).length < 2 ^ (prefixWord ++ tailWord_3979112).sum := by decide
  have hdescent : baseEnd_3979112 < baseStart_3979112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979146 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3979146 : Nat := 118140960795 + 3979146 * 2 ^ 59
def prefixEnd_3979146 : Nat := 4983230072969 + 3 ^ 40 * 3979146 * 2
def baseEnd_3979146 : Nat := 2043214492415593806675247

theorem tailTrace_3979146 : CollatzResearch.WordTrace tailWord_3979146 prefixEnd_3979146 2043214492415593806675247 := by
  unfold tailWord_3979146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36282844410560275219365323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96754251761494067251640861 36282844410560275219365323)
  ·
    refine ⟨54424266615840412829047985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36282844410560275219365323 54424266615840412829047985)
    ·
      refine ⟨40818199961880309621785989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54424266615840412829047985 40818199961880309621785989)
      ·
        refine ⟨7653412492852558054084873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40818199961880309621785989 7653412492852558054084873)
        ·
          refine ⟨5740059369639418540563655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7653412492852558054084873 5740059369639418540563655)
          ·
            refine ⟨8610089054459127810845483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740059369639418540563655 8610089054459127810845483)
            ·
              refine ⟨12915133581688691716268225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610089054459127810845483 12915133581688691716268225)
              ·
                refine ⟨9686350186266518787201169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915133581688691716268225 9686350186266518787201169)
                ·
                  refine ⟨7264762639699889090400877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686350186266518787201169 7264762639699889090400877)
                  ·
                    refine ⟨2724285989887458408900329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7264762639699889090400877 2724285989887458408900329)
                    ·
                      refine ⟨2043214492415593806675247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724285989887458408900329 2043214492415593806675247)
                      ·
                        rfl

theorem cell23_3979146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3979146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979146 prefixEnd_3979146 := by exact prefixLift 3979146
  have htrace : WordTrace (prefixWord ++ tailWord_3979146) baseStart_3979146 baseEnd_3979146 := by
    simpa [prefixWord, tailWord_3979146, baseEnd_3979146] using wordTrace_append hprefix tailTrace_3979146
  have hstable : (prefixWord ++ tailWord_3979146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979146).length < 2 ^ (prefixWord ++ tailWord_3979146).sum := by decide
  have hdescent : baseEnd_3979146 < baseStart_3979146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979162 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3979162 : Nat := 118140960795 + 3979162 * 2 ^ 59
def prefixEnd_3979162 : Nat := 4983230072969 + 3 ^ 40 * 3979162 * 2
def baseEnd_3979162 : Nat := 2043222708106065744075173

theorem tailTrace_3979162 : CollatzResearch.WordTrace tailWord_3979162 prefixEnd_3979162 2043222708106065744075173 := by
  unfold tailWord_3979162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36282990302545783902510935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96754640806788757073362493 36282990302545783902510935)
  ·
    refine ⟨54424485453818675853766403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36282990302545783902510935 54424485453818675853766403)
    ·
      refine ⟨81636728180728013780649605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54424485453818675853766403 81636728180728013780649605)
      ·
        refine ⟨15306886533886502583871801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81636728180728013780649605 15306886533886502583871801)
        ·
          refine ⟨11480164900414876937903851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15306886533886502583871801 11480164900414876937903851)
          ·
            refine ⟨17220247350622315406855777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11480164900414876937903851 17220247350622315406855777)
            ·
              refine ⟨12915185512966736555141833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17220247350622315406855777 12915185512966736555141833)
              ·
                refine ⟨9686389134725052416356375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915185512966736555141833 9686389134725052416356375)
                ·
                  refine ⟨14529583702087578624534563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686389134725052416356375 14529583702087578624534563)
                  ·
                    refine ⟨21794375553131367936801845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14529583702087578624534563 21794375553131367936801845)
                    ·
                      refine ⟨2043222708106065744075173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21794375553131367936801845 2043222708106065744075173)
                      ·
                        rfl

theorem cell23_3979162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3979162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979162 prefixEnd_3979162 := by exact prefixLift 3979162
  have htrace : WordTrace (prefixWord ++ tailWord_3979162) baseStart_3979162 baseEnd_3979162 := by
    simpa [prefixWord, tailWord_3979162, baseEnd_3979162] using wordTrace_append hprefix tailTrace_3979162
  have hstable : (prefixWord ++ tailWord_3979162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979162).length < 2 ^ (prefixWord ++ tailWord_3979162).sum := by decide
  have hdescent : baseEnd_3979162 < baseStart_3979162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979165 : List Nat := [1, 4, 2, 1, 2, 2, 1, 10]
def baseStart_3979165 : Nat := 118140960795 + 3979165 * 2 ^ 59
def prefixEnd_3979165 : Nat := 4983230072969 + 3 ^ 40 * 3979165 * 2
def baseEnd_3979165 : Nat := 75674972168445527123617

theorem tailTrace_3979165 : CollatzResearch.WordTrace tailWord_3979165 prefixEnd_3979165 75674972168445527123617 := by
  unfold tailWord_3979165
  simp only [CollatzResearch.WordTrace]
  refine ⟨145132070629172267122402949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96754713752781511414935299 145132070629172267122402949)
  ·
    refine ⟨27212263242969800085450553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145132070629172267122402949 27212263242969800085450553)
    ·
      refine ⟨20409197432227350064087915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27212263242969800085450553 20409197432227350064087915)
      ·
        refine ⟨30613796148341025096131873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409197432227350064087915 30613796148341025096131873)
        ·
          refine ⟨22960347111255768822098905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30613796148341025096131873 22960347111255768822098905)
          ·
            refine ⟨17220260333441826616574179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22960347111255768822098905 17220260333441826616574179)
            ·
              refine ⟨25830390500162739924861269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17220260333441826616574179 25830390500162739924861269)
              ·
                refine ⟨75674972168445527123617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25830390500162739924861269 75674972168445527123617)
                ·
                  rfl

theorem cell23_3979165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 10].length) (baseStart_3979165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979165 prefixEnd_3979165 := by exact prefixLift 3979165
  have htrace : WordTrace (prefixWord ++ tailWord_3979165) baseStart_3979165 baseEnd_3979165 := by
    simpa [prefixWord, tailWord_3979165, baseEnd_3979165] using wordTrace_append hprefix tailTrace_3979165
  have hstable : (prefixWord ++ tailWord_3979165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979165).length < 2 ^ (prefixWord ++ tailWord_3979165).sum := by decide
  have hdescent : baseEnd_3979165 < baseStart_3979165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979176 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3979176 : Nat := 118140960795 + 3979176 * 2 ^ 59
def prefixEnd_3979176 : Nat := 4983230072969 + 3 ^ 40 * 3979176 * 2
def baseEnd_3979176 : Nat := 2043229896835228689300109

theorem tailTrace_3979176 : CollatzResearch.WordTrace tailWord_3979176 prefixEnd_3979176 2043229896835228689300109 := by
  unfold tailWord_3979176
  simp only [CollatzResearch.WordTrace]
  refine ⟨72566235916066208000526691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96754981221421610667368921 72566235916066208000526691)
  ·
    refine ⟨108849353874099312000790037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72566235916066208000526691 108849353874099312000790037)
    ·
      refine ⟨5102313462848405250037033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108849353874099312000790037 5102313462848405250037033)
      ·
        refine ⟨3826735097136303937527775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102313462848405250037033 3826735097136303937527775)
        ·
          refine ⟨5740102645704455906291663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826735097136303937527775 5740102645704455906291663)
          ·
            refine ⟨8610153968556683859437495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740102645704455906291663 8610153968556683859437495)
            ·
              refine ⟨12915230952835025789156243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610153968556683859437495 12915230952835025789156243)
              ·
                refine ⟨19372846429252538683734365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915230952835025789156243 19372846429252538683734365)
                ·
                  refine ⟨7264817410969702006400387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19372846429252538683734365 7264817410969702006400387)
                  ·
                    refine ⟨10897226116454553009600581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264817410969702006400387 10897226116454553009600581)
                    ·
                      refine ⟨2043229896835228689300109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10897226116454553009600581 2043229896835228689300109)
                      ·
                        rfl

theorem cell23_3979176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3979176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979176 prefixEnd_3979176 := by exact prefixLift 3979176
  have htrace : WordTrace (prefixWord ++ tailWord_3979176) baseStart_3979176 baseEnd_3979176 := by
    simpa [prefixWord, tailWord_3979176, baseEnd_3979176] using wordTrace_append hprefix tailTrace_3979176
  have hstable : (prefixWord ++ tailWord_3979176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979176).length < 2 ^ (prefixWord ++ tailWord_3979176).sum := by decide
  have hdescent : baseEnd_3979176 < baseStart_3979176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979192 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_3979192 : Nat := 118140960795 + 3979192 * 2 ^ 59
def prefixEnd_3979192 : Nat := 4983230072969 + 3 ^ 40 * 3979192 * 2
def baseEnd_3979192 : Nat := 2043238112525700626700035

theorem tailTrace_3979192 : CollatzResearch.WordTrace tailWord_3979192 prefixEnd_3979192 2043238112525700626700035 := by
  unfold tailWord_3979192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72566527700037225366817915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96755370266716300489090553 72566527700037225366817915)
  ·
    refine ⟨108849791550055838050226873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72566527700037225366817915 108849791550055838050226873)
    ·
      refine ⟨81637343662541878537670155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108849791550055838050226873 81637343662541878537670155)
      ·
        refine ⟨122456015493812817806505233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81637343662541878537670155 122456015493812817806505233)
        ·
          refine ⟨91842011620359613354878925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122456015493812817806505233 91842011620359613354878925)
          ·
            refine ⟨34440754357634855008079597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91842011620359613354878925 34440754357634855008079597)
            ·
              refine ⟨12915282884113070628029849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34440754357634855008079597 12915282884113070628029849)
              ·
                refine ⟨9686462163084802971022387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915282884113070628029849 9686462163084802971022387)
                ·
                  refine ⟨14529693244627204456533581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686462163084802971022387 14529693244627204456533581)
                  ·
                    refine ⟨5448634966735201671200093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14529693244627204456533581 5448634966735201671200093)
                    ·
                      refine ⟨2043238112525700626700035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5448634966735201671200093 2043238112525700626700035)
                      ·
                        rfl

theorem cell23_3979192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_3979192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979192 prefixEnd_3979192 := by exact prefixLift 3979192
  have htrace : WordTrace (prefixWord ++ tailWord_3979192) baseStart_3979192 baseEnd_3979192 := by
    simpa [prefixWord, tailWord_3979192, baseEnd_3979192] using wordTrace_append hprefix tailTrace_3979192
  have hstable : (prefixWord ++ tailWord_3979192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979192).length < 2 ^ (prefixWord ++ tailWord_3979192).sum := by decide
  have hdescent : baseEnd_3979192 < baseStart_3979192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979196 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3979196 : Nat := 118140960795 + 3979196 * 2 ^ 59
def prefixEnd_3979196 : Nat := 4983230072969 + 3 ^ 40 * 3979196 * 2
def baseEnd_3979196 : Nat := 2043240166448318611050017

theorem tailTrace_3979196 : CollatzResearch.WordTrace tailWord_3979196 prefixEnd_3979196 2043240166448318611050017 := by
  unfold tailWord_3979196
  simp only [CollatzResearch.WordTrace]
  refine ⟨72566600646029979708390721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96755467528039972944520961 72566600646029979708390721)
  ·
    refine ⟨54424950484522484781293041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72566600646029979708390721 54424950484522484781293041)
    ·
      refine ⟨40818712863391863585969781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54424950484522484781293041 40818712863391863585969781)
      ·
        refine ⟨3826754330942987211184667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40818712863391863585969781 3826754330942987211184667)
        ·
          refine ⟨5740131496414480816777001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826754330942987211184667 5740131496414480816777001)
          ·
            refine ⟨4305098622310860612582751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5740131496414480816777001 4305098622310860612582751)
            ·
              refine ⟨6457647933466290918874127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305098622310860612582751 6457647933466290918874127)
              ·
                refine ⟨9686471900199436378311191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457647933466290918874127 9686471900199436378311191)
                ·
                  refine ⟨14529707850299154567466787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686471900199436378311191 14529707850299154567466787)
                  ·
                    refine ⟨21794561775448731851200181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14529707850299154567466787 21794561775448731851200181)
                    ·
                      refine ⟨2043240166448318611050017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21794561775448731851200181 2043240166448318611050017)
                      ·
                        rfl

theorem cell23_3979196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3979196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979196 prefixEnd_3979196 := by exact prefixLift 3979196
  have htrace : WordTrace (prefixWord ++ tailWord_3979196) baseStart_3979196 baseEnd_3979196 := by
    simpa [prefixWord, tailWord_3979196, baseEnd_3979196] using wordTrace_append hprefix tailTrace_3979196
  have hstable : (prefixWord ++ tailWord_3979196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979196).length < 2 ^ (prefixWord ++ tailWord_3979196).sum := by decide
  have hdescent : baseEnd_3979196 < baseStart_3979196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979215 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_3979215 : Nat := 118140960795 + 3979215 * 2 ^ 59
def prefixEnd_3979215 : Nat := 4983230072969 + 3 ^ 40 * 3979215 * 2
def baseEnd_3979215 : Nat := 2043249922580754036712429

theorem tailTrace_3979215 : CollatzResearch.WordTrace tailWord_3979215 prefixEnd_3979215 2043249922580754036712429 := by
  unfold tailWord_3979215
  simp only [CollatzResearch.WordTrace]
  refine ⟨145133894278991125661723099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96755929519327417107815399 145133894278991125661723099)
  ·
    refine ⟨217700841418486688492584649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145133894278991125661723099 217700841418486688492584649)
    ·
      refine ⟨163275631063865016369438487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217700841418486688492584649 163275631063865016369438487)
      ·
        refine ⟨244913446595797524554157731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163275631063865016369438487 244913446595797524554157731)
        ·
          refine ⟨367370169893696286831236597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244913446595797524554157731 367370169893696286831236597)
          ·
            refine ⟨34440953427534026890428431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367370169893696286831236597 34440953427534026890428431)
            ·
              refine ⟨51661430141301040335642647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34440953427534026890428431 51661430141301040335642647)
              ·
                refine ⟨77492145211951560503463971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51661430141301040335642647 77492145211951560503463971)
                ·
                  refine ⟨116238217817927340755195957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77492145211951560503463971 116238217817927340755195957)
                  ·
                    refine ⟨10897332920430688195799621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116238217817927340755195957 10897332920430688195799621)
                    ·
                      refine ⟨2043249922580754036712429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10897332920430688195799621 2043249922580754036712429)
                      ·
                        rfl

theorem cell23_3979215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_3979215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979215 prefixEnd_3979215 := by exact prefixLift 3979215
  have htrace : WordTrace (prefixWord ++ tailWord_3979215) baseStart_3979215 baseEnd_3979215 := by
    simpa [prefixWord, tailWord_3979215, baseEnd_3979215] using wordTrace_append hprefix tailTrace_3979215
  have hstable : (prefixWord ++ tailWord_3979215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979215).length < 2 ^ (prefixWord ++ tailWord_3979215).sum := by decide
  have hdescent : baseEnd_3979215 < baseStart_3979215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979272 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 7]
def baseStart_3979272 : Nat := 118140960795 + 3979272 * 2 ^ 59
def prefixEnd_3979272 : Nat := 4983230072969 + 3 ^ 40 * 3979272 * 2
def baseEnd_3979272 : Nat := 227031021219784479299963

theorem tailTrace_3979272 : CollatzResearch.WordTrace tailWord_3979272 prefixEnd_3979272 227031021219784479299963 := by
  unfold tailWord_3979272
  simp only [CollatzResearch.WordTrace]
  refine ⟨72567986619892312198274035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96757315493189749597698713 72567986619892312198274035)
  ·
    refine ⟨108851979929838468297411053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72567986619892312198274035 108851979929838468297411053)
    ·
      refine ⟨40819492473689425611529145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108851979929838468297411053 40819492473689425611529145)
      ·
        refine ⟨30614619355267069208646859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40819492473689425611529145 30614619355267069208646859)
        ·
          refine ⟨45921929032900603812970289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30614619355267069208646859 45921929032900603812970289)
          ·
            refine ⟨34441446774675452859727717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45921929032900603812970289 34441446774675452859727717)
            ·
              refine ⟨6457771270251647411198947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34441446774675452859727717 6457771270251647411198947)
              ·
                refine ⟨9686656905377471116798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457771270251647411198947 9686656905377471116798421)
                ·
                  refine ⟨227031021219784479299963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9686656905377471116798421 227031021219784479299963)
                  ·
                    rfl

theorem cell23_3979272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_3979272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979272 prefixEnd_3979272 := by exact prefixLift 3979272
  have htrace : WordTrace (prefixWord ++ tailWord_3979272) baseStart_3979272 baseEnd_3979272 := by
    simpa [prefixWord, tailWord_3979272, baseEnd_3979272] using wordTrace_append hprefix tailTrace_3979272
  have hstable : (prefixWord ++ tailWord_3979272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979272).length < 2 ^ (prefixWord ++ tailWord_3979272).sum := by decide
  have hdescent : baseEnd_3979272 < baseStart_3979272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979277 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3979277 : Nat := 118140960795 + 3979277 * 2 ^ 59
def prefixEnd_3979277 : Nat := 4983230072969 + 3 ^ 40 * 3979277 * 2
def baseEnd_3979277 : Nat := 2043281758381332794137145

theorem tailTrace_3979277 : CollatzResearch.WordTrace tailWord_3979277 prefixEnd_3979277 2043281758381332794137145 := by
  unfold tailWord_3979277
  simp only [CollatzResearch.WordTrace]
  refine ⟨145136155604766510250480085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96757437069844340166986723 145136155604766510250480085)
  ·
    refine ⟨3401628646986715083995627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145136155604766510250480085 3401628646986715083995627)
    ·
      refine ⟨5102442970480072625993441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3401628646986715083995627 5102442970480072625993441)
      ·
        refine ⟨3826832227860054469495081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102442970480072625993441 3826832227860054469495081)
        ·
          refine ⟨2870124170895040852121311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826832227860054469495081 2870124170895040852121311)
          ·
            refine ⟨4305186256342561278181967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870124170895040852121311 4305186256342561278181967)
            ·
              refine ⟨6457779384513841917272951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305186256342561278181967 6457779384513841917272951)
              ·
                refine ⟨9686669076770762875909427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457779384513841917272951 9686669076770762875909427)
                ·
                  refine ⟨14530003615156144313864141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686669076770762875909427 14530003615156144313864141)
                  ·
                    refine ⟨5448751355683554117699053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14530003615156144313864141 5448751355683554117699053)
                    ·
                      refine ⟨2043281758381332794137145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5448751355683554117699053 2043281758381332794137145)
                      ·
                        rfl

theorem cell23_3979277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3979277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979277 prefixEnd_3979277 := by exact prefixLift 3979277
  have htrace : WordTrace (prefixWord ++ tailWord_3979277) baseStart_3979277 baseEnd_3979277 := by
    simpa [prefixWord, tailWord_3979277, baseEnd_3979277] using wordTrace_append hprefix tailTrace_3979277
  have hstable : (prefixWord ++ tailWord_3979277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979277).length < 2 ^ (prefixWord ++ tailWord_3979277).sum := by decide
  have hdescent : baseEnd_3979277 < baseStart_3979277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979305 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_3979305 : Nat := 118140960795 + 3979305 * 2 ^ 59
def prefixEnd_3979305 : Nat := 4983230072969 + 3 ^ 40 * 3979305 * 2
def baseEnd_3979305 : Nat := 2043296135839658684587015

theorem tailTrace_3979305 : CollatzResearch.WordTrace tailWord_3979305 prefixEnd_3979305 2043296135839658684587015 := by
  unfold tailWord_3979305
  simp only [CollatzResearch.WordTrace]
  refine ⟨145137176848665071032499369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96758117899110047354999579 145137176848665071032499369)
  ·
    refine ⟨108852882636498803274374527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145137176848665071032499369 108852882636498803274374527)
    ·
      refine ⟨163279323954748204911561791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108852882636498803274374527 163279323954748204911561791)
      ·
        refine ⟨244918985932122307367342687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163279323954748204911561791 244918985932122307367342687)
        ·
          refine ⟨367378478898183461051014031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244918985932122307367342687 367378478898183461051014031)
          ·
            refine ⟨551067718347275191576521047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367378478898183461051014031 551067718347275191576521047)
            ·
              refine ⟨826601577520912787364781571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551067718347275191576521047 826601577520912787364781571)
              ·
                refine ⟨1239902366281369181047172357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826601577520912787364781571 1239902366281369181047172357)
                ·
                  refine ⟨232481693677756721446344817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239902366281369181047172357 232481693677756721446344817)
                  ·
                    refine ⟨174361270258317541084758613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232481693677756721446344817 174361270258317541084758613)
                    ·
                      refine ⟨2043296135839658684587015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174361270258317541084758613 2043296135839658684587015)
                      ·
                        rfl

theorem cell23_3979305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_3979305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979305 prefixEnd_3979305 := by exact prefixLift 3979305
  have htrace : WordTrace (prefixWord ++ tailWord_3979305) baseStart_3979305 baseEnd_3979305 := by
    simpa [prefixWord, tailWord_3979305, baseEnd_3979305] using wordTrace_append hprefix tailTrace_3979305
  have hstable : (prefixWord ++ tailWord_3979305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979305).length < 2 ^ (prefixWord ++ tailWord_3979305).sum := by decide
  have hdescent : baseEnd_3979305 < baseStart_3979305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979306 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_3979306 : Nat := 118140960795 + 3979306 * 2 ^ 59
def prefixEnd_3979306 : Nat := 4983230072969 + 3 ^ 40 * 3979306 * 2
def baseEnd_3979306 : Nat := 227032961035590353408279

theorem tailTrace_3979306 : CollatzResearch.WordTrace tailWord_3979306 prefixEnd_3979306 227032961035590353408279 := by
  unfold tailWord_3979306
  simp only [CollatzResearch.WordTrace]
  refine ⟨36284303330415362050821443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96758142214440965468857181 36284303330415362050821443)
  ·
    refine ⟨54426454995623043076232165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36284303330415362050821443 54426454995623043076232165)
    ·
      refine ⟨10204960311679320576793531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54426454995623043076232165 10204960311679320576793531)
      ·
        refine ⟨15307440467518980865190297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204960311679320576793531 15307440467518980865190297)
        ·
          refine ⟨11480580350639235648892723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15307440467518980865190297 11480580350639235648892723)
          ·
            refine ⟨17220870525958853473339085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11480580350639235648892723 17220870525958853473339085)
            ·
              refine ⟨6457826447234570052502157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17220870525958853473339085 6457826447234570052502157)
              ·
                refine ⟨2421684917712963769688309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6457826447234570052502157 2421684917712963769688309)
                ·
                  refine ⟨227032961035590353408279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2421684917712963769688309 227032961035590353408279)
                  ·
                    rfl

theorem cell23_3979306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_3979306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979306 prefixEnd_3979306 := by exact prefixLift 3979306
  have htrace : WordTrace (prefixWord ++ tailWord_3979306) baseStart_3979306 baseEnd_3979306 := by
    simpa [prefixWord, tailWord_3979306, baseEnd_3979306] using wordTrace_append hprefix tailTrace_3979306
  have hstable : (prefixWord ++ tailWord_3979306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979306).length < 2 ^ (prefixWord ++ tailWord_3979306).sum := by decide
  have hdescent : baseEnd_3979306 < baseStart_3979306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979329 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3979329 : Nat := 118140960795 + 3979329 * 2 ^ 59
def prefixEnd_3979329 : Nat := 4983230072969 + 3 ^ 40 * 3979329 * 2
def baseEnd_3979329 : Nat := 2043308459375366590686905

theorem tailTrace_3979329 : CollatzResearch.WordTrace tailWord_3979329 prefixEnd_3979329 2043308459375366590686905 := by
  unfold tailWord_3979329
  simp only [CollatzResearch.WordTrace]
  refine ⟨145138052200578123131373041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96758701467052082087582027 145138052200578123131373041)
  ·
    refine ⟨108853539150433592348529781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145138052200578123131373041 108853539150433592348529781)
    ·
      refine ⟨10205019295353149282674667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108853539150433592348529781 10205019295353149282674667)
      ·
        refine ⟨15307528943029723924012001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205019295353149282674667 15307528943029723924012001)
        ·
          refine ⟨11480646707272292943009001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15307528943029723924012001 11480646707272292943009001)
          ·
            refine ⟨8610485030454219707256751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11480646707272292943009001 8610485030454219707256751)
            ·
              refine ⟨12915727545681329560885127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610485030454219707256751 12915727545681329560885127)
              ·
                refine ⟨19373591318521994341327691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915727545681329560885127 19373591318521994341327691)
                ·
                  refine ⟨29060386977782991511991537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19373591318521994341327691 29060386977782991511991537)
                  ·
                    refine ⟨21795290233337243633993653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29060386977782991511991537 21795290233337243633993653)
                    ·
                      refine ⟨2043308459375366590686905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21795290233337243633993653 2043308459375366590686905)
                      ·
                        rfl

theorem cell23_3979329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3979329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979329 prefixEnd_3979329 := by exact prefixLift 3979329
  have htrace : WordTrace (prefixWord ++ tailWord_3979329) baseStart_3979329 baseEnd_3979329 := by
    simpa [prefixWord, tailWord_3979329, baseEnd_3979329] using wordTrace_append hprefix tailTrace_3979329
  have hstable : (prefixWord ++ tailWord_3979329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979329).length < 2 ^ (prefixWord ++ tailWord_3979329).sum := by decide
  have hdescent : baseEnd_3979329 < baseStart_3979329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
