import V185TrunkScan23Chunk0422

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2501076 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2501076 : Nat := 118140960795 + 2501076 * 2 ^ 59
def prefixEnd_2501076 : Nat := 4983230072969 + 3 ^ 40 * 2501076 * 2
def baseEnd_2501076 : Nat := 1284254141424561762347767

theorem tailTrace_2501076 : CollatzResearch.WordTrace tailWord_2501076 prefixEnd_2501076 1284254141424561762347767 := by
  unfold tailWord_2501076
  simp only [CollatzResearch.WordTrace]
  refine ⟨45610867943518138309389541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60814490591357517745852721 45610867943518138309389541)
  ·
    refine ⟨8552037739409650933010539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45610867943518138309389541 8552037739409650933010539)
    ·
      refine ⟨12828056609114476399515809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552037739409650933010539 12828056609114476399515809)
      ·
        refine ⟨9621042456835857299636857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828056609114476399515809 9621042456835857299636857)
        ·
          refine ⟨7215781842626892974727643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621042456835857299636857 7215781842626892974727643)
          ·
            refine ⟨10823672763940339462091465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215781842626892974727643 10823672763940339462091465)
            ·
              refine ⟨8117754572955254596568599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823672763940339462091465 8117754572955254596568599)
              ·
                refine ⟨12176631859432881894852899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117754572955254596568599 12176631859432881894852899)
                ·
                  refine ⟨18264947789149322842279349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12176631859432881894852899 18264947789149322842279349)
                  ·
                    refine ⟨1712338855232749016463689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18264947789149322842279349 1712338855232749016463689)
                    ·
                      refine ⟨1284254141424561762347767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712338855232749016463689 1284254141424561762347767)
                      ·
                        rfl

theorem cell23_2501076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2501076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501076 prefixEnd_2501076 := by exact prefixLift 2501076
  have htrace : WordTrace (prefixWord ++ tailWord_2501076) baseStart_2501076 baseEnd_2501076 := by
    simpa [prefixWord, tailWord_2501076, baseEnd_2501076] using wordTrace_append hprefix tailTrace_2501076
  have hstable : (prefixWord ++ tailWord_2501076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501076).length < 2 ^ (prefixWord ++ tailWord_2501076).sum := by decide
  have hdescent : baseEnd_2501076 < baseStart_2501076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501082 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_2501082 : Nat := 118140960795 + 2501082 * 2 ^ 59
def prefixEnd_2501082 : Nat := 4983230072969 + 3 ^ 40 * 2501082 * 2
def baseEnd_2501082 : Nat := 428085740769496246290913

theorem tailTrace_2501082 : CollatzResearch.WordTrace tailWord_2501082 prefixEnd_2501082 428085740769496246290913 := by
  unfold tailWord_2501082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22805488681253634910874375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60814636483343026428998333 22805488681253634910874375)
  ·
    refine ⟨34208233021880452366311563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22805488681253634910874375 34208233021880452366311563)
    ·
      refine ⟨51312349532820678549467345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34208233021880452366311563 51312349532820678549467345)
      ·
        refine ⟨38484262149615508912100509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51312349532820678549467345 38484262149615508912100509)
        ·
          refine ⟨14431598306105815842037691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38484262149615508912100509 14431598306105815842037691)
          ·
            refine ⟨21647397459158723763056537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431598306105815842037691 21647397459158723763056537)
            ·
              refine ⟨16235548094369042822292403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21647397459158723763056537 16235548094369042822292403)
              ·
                refine ⟨24353322141553564233438605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16235548094369042822292403 24353322141553564233438605)
                ·
                  refine ⟨9132495803082586587539477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24353322141553564233438605 9132495803082586587539477)
                  ·
                    refine ⟨428085740769496246290913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9132495803082586587539477 428085740769496246290913)
                    ·
                      rfl

theorem cell23_2501082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_2501082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501082 prefixEnd_2501082 := by exact prefixLift 2501082
  have htrace : WordTrace (prefixWord ++ tailWord_2501082) baseStart_2501082 baseEnd_2501082 := by
    simpa [prefixWord, tailWord_2501082, baseEnd_2501082] using wordTrace_append hprefix tailTrace_2501082
  have hstable : (prefixWord ++ tailWord_2501082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501082).length < 2 ^ (prefixWord ++ tailWord_2501082).sum := by decide
  have hdescent : baseEnd_2501082 < baseStart_2501082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501089 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_2501089 : Nat := 118140960795 + 2501089 * 2 ^ 59
def prefixEnd_2501089 : Nat := 4983230072969 + 3 ^ 40 * 2501089 * 2
def baseEnd_2501089 : Nat := 1284260816673070211485207

theorem tailTrace_2501089 : CollatzResearch.WordTrace tailWord_2501089 prefixEnd_2501089 1284260816673070211485207 := by
  unfold tailWord_2501089
  simp only [CollatzResearch.WordTrace]
  refine ⟨91222210035989179839002321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60814806690659453226001547 91222210035989179839002321)
  ·
    refine ⟨68416657526991884879251741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91222210035989179839002321 68416657526991884879251741)
    ·
      refine ⟨25656246572621956829719403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68416657526991884879251741 25656246572621956829719403)
      ·
        refine ⟨38484369858932935244579105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25656246572621956829719403 38484369858932935244579105)
        ·
          refine ⟨28863277394199701433434329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38484369858932935244579105 28863277394199701433434329)
          ·
            refine ⟨21647458045649776075075747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28863277394199701433434329 21647458045649776075075747)
            ·
              refine ⟨32471187068474664112613621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21647458045649776075075747 32471187068474664112613621)
              ·
                refine ⟨3044173787669499760557527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32471187068474664112613621 3044173787669499760557527)
                ·
                  refine ⟨4566260681504249640836291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044173787669499760557527 4566260681504249640836291)
                  ·
                    refine ⟨6849391022256374461254437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566260681504249640836291 6849391022256374461254437)
                    ·
                      refine ⟨1284260816673070211485207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6849391022256374461254437 1284260816673070211485207)
                      ·
                        rfl

theorem cell23_2501089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_2501089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501089 prefixEnd_2501089 := by exact prefixLift 2501089
  have htrace : WordTrace (prefixWord ++ tailWord_2501089) baseStart_2501089 baseEnd_2501089 := by
    simpa [prefixWord, tailWord_2501089, baseEnd_2501089] using wordTrace_append hprefix tailTrace_2501089
  have hstable : (prefixWord ++ tailWord_2501089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501089).length < 2 ^ (prefixWord ++ tailWord_2501089).sum := by decide
  have hdescent : baseEnd_2501089 < baseStart_2501089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501093 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2501093 : Nat := 118140960795 + 2501093 * 2 ^ 59
def prefixEnd_2501093 : Nat := 4983230072969 + 3 ^ 40 * 2501093 * 2
def baseEnd_2501093 : Nat := 1284262870595688195835189

theorem tailTrace_2501093 : CollatzResearch.WordTrace tailWord_2501093 prefixEnd_2501093 1284262870595688195835189 := by
  unfold tailWord_2501093
  simp only [CollatzResearch.WordTrace]
  refine ⟨91222355927974688522147933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60814903951983125681431955 91222355927974688522147933)
  ·
    refine ⟨34208383472990508195805475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91222355927974688522147933 34208383472990508195805475)
    ·
      refine ⟨51312575209485762293708213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34208383472990508195805475 51312575209485762293708213)
      ·
        refine ⟨4810553925889290215035145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51312575209485762293708213 4810553925889290215035145)
        ·
          refine ⟨3607915444416967661276359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4810553925889290215035145 3607915444416967661276359)
          ·
            refine ⟨5411873166625451491914539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607915444416967661276359 5411873166625451491914539)
            ·
              refine ⟨8117809749938177237871809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411873166625451491914539 8117809749938177237871809)
              ·
                refine ⟨6088357312453632928403857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117809749938177237871809 6088357312453632928403857)
                ·
                  refine ⟨4566267984340224696302893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088357312453632928403857 4566267984340224696302893)
                  ·
                    refine ⟨1712350494127584261113585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4566267984340224696302893 1712350494127584261113585)
                    ·
                      refine ⟨1284262870595688195835189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712350494127584261113585 1284262870595688195835189)
                      ·
                        rfl

theorem cell23_2501093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2501093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501093 prefixEnd_2501093 := by exact prefixLift 2501093
  have htrace : WordTrace (prefixWord ++ tailWord_2501093) baseStart_2501093 baseEnd_2501093 := by
    simpa [prefixWord, tailWord_2501093, baseEnd_2501093] using wordTrace_append hprefix tailTrace_2501093
  have hstable : (prefixWord ++ tailWord_2501093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501093).length < 2 ^ (prefixWord ++ tailWord_2501093).sum := by decide
  have hdescent : baseEnd_2501093 < baseStart_2501093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501099 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 2, 4]
def baseStart_2501099 : Nat := 118140960795 + 2501099 * 2 ^ 59
def prefixEnd_2501099 : Nat := 4983230072969 + 3 ^ 40 * 2501099 * 2
def baseEnd_2501099 : Nat := 428088650493205057453387

theorem tailTrace_2501099 : CollatzResearch.WordTrace tailWord_2501099 prefixEnd_2501099 428088650493205057453387 := by
  unfold tailWord_2501099
  simp only [CollatzResearch.WordTrace]
  refine ⟨91222574765952951546866351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60815049843968634364577567 91222574765952951546866351)
  ·
    refine ⟨136833862148929427320299527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91222574765952951546866351 136833862148929427320299527)
    ·
      refine ⟨205250793223394140980449291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136833862148929427320299527 205250793223394140980449291)
      ·
        refine ⟨307876189835091211470673937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205250793223394140980449291 307876189835091211470673937)
        ·
          refine ⟨230907142376318408603005453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307876189835091211470673937 230907142376318408603005453)
          ·
            refine ⟨86590178391119403226127045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230907142376318408603005453 86590178391119403226127045)
            ·
              refine ⟨16235658448334888104898821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86590178391119403226127045 16235658448334888104898821)
              ·
                refine ⟨3044185959062791519668529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16235658448334888104898821 3044185959062791519668529)
                ·
                  refine ⟨2283139469297093639751397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044185959062791519668529 2283139469297093639751397)
                  ·
                    refine ⟨428088650493205057453387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283139469297093639751397 428088650493205057453387)
                    ·
                      rfl

theorem cell23_2501099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 4].length) (baseStart_2501099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501099 prefixEnd_2501099 := by exact prefixLift 2501099
  have htrace : WordTrace (prefixWord ++ tailWord_2501099) baseStart_2501099 baseEnd_2501099 := by
    simpa [prefixWord, tailWord_2501099, baseEnd_2501099] using wordTrace_append hprefix tailTrace_2501099
  have hstable : (prefixWord ++ tailWord_2501099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501099).length < 2 ^ (prefixWord ++ tailWord_2501099).sum := by decide
  have hdescent : baseEnd_2501099 < baseStart_2501099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501112 : List Nat := [2, 1, 2, 1, 1, 4, 4, 8]
def baseStart_2501112 : Nat := 118140960795 + 2501112 * 2 ^ 59
def prefixEnd_2501112 : Nat := 4983230072969 + 3 ^ 40 * 2501112 * 2
def baseEnd_2501112 : Nat := 47565652841782356351763

theorem tailTrace_2501112 : CollatzResearch.WordTrace tailWord_2501112 prefixEnd_2501112 47565652841782356351763 := by
  unfold tailWord_2501112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45611524457452927383544795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60815365943270569844726393 45611524457452927383544795)
  ·
    refine ⟨68417286686179391075317193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45611524457452927383544795 68417286686179391075317193)
    ·
      refine ⟨51312965014634543306487895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68417286686179391075317193 51312965014634543306487895)
      ·
        refine ⟨76969447521951814959731843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51312965014634543306487895 76969447521951814959731843)
        ·
          refine ⟨115454171282927722439597765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76969447521951814959731843 115454171282927722439597765)
          ·
            refine ⟨21647657115548947957424581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115454171282927722439597765 21647657115548947957424581)
            ·
              refine ⟨4058935709165427742017109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21647657115548947957424581 4058935709165427742017109)
              ·
                refine ⟨47565652841782356351763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4058935709165427742017109 47565652841782356351763)
                ·
                  rfl

theorem cell23_2501112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 8].length) (baseStart_2501112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501112 prefixEnd_2501112 := by exact prefixLift 2501112
  have htrace : WordTrace (prefixWord ++ tailWord_2501112) baseStart_2501112 baseEnd_2501112 := by
    simpa [prefixWord, tailWord_2501112, baseEnd_2501112] using wordTrace_append hprefix tailTrace_2501112
  have hstable : (prefixWord ++ tailWord_2501112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501112).length < 2 ^ (prefixWord ++ tailWord_2501112).sum := by decide
  have hdescent : baseEnd_2501112 < baseStart_2501112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501133 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2501133 : Nat := 118140960795 + 2501133 * 2 ^ 59
def prefixEnd_2501133 : Nat := 4983230072969 + 3 ^ 40 * 2501133 * 2
def baseEnd_2501133 : Nat := 428094469940622679778335

theorem tailTrace_2501133 : CollatzResearch.WordTrace tailWord_2501133 prefixEnd_2501133 428094469940622679778335 := by
  unfold tailWord_2501133
  simp only [CollatzResearch.WordTrace]
  refine ⟨91223814847829775353604053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60815876565219850235736035 91223814847829775353604053)
  ·
    refine ⟨2138058160496010359850095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91223814847829775353604053 2138058160496010359850095)
    ·
      refine ⟨3207087240744015539775143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138058160496010359850095 3207087240744015539775143)
      ·
        refine ⟨4810630861116023309662715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207087240744015539775143 4810630861116023309662715)
        ·
          refine ⟨7215946291674034964494073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810630861116023309662715 7215946291674034964494073)
          ·
            refine ⟨5411959718755526223370555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215946291674034964494073 5411959718755526223370555)
            ·
              refine ⟨8117939578133289335055833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411959718755526223370555 8117939578133289335055833)
              ·
                refine ⟨6088454683599967001291875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117939578133289335055833 6088454683599967001291875)
                ·
                  refine ⟨9132682025399950501937813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088454683599967001291875 9132682025399950501937813)
                  ·
                    refine ⟨428094469940622679778335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9132682025399950501937813 428094469940622679778335)
                    ·
                      rfl

theorem cell23_2501133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2501133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501133 prefixEnd_2501133 := by exact prefixLift 2501133
  have htrace : WordTrace (prefixWord ++ tailWord_2501133) baseStart_2501133 baseEnd_2501133 := by
    simpa [prefixWord, tailWord_2501133, baseEnd_2501133] using wordTrace_append hprefix tailTrace_2501133
  have hstable : (prefixWord ++ tailWord_2501133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501133).length < 2 ^ (prefixWord ++ tailWord_2501133).sum := by decide
  have hdescent : baseEnd_2501133 < baseStart_2501133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501139 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3]
def baseStart_2501139 : Nat := 118140960795 + 2501139 * 2 ^ 59
def prefixEnd_2501139 : Nat := 4983230072969 + 3 ^ 40 * 2501139 * 2
def baseEnd_2501139 : Nat := 1284286490705795015859977

theorem tailTrace_2501139 : CollatzResearch.WordTrace tailWord_2501139 prefixEnd_2501139 1284286490705795015859977 := by
  unfold tailWord_2501139
  simp only [CollatzResearch.WordTrace]
  refine ⟨91224033685808038378322471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60816022457205358918881647 91224033685808038378322471)
  ·
    refine ⟨136836050528712057567483707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91224033685808038378322471 136836050528712057567483707)
    ·
      refine ⟨205254075793068086351225561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136836050528712057567483707 205254075793068086351225561)
      ·
        refine ⟨153940556844801064763419171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205254075793068086351225561 153940556844801064763419171)
        ·
          refine ⟨230910835267201597145128757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153940556844801064763419171 230910835267201597145128757)
          ·
            refine ⟨21647890806300149732355821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230910835267201597145128757 21647890806300149732355821)
            ·
              refine ⟨8117959052362556149633433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21647890806300149732355821 8117959052362556149633433)
              ·
                refine ⟨6088469289271917112225075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117959052362556149633433 6088469289271917112225075)
                ·
                  refine ⟨9132703933907875668337613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088469289271917112225075 9132703933907875668337613)
                  ·
                    refine ⟨3424763975215453375626605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9132703933907875668337613 3424763975215453375626605)
                    ·
                      refine ⟨1284286490705795015859977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3424763975215453375626605 1284286490705795015859977)
                      ·
                        rfl

theorem cell23_2501139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_2501139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501139 prefixEnd_2501139 := by exact prefixLift 2501139
  have htrace : WordTrace (prefixWord ++ tailWord_2501139) baseStart_2501139 baseEnd_2501139 := by
    simpa [prefixWord, tailWord_2501139, baseEnd_2501139] using wordTrace_append hprefix tailTrace_2501139
  have hstable : (prefixWord ++ tailWord_2501139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501139).length < 2 ^ (prefixWord ++ tailWord_2501139).sum := by decide
  have hdescent : baseEnd_2501139 < baseStart_2501139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501140 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2501140 : Nat := 118140960795 + 2501140 * 2 ^ 59
def prefixEnd_2501140 : Nat := 4983230072969 + 3 ^ 40 * 2501140 * 2
def baseEnd_2501140 : Nat := 1284287004186449511947473

theorem tailTrace_2501140 : CollatzResearch.WordTrace tailWord_2501140 prefixEnd_2501140 1284287004186449511947473 := by
  unfold tailWord_2501140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45612035079402207774554437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60816046772536277032739249 45612035079402207774554437)
  ·
    refine ⟨8552256577387913957728957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45612035079402207774554437 8552256577387913957728957)
    ·
      refine ⟨3207096216520467734148359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8552256577387913957728957 3207096216520467734148359)
      ·
        refine ⟨4810644324780701601222539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207096216520467734148359 4810644324780701601222539)
        ·
          refine ⟨7215966487171052401833809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810644324780701601222539 7215966487171052401833809)
          ·
            refine ⟨5411974865378289301375357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215966487171052401833809 5411974865378289301375357)
            ·
              refine ⟨2029490574516858488015759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5411974865378289301375357 2029490574516858488015759)
              ·
                refine ⟨3044235861775287732023639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029490574516858488015759 3044235861775287732023639)
                ·
                  refine ⟨4566353792662931598035459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044235861775287732023639 4566353792662931598035459)
                  ·
                    refine ⟨6849530688994397397053189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566353792662931598035459 6849530688994397397053189)
                    ·
                      refine ⟨1284287004186449511947473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6849530688994397397053189 1284287004186449511947473)
                      ·
                        rfl

theorem cell23_2501140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2501140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501140 prefixEnd_2501140 := by exact prefixLift 2501140
  have htrace : WordTrace (prefixWord ++ tailWord_2501140) baseStart_2501140 baseEnd_2501140 := by
    simpa [prefixWord, tailWord_2501140, baseEnd_2501140] using wordTrace_append hprefix tailTrace_2501140
  have hstable : (prefixWord ++ tailWord_2501140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501140).length < 2 ^ (prefixWord ++ tailWord_2501140).sum := by decide
  have hdescent : baseEnd_2501140 < baseStart_2501140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501143 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2501143 : Nat := 118140960795 + 2501143 * 2 ^ 59
def prefixEnd_2501143 : Nat := 4983230072969 + 3 ^ 40 * 2501143 * 2
def baseEnd_2501143 : Nat := 1284288544628413000209959

theorem tailTrace_2501143 : CollatzResearch.WordTrace tailWord_2501143 prefixEnd_2501143 1284288544628413000209959 := by
  unfold tailWord_2501143
  simp only [CollatzResearch.WordTrace]
  refine ⟨91224179577793547061468083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60816119718529031374312055 91224179577793547061468083)
  ·
    refine ⟨136836269366690320592202125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91224179577793547061468083 136836269366690320592202125)
    ·
      refine ⟨51313601012508870222075797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136836269366690320592202125 51313601012508870222075797)
      ·
        refine ⟨2405325047461353291659803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51313601012508870222075797 2405325047461353291659803)
        ·
          refine ⟨3607987571192029937489705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405325047461353291659803 3607987571192029937489705)
          ·
            refine ⟨2705990678394022453117279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607987571192029937489705 2705990678394022453117279)
            ·
              refine ⟨4058986017591033679675919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705990678394022453117279 4058986017591033679675919)
              ·
                refine ⟨6088479026386550519513879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058986017591033679675919 6088479026386550519513879)
                ·
                  refine ⟨9132718539579825779270819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088479026386550519513879 9132718539579825779270819)
                  ·
                    refine ⟨13699077809369738668906229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9132718539579825779270819 13699077809369738668906229)
                    ·
                      refine ⟨1284288544628413000209959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13699077809369738668906229 1284288544628413000209959)
                      ·
                        rfl

theorem cell23_2501143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2501143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501143 prefixEnd_2501143 := by exact prefixLift 2501143
  have htrace : WordTrace (prefixWord ++ tailWord_2501143) baseStart_2501143 baseEnd_2501143 := by
    simpa [prefixWord, tailWord_2501143, baseEnd_2501143] using wordTrace_append hprefix tailTrace_2501143
  have hstable : (prefixWord ++ tailWord_2501143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501143).length < 2 ^ (prefixWord ++ tailWord_2501143).sum := by decide
  have hdescent : baseEnd_2501143 < baseStart_2501143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501196 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2501196 : Nat := 118140960795 + 2501196 * 2 ^ 59
def prefixEnd_2501196 : Nat := 4983230072969 + 3 ^ 40 * 2501196 * 2
def baseEnd_2501196 : Nat := 1284315759103101292847215

theorem tailTrace_2501196 : CollatzResearch.WordTrace tailWord_2501196 prefixEnd_2501196 1284315759103101292847215 := by
  unfold tailWord_2501196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45613056323300768556573721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60817408431067691408764961 45613056323300768556573721)
  ·
    refine ⟨34209792242475576417430291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45613056323300768556573721 34209792242475576417430291)
    ·
      refine ⟨51314688363713364626145437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34209792242475576417430291 51314688363713364626145437)
      ·
        refine ⟨19243008136392511734804539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51314688363713364626145437 19243008136392511734804539)
        ·
          refine ⟨28864512204588767602206809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19243008136392511734804539 28864512204588767602206809)
          ·
            refine ⟨21648384153441575701655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28864512204588767602206809 21648384153441575701655107)
            ·
              refine ⟨32472576230162363552482661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21648384153441575701655107 32472576230162363552482661)
              ·
                refine ⟨6088608043155443166090499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32472576230162363552482661 6088608043155443166090499)
                ·
                  refine ⟨9132912064733164749135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088608043155443166090499 9132912064733164749135749)
                  ·
                    refine ⟨1712421012137468390462953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9132912064733164749135749 1712421012137468390462953)
                    ·
                      refine ⟨1284315759103101292847215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712421012137468390462953 1284315759103101292847215)
                      ·
                        rfl

theorem cell23_2501196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2501196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501196 prefixEnd_2501196 := by exact prefixLift 2501196
  have htrace : WordTrace (prefixWord ++ tailWord_2501196) baseStart_2501196 baseEnd_2501196 := by
    simpa [prefixWord, tailWord_2501196, baseEnd_2501196] using wordTrace_append hprefix tailTrace_2501196
  have hstable : (prefixWord ++ tailWord_2501196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501196).length < 2 ^ (prefixWord ++ tailWord_2501196).sum := by decide
  have hdescent : baseEnd_2501196 < baseStart_2501196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501219 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 7]
def baseStart_2501219 : Nat := 118140960795 + 2501219 * 2 ^ 59
def prefixEnd_2501219 : Nat := 4983230072969 + 3 ^ 40 * 2501219 * 2
def baseEnd_2501219 : Nat := 142703063239794966984401

theorem tailTrace_2501219 : CollatzResearch.WordTrace tailWord_2501219 prefixEnd_2501219 142703063239794966984401 := by
  unfold tailWord_2501219
  simp only [CollatzResearch.WordTrace]
  refine ⟨91226951525518212041234711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60817967683678808027489807 91226951525518212041234711)
  ·
    refine ⟨136840427288277318061852067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91226951525518212041234711 136840427288277318061852067)
    ·
      refine ⟨205260640932415977092778101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136840427288277318061852067 205260640932415977092778101)
      ·
        refine ⟨19243185087413997852447947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205260640932415977092778101 19243185087413997852447947)
        ·
          refine ⟨28864777631120996778671921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19243185087413997852447947 28864777631120996778671921)
          ·
            refine ⟨21648583223340747584003941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28864777631120996778671921 21648583223340747584003941)
            ·
              refine ⟨4059109354376390172000739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21648583223340747584003941 4059109354376390172000739)
              ·
                refine ⟨6088664031564585258001109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059109354376390172000739 6088664031564585258001109)
                ·
                  refine ⟨142703063239794966984401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6088664031564585258001109 142703063239794966984401)
                  ·
                    rfl

theorem cell23_2501219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 7].length) (baseStart_2501219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501219 prefixEnd_2501219 := by exact prefixLift 2501219
  have htrace : WordTrace (prefixWord ++ tailWord_2501219) baseStart_2501219 baseEnd_2501219 := by
    simpa [prefixWord, tailWord_2501219, baseEnd_2501219] using wordTrace_append hprefix tailTrace_2501219
  have hstable : (prefixWord ++ tailWord_2501219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501219).length < 2 ^ (prefixWord ++ tailWord_2501219).sum := by decide
  have hdescent : baseEnd_2501219 < baseStart_2501219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501230 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2501230 : Nat := 118140960795 + 2501230 * 2 ^ 59
def prefixEnd_2501230 : Nat := 4983230072969 + 3 ^ 40 * 2501230 * 2
def baseEnd_2501230 : Nat := 1284333217445354159822059

theorem tailTrace_2501230 : CollatzResearch.WordTrace tailWord_2501230 prefixEnd_2501230 1284333217445354159822059 := by
  unfold tailWord_2501230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403419091059795114985643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60818235152318907279923429 11403419091059795114985643)
  ·
    refine ⟨17105128636589692672478465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403419091059795114985643 17105128636589692672478465)
    ·
      refine ⟨12828846477442269504358849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17105128636589692672478465 12828846477442269504358849)
      ·
        refine ⟨9621634858081702128269137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828846477442269504358849 9621634858081702128269137)
        ·
          refine ⟨7216226143561276596201853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621634858081702128269137 7216226143561276596201853)
          ·
            refine ⟨2706084803835478723575695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7216226143561276596201853 2706084803835478723575695)
            ·
              refine ⟨4059127205753218085363543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706084803835478723575695 4059127205753218085363543)
              ·
                refine ⟨6088690808629827128045315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059127205753218085363543 6088690808629827128045315)
                ·
                  refine ⟨9133036212944740692067973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088690808629827128045315 9133036212944740692067973)
                  ·
                    refine ⟨1712444289927138879762745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9133036212944740692067973 1712444289927138879762745)
                    ·
                      refine ⟨1284333217445354159822059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712444289927138879762745 1284333217445354159822059)
                      ·
                        rfl

theorem cell23_2501230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2501230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501230 prefixEnd_2501230 := by exact prefixLift 2501230
  have htrace : WordTrace (prefixWord ++ tailWord_2501230) baseStart_2501230 baseEnd_2501230 := by
    simpa [prefixWord, tailWord_2501230, baseEnd_2501230] using wordTrace_append hprefix tailTrace_2501230
  have hstable : (prefixWord ++ tailWord_2501230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501230).length < 2 ^ (prefixWord ++ tailWord_2501230).sum := by decide
  have hdescent : baseEnd_2501230 < baseStart_2501230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501249 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2501249 : Nat := 118140960795 + 2501249 * 2 ^ 59
def prefixEnd_2501249 : Nat := 4983230072969 + 3 ^ 40 * 2501249 * 2
def baseEnd_2501249 : Nat := 428114324525929861828157

theorem tailTrace_2501249 : CollatzResearch.WordTrace tailWord_2501249 prefixEnd_2501249 428114324525929861828157 := by
  unfold tailWord_2501249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91228045715409527164826801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60818697143606351443217867 91228045715409527164826801)
  ·
    refine ⟨68421034286557145373620101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91228045715409527164826801 68421034286557145373620101)
    ·
      refine ⟨12828943928729464757553769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68421034286557145373620101 12828943928729464757553769)
      ·
        refine ⟨9621707946547098568165327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828943928729464757553769 9621707946547098568165327)
        ·
          refine ⟨14432561919820647852247991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621707946547098568165327 14432561919820647852247991)
          ·
            refine ⟨21648842879730971778371987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14432561919820647852247991 21648842879730971778371987)
            ·
              refine ⟨32473264319596457667557981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21648842879730971778371987 32473264319596457667557981)
              ·
                refine ⟨12177474119848671625334243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32473264319596457667557981 12177474119848671625334243)
                ·
                  refine ⟨18266211179773007438001365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12177474119848671625334243 18266211179773007438001365)
                  ·
                    refine ⟨428114324525929861828157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18266211179773007438001365 428114324525929861828157)
                    ·
                      rfl

theorem cell23_2501249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2501249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501249 prefixEnd_2501249 := by exact prefixLift 2501249
  have htrace : WordTrace (prefixWord ++ tailWord_2501249) baseStart_2501249 baseEnd_2501249 := by
    simpa [prefixWord, tailWord_2501249, baseEnd_2501249] using wordTrace_append hprefix tailTrace_2501249
  have hstable : (prefixWord ++ tailWord_2501249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501249).length < 2 ^ (prefixWord ++ tailWord_2501249).sum := by decide
  have hdescent : baseEnd_2501249 < baseStart_2501249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501253 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 5]
def baseStart_2501253 : Nat := 118140960795 + 2501253 * 2 ^ 59
def prefixEnd_2501253 : Nat := 4983230072969 + 3 ^ 40 * 2501253 * 2
def baseEnd_2501253 : Nat := 142705003055600841092717

theorem tailTrace_2501253 : CollatzResearch.WordTrace tailWord_2501253 prefixEnd_2501253 142705003055600841092717 := by
  unfold tailWord_2501253
  simp only [CollatzResearch.WordTrace]
  refine ⟨91228191607395035847972413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60818794404930023898648275 91228191607395035847972413)
  ·
    refine ⟨34210571852773138442989655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91228191607395035847972413 34210571852773138442989655)
    ·
      refine ⟨51315857779159707664484483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34210571852773138442989655 51315857779159707664484483)
      ·
        refine ⟨76973786668739561496726725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51315857779159707664484483 76973786668739561496726725)
        ·
          refine ⟨14432585000388667780636261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76973786668739561496726725 14432585000388667780636261)
          ·
            refine ⟨2706109687572875208869299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14432585000388667780636261 2706109687572875208869299)
            ·
              refine ⟨4059164531359312813303949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706109687572875208869299 4059164531359312813303949)
              ·
                refine ⟨1522186699259742304988981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059164531359312813303949 1522186699259742304988981)
                ·
                  refine ⟨142705003055600841092717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522186699259742304988981 142705003055600841092717)
                  ·
                    rfl

theorem cell23_2501253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_2501253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501253 prefixEnd_2501253 := by exact prefixLift 2501253
  have htrace : WordTrace (prefixWord ++ tailWord_2501253) baseStart_2501253 baseEnd_2501253 := by
    simpa [prefixWord, tailWord_2501253, baseEnd_2501253] using wordTrace_append hprefix tailTrace_2501253
  have hstable : (prefixWord ++ tailWord_2501253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501253).length < 2 ^ (prefixWord ++ tailWord_2501253).sum := by decide
  have hdescent : baseEnd_2501253 < baseStart_2501253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501266 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2501266 : Nat := 118140960795 + 2501266 * 2 ^ 59
def prefixEnd_2501266 : Nat := 4983230072969 + 3 ^ 40 * 2501266 * 2
def baseEnd_2501266 : Nat := 428117234249638672990631

theorem tailTrace_2501266 : CollatzResearch.WordTrace tailWord_2501266 prefixEnd_2501266 428117234249638672990631 := by
  unfold tailWord_2501266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22807166439086984767048913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60819110504231959378797101 22807166439086984767048913)
  ·
    refine ⟨17105374829315238575286685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22807166439086984767048913 17105374829315238575286685)
    ·
      refine ⟨6414515560993214465732507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17105374829315238575286685 6414515560993214465732507)
      ·
        refine ⟨9621773341489821698598761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414515560993214465732507 9621773341489821698598761)
        ·
          refine ⟨7216330006117366273949071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621773341489821698598761 7216330006117366273949071)
          ·
            refine ⟨10824495009176049410923607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7216330006117366273949071 10824495009176049410923607)
            ·
              refine ⟨16236742513764074116385411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10824495009176049410923607 16236742513764074116385411)
              ·
                refine ⟨24355113770646111174578117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236742513764074116385411 24355113770646111174578117)
                ·
                  refine ⟨4566583831996145845233397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24355113770646111174578117 4566583831996145845233397)
                  ·
                    refine ⟨428117234249638672990631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4566583831996145845233397 428117234249638672990631)
                    ·
                      rfl

theorem cell23_2501266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2501266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501266 prefixEnd_2501266 := by exact prefixLift 2501266
  have htrace : WordTrace (prefixWord ++ tailWord_2501266) baseStart_2501266 baseEnd_2501266 := by
    simpa [prefixWord, tailWord_2501266, baseEnd_2501266] using wordTrace_append hprefix tailTrace_2501266
  have hstable : (prefixWord ++ tailWord_2501266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501266).length < 2 ^ (prefixWord ++ tailWord_2501266).sum := by decide
  have hdescent : baseEnd_2501266 < baseStart_2501266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501276 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2501276 : Nat := 118140960795 + 2501276 * 2 ^ 59
def prefixEnd_2501276 : Nat := 4983230072969 + 3 ^ 40 * 2501276 * 2
def baseEnd_2501276 : Nat := 1284356837555460979846847

theorem tailTrace_2501276 : CollatzResearch.WordTrace tailWord_2501276 prefixEnd_2501276 1284356837555460979846847 := by
  unfold tailWord_2501276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45614515243155855388029841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60819353657541140517373121 45614515243155855388029841)
  ·
    refine ⟨34210886432366891541022381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45614515243155855388029841 34210886432366891541022381)
    ·
      refine ⟨12829082412137584327883393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34210886432366891541022381 12829082412137584327883393)
      ·
        refine ⟨9621811809103188245912545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12829082412137584327883393 9621811809103188245912545)
        ·
          refine ⟨7216358856827391184434409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621811809103188245912545 7216358856827391184434409)
          ·
            refine ⟨5412269142620543388325807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7216358856827391184434409 5412269142620543388325807)
            ·
              refine ⟨8118403713930815082488711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412269142620543388325807 8118403713930815082488711)
              ·
                refine ⟨12177605570896222623733067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8118403713930815082488711 12177605570896222623733067)
                ·
                  refine ⟨18266408356344333935599601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12177605570896222623733067 18266408356344333935599601)
                  ·
                    refine ⟨13699806267258250451699701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18266408356344333935599601 13699806267258250451699701)
                    ·
                      refine ⟨1284356837555460979846847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13699806267258250451699701 1284356837555460979846847)
                      ·
                        rfl

theorem cell23_2501276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2501276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501276 prefixEnd_2501276 := by exact prefixLift 2501276
  have htrace : WordTrace (prefixWord ++ tailWord_2501276) baseStart_2501276 baseEnd_2501276 := by
    simpa [prefixWord, tailWord_2501276, baseEnd_2501276] using wordTrace_append hprefix tailTrace_2501276
  have hstable : (prefixWord ++ tailWord_2501276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501276).length < 2 ^ (prefixWord ++ tailWord_2501276).sum := by decide
  have hdescent : baseEnd_2501276 < baseStart_2501276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501303 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_2501303 : Nat := 118140960795 + 2501303 * 2 ^ 59
def prefixEnd_2501303 : Nat := 4983230072969 + 3 ^ 40 * 2501303 * 2
def baseEnd_2501303 : Nat := 1284370701533132374209223

theorem tailTrace_2501303 : CollatzResearch.WordTrace tailWord_2501303 prefixEnd_2501303 1284370701533132374209223 := by
  unfold tailWord_2501303
  simp only [CollatzResearch.WordTrace]
  refine ⟨91230015257213894387292563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60820010171475929591528375 91230015257213894387292563)
  ·
    refine ⟨136845022885820841580938845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91230015257213894387292563 136845022885820841580938845)
    ·
      refine ⟨51316883582182815592852067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136845022885820841580938845 51316883582182815592852067)
      ·
        refine ⟨76975325373274223389278101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51316883582182815592852067 76975325373274223389278101)
        ·
          refine ⟨3608218376872229221372411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76975325373274223389278101 3608218376872229221372411)
          ·
            refine ⟨5412327565308343832058617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608218376872229221372411 5412327565308343832058617)
            ·
              refine ⟨4059245673981257874043963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412327565308343832058617 4059245673981257874043963)
              ·
                refine ⟨6088868510971886811065945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059245673981257874043963 6088868510971886811065945)
                ·
                  refine ⟨4566651383228915108299459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088868510971886811065945 4566651383228915108299459)
                  ·
                    refine ⟨6849977074843372662449189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566651383228915108299459 6849977074843372662449189)
                    ·
                      refine ⟨1284370701533132374209223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6849977074843372662449189 1284370701533132374209223)
                      ·
                        rfl

theorem cell23_2501303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_2501303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501303 prefixEnd_2501303 := by exact prefixLift 2501303
  have htrace : WordTrace (prefixWord ++ tailWord_2501303) baseStart_2501303 baseEnd_2501303 := by
    simpa [prefixWord, tailWord_2501303, baseEnd_2501303] using wordTrace_append hprefix tailTrace_2501303
  have hstable : (prefixWord ++ tailWord_2501303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501303).length < 2 ^ (prefixWord ++ tailWord_2501303).sum := by decide
  have hdescent : baseEnd_2501303 < baseStart_2501303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501326 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_2501326 : Nat := 118140960795 + 2501326 * 2 ^ 59
def prefixEnd_2501326 : Nat := 4983230072969 + 3 ^ 40 * 2501326 * 2
def baseEnd_2501326 : Nat := 142709167954242864913513

theorem tailTrace_2501326 : CollatzResearch.WordTrace tailWord_2501326 prefixEnd_2501326 142709167954242864913513 := by
  unfold tailWord_2501326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403856767016321164422479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60820569424087046210253221 11403856767016321164422479)
  ·
    refine ⟨17105785150524481746633719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403856767016321164422479 17105785150524481746633719)
    ·
      refine ⟨25658677725786722619950579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17105785150524481746633719 25658677725786722619950579)
      ·
        refine ⟨38488016588680083929925869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25658677725786722619950579 38488016588680083929925869)
        ·
          refine ⟨14433006220755031473722201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38488016588680083929925869 14433006220755031473722201)
          ·
            refine ⟨10824754665566273605291651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14433006220755031473722201 10824754665566273605291651)
            ·
              refine ⟨16237131998349410407937477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10824754665566273605291651 16237131998349410407937477)
              ·
                refine ⟨3044462249690514451488277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16237131998349410407937477 3044462249690514451488277)
                ·
                  refine ⟨142709167954242864913513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3044462249690514451488277 142709167954242864913513)
                  ·
                    rfl

theorem cell23_2501326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_2501326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501326 prefixEnd_2501326 := by exact prefixLift 2501326
  have htrace : WordTrace (prefixWord ++ tailWord_2501326) baseStart_2501326 baseEnd_2501326 := by
    simpa [prefixWord, tailWord_2501326, baseEnd_2501326] using wordTrace_append hprefix tailTrace_2501326
  have hstable : (prefixWord ++ tailWord_2501326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501326).length < 2 ^ (prefixWord ++ tailWord_2501326).sum := by decide
  have hdescent : baseEnd_2501326 < baseStart_2501326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501329 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2501329 : Nat := 118140960795 + 2501329 * 2 ^ 59
def prefixEnd_2501329 : Nat := 4983230072969 + 3 ^ 40 * 2501329 * 2
def baseEnd_2501329 : Nat := 1284384052030149272484103

theorem tailTrace_2501329 : CollatzResearch.WordTrace tailWord_2501329 prefixEnd_2501329 1284384052030149272484103 := by
  unfold tailWord_2501329
  simp only [CollatzResearch.WordTrace]
  refine ⟨91230963555119700827739041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60820642370079800551826027 91230963555119700827739041)
  ·
    refine ⟨68423222666339775620804281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91230963555119700827739041 68423222666339775620804281)
    ·
      refine ⟨51317416999754831715603211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68423222666339775620804281 51317416999754831715603211)
      ·
        refine ⟨76976125499632247573404817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51317416999754831715603211 76976125499632247573404817)
        ·
          refine ⟨57732094124724185680053613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76976125499632247573404817 57732094124724185680053613)
          ·
            refine ⟨21649535296771569630020105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57732094124724185680053613 21649535296771569630020105)
            ·
              refine ⟨16237151472578677222515079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21649535296771569630020105 16237151472578677222515079)
              ·
                refine ⟨24355727208868015833772619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16237151472578677222515079 24355727208868015833772619)
                ·
                  refine ⟨36533590813302023750658929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24355727208868015833772619 36533590813302023750658929)
                  ·
                    refine ⟨27400193109976517812994197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36533590813302023750658929 27400193109976517812994197)
                    ·
                      refine ⟨1284384052030149272484103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27400193109976517812994197 1284384052030149272484103)
                      ·
                        rfl

theorem cell23_2501329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2501329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501329 prefixEnd_2501329 := by exact prefixLift 2501329
  have htrace : WordTrace (prefixWord ++ tailWord_2501329) baseStart_2501329 baseEnd_2501329 := by
    simpa [prefixWord, tailWord_2501329, baseEnd_2501329] using wordTrace_append hprefix tailTrace_2501329
  have hstable : (prefixWord ++ tailWord_2501329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501329).length < 2 ^ (prefixWord ++ tailWord_2501329).sum := by decide
  have hdescent : baseEnd_2501329 < baseStart_2501329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501356 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_2501356 : Nat := 118140960795 + 2501356 * 2 ^ 59
def prefixEnd_2501356 : Nat := 4983230072969 + 3 ^ 40 * 2501356 * 2
def baseEnd_2501356 : Nat := 428132638669273555615493

theorem tailTrace_2501356 : CollatzResearch.WordTrace tailWord_2501356 prefixEnd_2501356 428132638669273555615493 := by
  unfold tailWord_2501356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45615974163010942219485961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60821298884014589625981281 45615974163010942219485961)
  ·
    refine ⟨34211980622258206664614471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45615974163010942219485961 34211980622258206664614471)
    ·
      refine ⟨51317970933387309996921707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34211980622258206664614471 51317970933387309996921707)
      ·
        refine ⟨76976956400080964995382561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51317970933387309996921707 76976956400080964995382561)
        ·
          refine ⟨57732717300060723746536921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76976956400080964995382561 57732717300060723746536921)
          ·
            refine ⟨43299537975045542809902691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57732717300060723746536921 43299537975045542809902691)
            ·
              refine ⟨64949306962568314214854037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43299537975045542809902691 64949306962568314214854037)
              ·
                refine ⟨3044498763870389728821283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64949306962568314214854037 3044498763870389728821283)
                ·
                  refine ⟨4566748145805584593231925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044498763870389728821283 4566748145805584593231925)
                  ·
                    refine ⟨428132638669273555615493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4566748145805584593231925 428132638669273555615493)
                    ·
                      rfl

theorem cell23_2501356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_2501356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501356 prefixEnd_2501356 := by exact prefixLift 2501356
  have htrace : WordTrace (prefixWord ++ tailWord_2501356) baseStart_2501356 baseEnd_2501356 := by
    simpa [prefixWord, tailWord_2501356, baseEnd_2501356] using wordTrace_append hprefix tailTrace_2501356
  have hstable : (prefixWord ++ tailWord_2501356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501356).length < 2 ^ (prefixWord ++ tailWord_2501356).sum := by decide
  have hdescent : baseEnd_2501356 < baseStart_2501356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501370 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_2501370 : Nat := 118140960795 + 2501370 * 2 ^ 59
def prefixEnd_2501370 : Nat := 4983230072969 + 3 ^ 40 * 2501370 * 2
def baseEnd_2501370 : Nat := 1284405104736983612071415

theorem tailTrace_2501370 : CollatzResearch.WordTrace tailWord_2501370 prefixEnd_2501370 1284405104736983612071415 := by
  unfold tailWord_2501370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808114736992791207495391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60821639298647443219987709 22808114736992791207495391)
  ·
    refine ⟨34212172105489186811243087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22808114736992791207495391 34212172105489186811243087)
    ·
      refine ⟨51318258158233780216864631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34212172105489186811243087 51318258158233780216864631)
      ·
        refine ⟨76977387237350670325296947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51318258158233780216864631 76977387237350670325296947)
        ·
          refine ⟨115466080856026005487945421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76977387237350670325296947 115466080856026005487945421)
          ·
            refine ⟨43299780321009752057979533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115466080856026005487945421 43299780321009752057979533)
            ·
              refine ⟨16237417620378657021742325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43299780321009752057979533 16237417620378657021742325)
              ·
                refine ⟨1522257901910499095788343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16237417620378657021742325 1522257901910499095788343)
                ·
                  refine ⟨2283386852865748643682515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522257901910499095788343 2283386852865748643682515)
                  ·
                    refine ⟨3425080279298622965523773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283386852865748643682515 3425080279298622965523773)
                    ·
                      refine ⟨1284405104736983612071415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425080279298622965523773 1284405104736983612071415)
                      ·
                        rfl

theorem cell23_2501370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_2501370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501370 prefixEnd_2501370 := by exact prefixLift 2501370
  have htrace : WordTrace (prefixWord ++ tailWord_2501370) baseStart_2501370 baseEnd_2501370 := by
    simpa [prefixWord, tailWord_2501370, baseEnd_2501370] using wordTrace_append hprefix tailTrace_2501370
  have hstable : (prefixWord ++ tailWord_2501370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501370).length < 2 ^ (prefixWord ++ tailWord_2501370).sum := by decide
  have hdescent : baseEnd_2501370 < baseStart_2501370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501410 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2501410 : Nat := 118140960795 + 2501410 * 2 ^ 59
def prefixEnd_2501410 : Nat := 4983230072969 + 3 ^ 40 * 2501410 * 2
def baseEnd_2501410 : Nat := 1284425643963163455571231

theorem tailTrace_2501410 : CollatzResearch.WordTrace tailWord_2501410 prefixEnd_2501410 1284425643963163455571231 := by
  unfold tailWord_2501410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808479466956562915359421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60822611911884167774291789 22808479466956562915359421)
  ·
    refine ⟨8553179800108711093259783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22808479466956562915359421 8553179800108711093259783)
    ·
      refine ⟨12829769700163066639889675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8553179800108711093259783 12829769700163066639889675)
      ·
        refine ⟨19244654550244599959834513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12829769700163066639889675 19244654550244599959834513)
        ·
          refine ⟨14433490912683449969875885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19244654550244599959834513 14433490912683449969875885)
          ·
            refine ⟨5412559092256293738703457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14433490912683449969875885 5412559092256293738703457)
            ·
              refine ⟨4059419319192220304027593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412559092256293738703457 4059419319192220304027593)
              ·
                refine ⟨3044564489394165228020695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059419319192220304027593 3044564489394165228020695)
                ·
                  refine ⟨4566846734091247842031043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044564489394165228020695 4566846734091247842031043)
                  ·
                    refine ⟨6850270101136871763046565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566846734091247842031043 6850270101136871763046565)
                    ·
                      refine ⟨1284425643963163455571231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6850270101136871763046565 1284425643963163455571231)
                      ·
                        rfl

theorem cell23_2501410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2501410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501410 prefixEnd_2501410 := by exact prefixLift 2501410
  have htrace : WordTrace (prefixWord ++ tailWord_2501410) baseStart_2501410 baseEnd_2501410 := by
    simpa [prefixWord, tailWord_2501410, baseEnd_2501410] using wordTrace_append hprefix tailTrace_2501410
  have hstable : (prefixWord ++ tailWord_2501410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501410).length < 2 ^ (prefixWord ++ tailWord_2501410).sum := by decide
  have hdescent : baseEnd_2501410 < baseStart_2501410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501416 : List Nat := [2, 1, 5, 1, 1, 1, 3, 9]
def baseStart_2501416 : Nat := 118140960795 + 2501416 * 2 ^ 59
def prefixEnd_2501416 : Nat := 4983230072969 + 3 ^ 40 * 2501416 * 2
def baseEnd_2501416 : Nat := 47571434253595941929489

theorem tailTrace_2501416 : CollatzResearch.WordTrace tailWord_2501416 prefixEnd_2501416 47571434253595941929489 := by
  unfold tailWord_2501416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45617068352902257343078051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60822757803869676457437401 45617068352902257343078051)
  ·
    refine ⟨68425602529353386014617077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45617068352902257343078051 68425602529353386014617077)
    ·
      refine ⟨6414900237126879938870351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68425602529353386014617077 6414900237126879938870351)
      ·
        refine ⟨9622350355690319908305527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414900237126879938870351 9622350355690319908305527)
        ·
          refine ⟨14433525533535479862458291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9622350355690319908305527 14433525533535479862458291)
          ·
            refine ⟨21650288300303219793687437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14433525533535479862458291 21650288300303219793687437)
            ·
              refine ⟨8118858112613707422632789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21650288300303219793687437 8118858112613707422632789)
              ·
                refine ⟨47571434253595941929489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8118858112613707422632789 47571434253595941929489)
                ·
                  rfl

theorem cell23_2501416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 9].length) (baseStart_2501416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501416 prefixEnd_2501416 := by exact prefixLift 2501416
  have htrace : WordTrace (prefixWord ++ tailWord_2501416) baseStart_2501416 baseEnd_2501416 := by
    simpa [prefixWord, tailWord_2501416, baseEnd_2501416] using wordTrace_append hprefix tailTrace_2501416
  have hstable : (prefixWord ++ tailWord_2501416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501416).length < 2 ^ (prefixWord ++ tailWord_2501416).sum := by decide
  have hdescent : baseEnd_2501416 < baseStart_2501416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501443 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 3]
def baseStart_2501443 : Nat := 118140960795 + 2501443 * 2 ^ 59
def prefixEnd_2501443 : Nat := 4983230072969 + 3 ^ 40 * 2501443 * 2
def baseEnd_2501443 : Nat := 1284442588824761826458579

theorem tailTrace_2501443 : CollatzResearch.WordTrace tailWord_2501443 prefixEnd_2501443 1284442588824761826458579 := by
  unfold tailWord_2501443
  simp only [CollatzResearch.WordTrace]
  refine ⟨91235121476706698297388983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60823414317804465531592655 91235121476706698297388983)
  ·
    refine ⟨136852682215060047446083475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91235121476706698297388983 136852682215060047446083475)
    ·
      refine ⟨205279023322590071169125213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136852682215060047446083475 205279023322590071169125213)
      ·
        refine ⟨76979633745971276688421955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205279023322590071169125213 76979633745971276688421955)
        ·
          refine ⟨115469450618956915032632933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76979633745971276688421955 115469450618956915032632933)
          ·
            refine ⟨21650521991054421568618675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115469450618956915032632933 21650521991054421568618675)
            ·
              refine ⟨32475782986581632352928013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21650521991054421568618675 32475782986581632352928013)
              ·
                refine ⟨12178418619968112132348005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32475782986581632352928013 12178418619968112132348005)
                ·
                  refine ⟨2283453491244021024815251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12178418619968112132348005 2283453491244021024815251)
                  ·
                    refine ⟨3425180236866031537222877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283453491244021024815251 3425180236866031537222877)
                    ·
                      refine ⟨1284442588824761826458579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425180236866031537222877 1284442588824761826458579)
                      ·
                        rfl

theorem cell23_2501443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_2501443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501443 prefixEnd_2501443 := by exact prefixLift 2501443
  have htrace : WordTrace (prefixWord ++ tailWord_2501443) baseStart_2501443 baseEnd_2501443 := by
    simpa [prefixWord, tailWord_2501443, baseEnd_2501443] using wordTrace_append hprefix tailTrace_2501443
  have hstable : (prefixWord ++ tailWord_2501443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501443).length < 2 ^ (prefixWord ++ tailWord_2501443).sum := by decide
  have hdescent : baseEnd_2501443 < baseStart_2501443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501483 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 4, 2]
def baseStart_2501483 : Nat := 118140960795 + 2501483 * 2 ^ 59
def prefixEnd_2501483 : Nat := 4983230072969 + 3 ^ 40 * 2501483 * 2
def baseEnd_2501483 : Nat := 1284463128050941669958395

theorem tailTrace_2501483 : CollatzResearch.WordTrace tailWord_2501483 prefixEnd_2501483 1284463128050941669958395 := by
  unfold tailWord_2501483
  simp only [CollatzResearch.WordTrace]
  refine ⟨91236580396561785128845103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60824386931041190085896735 91236580396561785128845103)
  ·
    refine ⟨136854870594842677693267655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91236580396561785128845103 136854870594842677693267655)
    ·
      refine ⟨205282305892264016539901483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136854870594842677693267655 205282305892264016539901483)
      ·
        refine ⟨307923458838396024809852225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205282305892264016539901483 307923458838396024809852225)
        ·
          refine ⟨230942594128797018607389169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307923458838396024809852225 230942594128797018607389169)
          ·
            refine ⟨173206945596597763955541877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230942594128797018607389169 173206945596597763955541877)
            ·
              refine ⟨16238151149681040370832051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173206945596597763955541877 16238151149681040370832051)
              ·
                refine ⟨24357226724521560556248077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16238151149681040370832051 24357226724521560556248077)
                ·
                  refine ⟨9133960021695585208593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24357226724521560556248077 9133960021695585208593029)
                  ·
                    refine ⟨1712617504067922226611193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9133960021695585208593029 1712617504067922226611193)
                    ·
                      refine ⟨1284463128050941669958395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712617504067922226611193 1284463128050941669958395)
                      ·
                        rfl

theorem cell23_2501483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4, 2].length) (baseStart_2501483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501483 prefixEnd_2501483 := by exact prefixLift 2501483
  have htrace : WordTrace (prefixWord ++ tailWord_2501483) baseStart_2501483 baseEnd_2501483 := by
    simpa [prefixWord, tailWord_2501483, baseEnd_2501483] using wordTrace_append hprefix tailTrace_2501483
  have hstable : (prefixWord ++ tailWord_2501483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501483).length < 2 ^ (prefixWord ++ tailWord_2501483).sum := by decide
  have hdescent : baseEnd_2501483 < baseStart_2501483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501494 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2501494 : Nat := 118140960795 + 2501494 * 2 ^ 59
def prefixEnd_2501494 : Nat := 4983230072969 + 3 ^ 40 * 2501494 * 2
def baseEnd_2501494 : Nat := 1284468776338141126920845

theorem tailTrace_2501494 : CollatzResearch.WordTrace tailWord_2501494 prefixEnd_2501494 1284468776338141126920845 := by
  unfold tailWord_2501494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702311349970120875468471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60824654399681289338330357 5702311349970120875468471)
  ·
    refine ⟨8553467024955181313202707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5702311349970120875468471 8553467024955181313202707)
    ·
      refine ⟨12830200537432771969804061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8553467024955181313202707 12830200537432771969804061)
      ·
        refine ⟨4811325201537289488676523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12830200537432771969804061 4811325201537289488676523)
        ·
          refine ⟨7216987802305934233014785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811325201537289488676523 7216987802305934233014785)
          ·
            refine ⟨5412740851729450674761089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7216987802305934233014785 5412740851729450674761089)
            ·
              refine ⟨4059555638797088006070817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412740851729450674761089 4059555638797088006070817)
              ·
                refine ⟨3044666729097816004553113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059555638797088006070817 3044666729097816004553113)
                ·
                  refine ⟨2283500046823362003414835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044666729097816004553113 2283500046823362003414835)
                  ·
                    refine ⟨3425250070235043005122253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283500046823362003414835 3425250070235043005122253)
                    ·
                      refine ⟨1284468776338141126920845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425250070235043005122253 1284468776338141126920845)
                      ·
                        rfl

theorem cell23_2501494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2501494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501494 prefixEnd_2501494 := by exact prefixLift 2501494
  have htrace : WordTrace (prefixWord ++ tailWord_2501494) baseStart_2501494 baseEnd_2501494 := by
    simpa [prefixWord, tailWord_2501494, baseEnd_2501494] using wordTrace_append hprefix tailTrace_2501494
  have hstable : (prefixWord ++ tailWord_2501494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501494).length < 2 ^ (prefixWord ++ tailWord_2501494).sum := by decide
  have hdescent : baseEnd_2501494 < baseStart_2501494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_2501500 : Nat := 118140960795 + 2501500 * 2 ^ 59
def prefixEnd_2501500 : Nat := 4983230072969 + 3 ^ 40 * 2501500 * 2
def baseEnd_2501500 : Nat := 1284471857222068103445817

theorem tailTrace_2501500 : CollatzResearch.WordTrace tailWord_2501500 prefixEnd_2501500 1284471857222068103445817 := by
  unfold tailWord_2501500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45618600218750098516106977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60824800291666798021475969 45618600218750098516106977)
  ·
    refine ⟨34213950164062573887080233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45618600218750098516106977 34213950164062573887080233)
    ·
      refine ⟨25660462623046930415310175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34213950164062573887080233 25660462623046930415310175)
      ·
        refine ⟨38490693934570395622965263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25660462623046930415310175 38490693934570395622965263)
        ·
          refine ⟨57736040901855593434447895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38490693934570395622965263 57736040901855593434447895)
          ·
            refine ⟨86604061352783390151671843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57736040901855593434447895 86604061352783390151671843)
            ·
              refine ⟨129906092029175085227507765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86604061352783390151671843 129906092029175085227507765)
              ·
                refine ⟨12178696127735164240078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129906092029175085227507765 12178696127735164240078853)
                ·
                  refine ⟨2283505523950343295014785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12178696127735164240078853 2283505523950343295014785)
                  ·
                    refine ⟨1712629142962757471261089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283505523950343295014785 1712629142962757471261089)
                    ·
                      refine ⟨1284471857222068103445817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712629142962757471261089 1284471857222068103445817)
                      ·
                        rfl

theorem cell23_2501500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_2501500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501500 prefixEnd_2501500 := by exact prefixLift 2501500
  have htrace : WordTrace (prefixWord ++ tailWord_2501500) baseStart_2501500 baseEnd_2501500 := by
    simpa [prefixWord, tailWord_2501500, baseEnd_2501500] using wordTrace_append hprefix tailTrace_2501500
  have hstable : (prefixWord ++ tailWord_2501500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501500).length < 2 ^ (prefixWord ++ tailWord_2501500).sum := by decide
  have hdescent : baseEnd_2501500 < baseStart_2501500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501513 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_2501513 : Nat := 118140960795 + 2501513 * 2 ^ 59
def prefixEnd_2501513 : Nat := 4983230072969 + 3 ^ 40 * 2501513 * 2
def baseEnd_2501513 : Nat := 1284478532470576552583257

theorem tailTrace_2501513 : CollatzResearch.WordTrace tailWord_2501513 prefixEnd_2501513 1284478532470576552583257 := by
  unfold tailWord_2501513
  simp only [CollatzResearch.WordTrace]
  refine ⟨91237674586453100252437193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60825116390968733501624795 91237674586453100252437193)
  ·
    refine ⟨68428255939839825189327895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91237674586453100252437193 68428255939839825189327895)
    ·
      refine ⟨102642383909759737783991843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68428255939839825189327895 102642383909759737783991843)
      ·
        refine ⟨153963575864639606675987765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102642383909759737783991843 153963575864639606675987765)
        ·
          refine ⟨14434085237309963125873853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153963575864639606675987765 14434085237309963125873853)
          ·
            refine ⟨5412781963991236172202695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14434085237309963125873853 5412781963991236172202695)
            ·
              refine ⟨8119172945986854258304043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412781963991236172202695 8119172945986854258304043)
              ·
                refine ⟨12178759418980281387456065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8119172945986854258304043 12178759418980281387456065)
                ·
                  refine ⟨9134069564235211040592049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12178759418980281387456065 9134069564235211040592049)
                  ·
                    refine ⟨6850552173176408280444037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9134069564235211040592049 6850552173176408280444037)
                    ·
                      refine ⟨1284478532470576552583257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6850552173176408280444037 1284478532470576552583257)
                      ·
                        rfl

theorem cell23_2501513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_2501513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501513 prefixEnd_2501513 := by exact prefixLift 2501513
  have htrace : WordTrace (prefixWord ++ tailWord_2501513) baseStart_2501513 baseEnd_2501513 := by
    simpa [prefixWord, tailWord_2501513, baseEnd_2501513] using wordTrace_append hprefix tailTrace_2501513
  have hstable : (prefixWord ++ tailWord_2501513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501513).length < 2 ^ (prefixWord ++ tailWord_2501513).sum := by decide
  have hdescent : baseEnd_2501513 < baseStart_2501513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501533 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2501533 : Nat := 118140960795 + 2501533 * 2 ^ 59
def prefixEnd_2501533 : Nat := 4983230072969 + 3 ^ 40 * 2501533 * 2
def baseEnd_2501533 : Nat := 1284488802083666474333165

theorem tailTrace_2501533 : CollatzResearch.WordTrace tailWord_2501533 prefixEnd_2501533 1284488802083666474333165 := by
  unfold tailWord_2501533
  simp only [CollatzResearch.WordTrace]
  refine ⟨91238404046380643668165253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60825602697587095778776835 91238404046380643668165253)
  ·
    refine ⟨17107200758696370687780985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91238404046380643668165253 17107200758696370687780985)
    ·
      refine ⟨12830400569022278015835739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17107200758696370687780985 12830400569022278015835739)
      ·
        refine ⟨19245600853533417023753609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12830400569022278015835739 19245600853533417023753609)
        ·
          refine ⟨14434200640150062767815207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19245600853533417023753609 14434200640150062767815207)
          ·
            refine ⟨21651300960225094151722811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14434200640150062767815207 21651300960225094151722811)
            ·
              refine ⟨32476951440337641227584217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21651300960225094151722811 32476951440337641227584217)
              ·
                refine ⟨24357713580253230920688163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32476951440337641227584217 24357713580253230920688163)
                ·
                  refine ⟨36536570370379846381032245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24357713580253230920688163 36536570370379846381032245)
                  ·
                    refine ⟨3425303472223110598221773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36536570370379846381032245 3425303472223110598221773)
                    ·
                      refine ⟨1284488802083666474333165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425303472223110598221773 1284488802083666474333165)
                      ·
                        rfl

theorem cell23_2501533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2501533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501533 prefixEnd_2501533 := by exact prefixLift 2501533
  have htrace : WordTrace (prefixWord ++ tailWord_2501533) baseStart_2501533 baseEnd_2501533 := by
    simpa [prefixWord, tailWord_2501533, baseEnd_2501533] using wordTrace_append hprefix tailTrace_2501533
  have hstable : (prefixWord ++ tailWord_2501533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501533).length < 2 ^ (prefixWord ++ tailWord_2501533).sum := by decide
  have hdescent : baseEnd_2501533 < baseStart_2501533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501540 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2501540 : Nat := 118140960795 + 2501540 * 2 ^ 59
def prefixEnd_2501540 : Nat := 4983230072969 + 3 ^ 40 * 2501540 * 2
def baseEnd_2501540 : Nat := 142721377383138660771737

theorem tailTrace_2501540 : CollatzResearch.WordTrace tailWord_2501540 prefixEnd_2501540 142721377383138660771737 := by
  unfold tailWord_2501540
  simp only [CollatzResearch.WordTrace]
  refine ⟨45619329678677641931835037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60825772904903522575780049 45619329678677641931835037)
  ·
    refine ⟨17107248629504115724438139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45619329678677641931835037 17107248629504115724438139)
    ·
      refine ⟨25660872944256173586657209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17107248629504115724438139 25660872944256173586657209)
      ·
        refine ⟨19245654708192130189992907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25660872944256173586657209 19245654708192130189992907)
        ·
          refine ⟨28868482062288195284989361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19245654708192130189992907 28868482062288195284989361)
          ·
            refine ⟨21651361546716146463742021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28868482062288195284989361 21651361546716146463742021)
            ·
              refine ⟨4059630290009277461951629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21651361546716146463742021 4059630290009277461951629)
              ·
                refine ⟨1522361358753479048231861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059630290009277461951629 1522361358753479048231861)
                ·
                  refine ⟨142721377383138660771737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522361358753479048231861 142721377383138660771737)
                  ·
                    rfl

theorem cell23_2501540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2501540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501540 prefixEnd_2501540 := by exact prefixLift 2501540
  have htrace : WordTrace (prefixWord ++ tailWord_2501540) baseStart_2501540 baseEnd_2501540 := by
    simpa [prefixWord, tailWord_2501540, baseEnd_2501540] using wordTrace_append hprefix tailTrace_2501540
  have hstable : (prefixWord ++ tailWord_2501540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501540).length < 2 ^ (prefixWord ++ tailWord_2501540).sum := by decide
  have hdescent : baseEnd_2501540 < baseStart_2501540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501610 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2501610 : Nat := 118140960795 + 2501610 * 2 ^ 59
def prefixEnd_2501610 : Nat := 4983230072969 + 3 ^ 40 * 2501610 * 2
def baseEnd_2501610 : Nat := 1284528340094062673070311

theorem tailTrace_2501610 : CollatzResearch.WordTrace tailWord_2501610 prefixEnd_2501610 1284528340094062673070311 := by
  unfold tailWord_2501610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810303116775421454679571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60827474978067790545812189 22810303116775421454679571)
  ·
    refine ⟨34215454675163132182019357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22810303116775421454679571 34215454675163132182019357)
    ·
      refine ⟨12830795503186174568257259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34215454675163132182019357 12830795503186174568257259)
      ·
        refine ⟨19246193254779261852385889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12830795503186174568257259 19246193254779261852385889)
        ·
          refine ⟨14434644941084446389289417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19246193254779261852385889 14434644941084446389289417)
          ·
            refine ⟨10825983705813334791967063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14434644941084446389289417 10825983705813334791967063)
            ·
              refine ⟨16238975558720002187950595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10825983705813334791967063 16238975558720002187950595)
              ·
                refine ⟨24358463338080003281925893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16238975558720002187950595 24358463338080003281925893)
                ·
                  refine ⟨4567211875890000615361105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24358463338080003281925893 4567211875890000615361105)
                  ·
                    refine ⟨3425408906917500461520829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567211875890000615361105 3425408906917500461520829)
                    ·
                      refine ⟨1284528340094062673070311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425408906917500461520829 1284528340094062673070311)
                      ·
                        rfl

theorem cell23_2501610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2501610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501610 prefixEnd_2501610 := by exact prefixLift 2501610
  have htrace : WordTrace (prefixWord ++ tailWord_2501610) baseStart_2501610 baseEnd_2501610 := by
    simpa [prefixWord, tailWord_2501610, baseEnd_2501610] using wordTrace_append hprefix tailTrace_2501610
  have hstable : (prefixWord ++ tailWord_2501610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501610).length < 2 ^ (prefixWord ++ tailWord_2501610).sum := by decide
  have hdescent : baseEnd_2501610 < baseStart_2501610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501617 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2501617 : Nat := 118140960795 + 2501617 * 2 ^ 59
def prefixEnd_2501617 : Nat := 4983230072969 + 3 ^ 40 * 2501617 * 2
def baseEnd_2501617 : Nat := 428177311486214715227593

theorem tailTrace_2501617 : CollatzResearch.WordTrace tailWord_2501617 prefixEnd_2501617 428177311486214715227593 := by
  unfold tailWord_2501617
  simp only [CollatzResearch.WordTrace]
  refine ⟨91241467778076326014223105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60827645185384217342815403 91241467778076326014223105)
  ·
    refine ⟨68431100833557244510667329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91241467778076326014223105 68431100833557244510667329)
    ·
      refine ⟨51323325625167933383000497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68431100833557244510667329 51323325625167933383000497)
      ·
        refine ⟨38492494218875950037250373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51323325625167933383000497 38492494218875950037250373)
        ·
          refine ⟨7217342666039240631984445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38492494218875950037250373 7217342666039240631984445)
          ·
            refine ⟨2706503499764715236994167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7217342666039240631984445 2706503499764715236994167)
            ·
              refine ⟨4059755249647072855491251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706503499764715236994167 4059755249647072855491251)
              ·
                refine ⟨6089632874470609283236877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059755249647072855491251 6089632874470609283236877)
                ·
                  refine ⟨2283612327926478481213829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6089632874470609283236877 2283612327926478481213829)
                  ·
                    refine ⟨428177311486214715227593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283612327926478481213829 428177311486214715227593)
                    ·
                      rfl

theorem cell23_2501617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2501617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501617 prefixEnd_2501617 := by exact prefixLift 2501617
  have htrace : WordTrace (prefixWord ++ tailWord_2501617) baseStart_2501617 baseEnd_2501617 := by
    simpa [prefixWord, tailWord_2501617, baseEnd_2501617] using wordTrace_append hprefix tailTrace_2501617
  have hstable : (prefixWord ++ tailWord_2501617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501617).length < 2 ^ (prefixWord ++ tailWord_2501617).sum := by decide
  have hdescent : baseEnd_2501617 < baseStart_2501617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501667 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 2, 3, 2]
def baseStart_2501667 : Nat := 118140960795 + 2501667 * 2 ^ 59
def prefixEnd_2501667 : Nat := 4983230072969 + 3 ^ 40 * 2501667 * 2
def baseEnd_2501667 : Nat := 1284557608491368950057549

theorem tailTrace_2501667 : CollatzResearch.WordTrace tailWord_2501667 prefixEnd_2501667 1284557608491368950057549 := by
  unfold tailWord_2501667
  simp only [CollatzResearch.WordTrace]
  refine ⟨91243291427895184553543255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60828860951930123035695503 91243291427895184553543255)
  ·
    refine ⟨136864937141842776830314883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91243291427895184553543255 136864937141842776830314883)
    ·
      refine ⟨205297405712764165245472325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136864937141842776830314883 205297405712764165245472325)
      ·
        refine ⟨38493263571143280983526061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205297405712764165245472325 38493263571143280983526061)
        ·
          refine ⟨14434973839178730368822273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38493263571143280983526061 14434973839178730368822273)
          ·
            refine ⟨10826230379384047776616705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14434973839178730368822273 10826230379384047776616705)
            ·
              refine ⟨8119672784538035832462529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10826230379384047776616705 8119672784538035832462529)
              ·
                refine ⟨6089754588403526874346897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8119672784538035832462529 6089754588403526874346897)
                ·
                  refine ⟨4567315941302645155760173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089754588403526874346897 4567315941302645155760173)
                  ·
                    refine ⟨1712743477988491933410065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4567315941302645155760173 1712743477988491933410065)
                    ·
                      refine ⟨1284557608491368950057549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712743477988491933410065 1284557608491368950057549)
                      ·
                        rfl

theorem cell23_2501667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_2501667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501667 prefixEnd_2501667 := by exact prefixLift 2501667
  have htrace : WordTrace (prefixWord ++ tailWord_2501667) baseStart_2501667 baseEnd_2501667 := by
    simpa [prefixWord, tailWord_2501667, baseEnd_2501667] using wordTrace_append hprefix tailTrace_2501667
  have hstable : (prefixWord ++ tailWord_2501667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501667).length < 2 ^ (prefixWord ++ tailWord_2501667).sum := by decide
  have hdescent : baseEnd_2501667 < baseStart_2501667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_2501683 : Nat := 118140960795 + 2501683 * 2 ^ 59
def prefixEnd_2501683 : Nat := 4983230072969 + 3 ^ 40 * 2501683 * 2
def baseEnd_2501683 : Nat := 1284565824181840887457475

theorem tailTrace_2501683 : CollatzResearch.WordTrace tailWord_2501683 prefixEnd_2501683 1284565824181840887457475 := by
  unfold tailWord_2501683
  simp only [CollatzResearch.WordTrace]
  refine ⟨91243874995837219286125703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60829249997224812857417135 91243874995837219286125703)
  ·
    refine ⟨136865812493755828929188555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91243874995837219286125703 136865812493755828929188555)
    ·
      refine ⟨205298718740633743393782833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136865812493755828929188555 205298718740633743393782833)
      ·
        refine ⟨153974039055475307545337125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205298718740633743393782833 153974039055475307545337125)
        ·
          refine ⟨28870132322901620164750711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153974039055475307545337125 28870132322901620164750711)
          ·
            refine ⟨43305198484352430247126067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28870132322901620164750711 43305198484352430247126067)
            ·
              refine ⟨64957797726528645370689101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43305198484352430247126067 64957797726528645370689101)
              ·
                refine ⟨24359174147448242014008413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64957797726528645370689101 24359174147448242014008413)
                ·
                  refine ⟨9134690305293090755253155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24359174147448242014008413 9134690305293090755253155)
                  ·
                    refine ⟨13702035457939636132879733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9134690305293090755253155 13702035457939636132879733)
                    ·
                      refine ⟨1284565824181840887457475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13702035457939636132879733 1284565824181840887457475)
                      ·
                        rfl

theorem cell23_2501683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_2501683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501683 prefixEnd_2501683 := by exact prefixLift 2501683
  have htrace : WordTrace (prefixWord ++ tailWord_2501683) baseStart_2501683 baseEnd_2501683 := by
    simpa [prefixWord, tailWord_2501683, baseEnd_2501683] using wordTrace_append hprefix tailTrace_2501683
  have hstable : (prefixWord ++ tailWord_2501683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501683).length < 2 ^ (prefixWord ++ tailWord_2501683).sum := by decide
  have hdescent : baseEnd_2501683 < baseStart_2501683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501710 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2501710 : Nat := 118140960795 + 2501710 * 2 ^ 59
def prefixEnd_2501710 : Nat := 4983230072969 + 3 ^ 40 * 2501710 * 2
def baseEnd_2501710 : Nat := 1284579688159512281819851

theorem tailTrace_2501710 : CollatzResearch.WordTrace tailWord_2501710 prefixEnd_2501710 1284579688159512281819851 := by
  unfold tailWord_2501710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405607470842425362169823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60829906511159601931572389 11405607470842425362169823)
  ·
    refine ⟨17108411206263638043254735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405607470842425362169823 17108411206263638043254735)
    ·
      refine ⟨25662616809395457064882103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17108411206263638043254735 25662616809395457064882103)
      ·
        refine ⟨38493925214093185597323155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25662616809395457064882103 38493925214093185597323155)
        ·
          refine ⟨57740887821139778395984733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38493925214093185597323155 57740887821139778395984733)
          ·
            refine ⟨21652832932927416898494275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57740887821139778395984733 21652832932927416898494275)
            ·
              refine ⟨32479249399391125347741413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21652832932927416898494275 32479249399391125347741413)
              ·
                refine ⟨6089859262385836002701515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32479249399391125347741413 6089859262385836002701515)
                ·
                  refine ⟨9134788893578754004052273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089859262385836002701515 9134788893578754004052273)
                  ·
                    refine ⟨6851091670184065503039205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9134788893578754004052273 6851091670184065503039205)
                    ·
                      refine ⟨1284579688159512281819851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6851091670184065503039205 1284579688159512281819851)
                      ·
                        rfl

theorem cell23_2501710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2501710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501710 prefixEnd_2501710 := by exact prefixLift 2501710
  have htrace : WordTrace (prefixWord ++ tailWord_2501710) baseStart_2501710 baseEnd_2501710 := by
    simpa [prefixWord, tailWord_2501710, baseEnd_2501710] using wordTrace_append hprefix tailTrace_2501710
  have hstable : (prefixWord ++ tailWord_2501710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501710).length < 2 ^ (prefixWord ++ tailWord_2501710).sum := by decide
  have hdescent : baseEnd_2501710 < baseStart_2501710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501714 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_2501714 : Nat := 118140960795 + 2501714 * 2 ^ 59
def prefixEnd_2501714 : Nat := 4983230072969 + 3 ^ 40 * 2501714 * 2
def baseEnd_2501714 : Nat := 1284581742082130266169833

theorem tailTrace_2501714 : CollatzResearch.WordTrace tailWord_2501714 prefixEnd_2501714 1284581742082130266169833 := by
  unfold tailWord_2501714
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811251414681227895126049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60830003772483274387002797 22811251414681227895126049)
  ·
    refine ⟨17108438561010920921344537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22811251414681227895126049 17108438561010920921344537)
    ·
      refine ⟨12831328920758190691008403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17108438561010920921344537 12831328920758190691008403)
      ·
        refine ⟨19246993381137286036512605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12831328920758190691008403 19246993381137286036512605)
        ·
          refine ⟨7217622517926482263692227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19246993381137286036512605 7217622517926482263692227)
          ·
            refine ⟨10826433776889723395538341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7217622517926482263692227 10826433776889723395538341)
            ·
              refine ⟨2029956333166823136663439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10826433776889723395538341 2029956333166823136663439)
              ·
                refine ⟨3044934499750234704995159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029956333166823136663439 3044934499750234704995159)
                ·
                  refine ⟨4567401749625352057492739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044934499750234704995159 4567401749625352057492739)
                  ·
                    refine ⟨6851102624438028086239109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567401749625352057492739 6851102624438028086239109)
                    ·
                      refine ⟨1284581742082130266169833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6851102624438028086239109 1284581742082130266169833)
                      ·
                        rfl

theorem cell23_2501714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_2501714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501714 prefixEnd_2501714 := by exact prefixLift 2501714
  have htrace : WordTrace (prefixWord ++ tailWord_2501714) baseStart_2501714 baseEnd_2501714 := by
    simpa [prefixWord, tailWord_2501714, baseEnd_2501714] using wordTrace_append hprefix tailTrace_2501714
  have hstable : (prefixWord ++ tailWord_2501714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501714).length < 2 ^ (prefixWord ++ tailWord_2501714).sum := by decide
  have hdescent : baseEnd_2501714 < baseStart_2501714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501717 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2501717 : Nat := 118140960795 + 2501717 * 2 ^ 59
def prefixEnd_2501717 : Nat := 4983230072969 + 3 ^ 40 * 2501717 * 2
def baseEnd_2501717 : Nat := 1284583282524093754432319

theorem tailTrace_2501717 : CollatzResearch.WordTrace tailWord_2501717 prefixEnd_2501717 1284583282524093754432319 := by
  unfold tailWord_2501717
  simp only [CollatzResearch.WordTrace]
  refine ⟨91245115077714043092863405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60830076718476028728575603 91245115077714043092863405)
  ·
    refine ⟨34216918154142766159823777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91245115077714043092863405 34216918154142766159823777)
    ·
      refine ⟨25662688615607074619867833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34216918154142766159823777 25662688615607074619867833)
      ·
        refine ⟨19247016461705305964900875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25662688615607074619867833 19247016461705305964900875)
        ·
          refine ⟨28870524692557958947351313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19247016461705305964900875 28870524692557958947351313)
          ·
            refine ⟨21652893519418469210513485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28870524692557958947351313 21652893519418469210513485)
            ·
              refine ⟨8119835069781925953942557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21652893519418469210513485 8119835069781925953942557)
              ·
                refine ⟨3044938151168222232728459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8119835069781925953942557 3044938151168222232728459)
                ·
                  refine ⟨4567407226752333349092689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044938151168222232728459 4567407226752333349092689)
                  ·
                    refine ⟨3425555420064250011819517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567407226752333349092689 3425555420064250011819517)
                    ·
                      refine ⟨1284583282524093754432319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425555420064250011819517 1284583282524093754432319)
                      ·
                        rfl

theorem cell23_2501717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2501717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501717 prefixEnd_2501717 := by exact prefixLift 2501717
  have htrace : WordTrace (prefixWord ++ tailWord_2501717) baseStart_2501717 baseEnd_2501717 := by
    simpa [prefixWord, tailWord_2501717, baseEnd_2501717] using wordTrace_append hprefix tailTrace_2501717
  have hstable : (prefixWord ++ tailWord_2501717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501717).length < 2 ^ (prefixWord ++ tailWord_2501717).sum := by decide
  have hdescent : baseEnd_2501717 < baseStart_2501717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501765 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_2501765 : Nat := 118140960795 + 2501765 * 2 ^ 59
def prefixEnd_2501765 : Nat := 4983230072969 + 3 ^ 40 * 2501765 * 2
def baseEnd_2501765 : Nat := 1284607929595509566632099

theorem tailTrace_2501765 : CollatzResearch.WordTrace tailWord_2501765 prefixEnd_2501765 1284607929595509566632099 := by
  unfold tailWord_2501765
  simp only [CollatzResearch.WordTrace]
  refine ⟨91246865781540147290610749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60831243854360098193740499 91246865781540147290610749)
  ·
    refine ⟨34217574668077555233979031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91246865781540147290610749 34217574668077555233979031)
    ·
      refine ⟨51326362002116332850968547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34217574668077555233979031 51326362002116332850968547)
      ·
        refine ⟨76989543003174499276452821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51326362002116332850968547 76989543003174499276452821)
        ·
          refine ⟨1804442414136902326791863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76989543003174499276452821 1804442414136902326791863)
          ·
            refine ⟨2706663621205353490187795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804442414136902326791863 2706663621205353490187795)
            ·
              refine ⟨4059995431808030235281693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706663621205353490187795 4059995431808030235281693)
              ·
                refine ⟨1522498286928011338230635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059995431808030235281693 1522498286928011338230635)
                ·
                  refine ⟨2283747430392017007345953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522498286928011338230635 2283747430392017007345953)
                  ·
                    refine ⟨1712810572794012755509465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283747430392017007345953 1712810572794012755509465)
                    ·
                      refine ⟨1284607929595509566632099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712810572794012755509465 1284607929595509566632099)
                      ·
                        rfl

theorem cell23_2501765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_2501765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501765 prefixEnd_2501765 := by exact prefixLift 2501765
  have htrace : WordTrace (prefixWord ++ tailWord_2501765) baseStart_2501765 baseEnd_2501765 := by
    simpa [prefixWord, tailWord_2501765, baseEnd_2501765] using wordTrace_append hprefix tailTrace_2501765
  have hstable : (prefixWord ++ tailWord_2501765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501765).length < 2 ^ (prefixWord ++ tailWord_2501765).sum := by decide
  have hdescent : baseEnd_2501765 < baseStart_2501765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501838 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_2501838 : Nat := 118140960795 + 2501838 * 2 ^ 59
def prefixEnd_2501838 : Nat := 4983230072969 + 3 ^ 40 * 2501838 * 2
def baseEnd_2501838 : Nat := 1284645413683287781019263

theorem tailTrace_2501838 : CollatzResearch.WordTrace tailWord_2501838 prefixEnd_2501838 1284645413683287781019263 := by
  unfold tailWord_2501838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406191038784460094752271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60833018873517120505345445 11406191038784460094752271)
  ·
    refine ⟨17109286558176690142128407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11406191038784460094752271 17109286558176690142128407)
    ·
      refine ⟨25663929837265035213192611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17109286558176690142128407 25663929837265035213192611)
      ·
        refine ⟨38495894755897552819788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25663929837265035213192611 38495894755897552819788917)
        ·
          refine ⟨3608990133365395576855211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38495894755897552819788917 3608990133365395576855211)
          ·
            refine ⟨5413485200048093365282817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608990133365395576855211 5413485200048093365282817)
            ·
              refine ⟨4060113900036070023962113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413485200048093365282817 4060113900036070023962113)
              ·
                refine ⟨3045085425027052517971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060113900036070023962113 3045085425027052517971585)
                ·
                  refine ⟨2283814068770289388478689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045085425027052517971585 2283814068770289388478689)
                  ·
                    refine ⟨1712860551577717041359017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283814068770289388478689 1712860551577717041359017)
                    ·
                      refine ⟨1284645413683287781019263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712860551577717041359017 1284645413683287781019263)
                      ·
                        rfl

theorem cell23_2501838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_2501838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501838 prefixEnd_2501838 := by exact prefixLift 2501838
  have htrace : WordTrace (prefixWord ++ tailWord_2501838) baseStart_2501838 baseEnd_2501838 := by
    simpa [prefixWord, tailWord_2501838, baseEnd_2501838] using wordTrace_append hprefix tailTrace_2501838
  have hstable : (prefixWord ++ tailWord_2501838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501838).length < 2 ^ (prefixWord ++ tailWord_2501838).sum := by decide
  have hdescent : baseEnd_2501838 < baseStart_2501838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501847 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_2501847 : Nat := 118140960795 + 2501847 * 2 ^ 59
def prefixEnd_2501847 : Nat := 4983230072969 + 3 ^ 40 * 2501847 * 2
def baseEnd_2501847 : Nat := 1284650035009178245806721

theorem tailTrace_2501847 : CollatzResearch.WordTrace tailWord_2501847 prefixEnd_2501847 1284650035009178245806721 := by
  unfold tailWord_2501847
  simp only [CollatzResearch.WordTrace]
  refine ⟨91249856567243075295095795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60833237711495383530063863 91249856567243075295095795)
  ·
    refine ⟨136874784850864612942643693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91249856567243075295095795 136874784850864612942643693)
    ·
      refine ⟨51328044319074229853491385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136874784850864612942643693 51328044319074229853491385)
      ·
        refine ⟨38496033239305672390118539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51328044319074229853491385 38496033239305672390118539)
        ·
          refine ⟨57744049858958508585177809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38496033239305672390118539 57744049858958508585177809)
          ·
            refine ⟨43308037394218881438883357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57744049858958508585177809 43308037394218881438883357)
            ·
              refine ⟨16240514022832080539581259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43308037394218881438883357 16240514022832080539581259)
              ·
                refine ⟨24360771034248120809371889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16240514022832080539581259 24360771034248120809371889)
                ·
                  refine ⟨18270578275686090607028917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24360771034248120809371889 18270578275686090607028917)
                  ·
                    refine ⟨1712866713345570994408961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18270578275686090607028917 1712866713345570994408961)
                    ·
                      refine ⟨1284650035009178245806721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712866713345570994408961 1284650035009178245806721)
                      ·
                        rfl

theorem cell23_2501847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_2501847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501847 prefixEnd_2501847 := by exact prefixLift 2501847
  have htrace : WordTrace (prefixWord ++ tailWord_2501847) baseStart_2501847 baseEnd_2501847 := by
    simpa [prefixWord, tailWord_2501847, baseEnd_2501847] using wordTrace_append hprefix tailTrace_2501847
  have hstable : (prefixWord ++ tailWord_2501847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501847).length < 2 ^ (prefixWord ++ tailWord_2501847).sum := by decide
  have hdescent : baseEnd_2501847 < baseStart_2501847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501897 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_2501897 : Nat := 118140960795 + 2501897 * 2 ^ 59
def prefixEnd_2501897 : Nat := 4983230072969 + 3 ^ 40 * 2501897 * 2
def baseEnd_2501897 : Nat := 1284675709041903050181491

theorem tailTrace_2501897 : CollatzResearch.WordTrace tailWord_2501897 prefixEnd_2501897 1284675709041903050181491 := by
  unfold tailWord_2501897
  simp only [CollatzResearch.WordTrace]
  refine ⟨91251680217061933834415945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60834453478041289222943963 91251680217061933834415945)
  ·
    refine ⟨68438760162796450375811959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91251680217061933834415945 68438760162796450375811959)
    ·
      refine ⟨102658140244194675563717939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68438760162796450375811959 102658140244194675563717939)
      ·
        refine ⟨153987210366292013345576909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102658140244194675563717939 153987210366292013345576909)
        ·
          refine ⟨57745203887359505004591341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153987210366292013345576909 57745203887359505004591341)
          ·
            refine ⟨21654451457759814376721753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57745203887359505004591341 21654451457759814376721753)
            ·
              refine ⟨16240838593319860782541315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21654451457759814376721753 16240838593319860782541315)
              ·
                refine ⟨24361257889979791173811973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16240838593319860782541315 24361257889979791173811973)
                ·
                  refine ⟨4567735854371210845089745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24361257889979791173811973 4567735854371210845089745)
                  ·
                    refine ⟨3425801890778408133817309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567735854371210845089745 3425801890778408133817309)
                    ·
                      refine ⟨1284675709041903050181491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425801890778408133817309 1284675709041903050181491)
                      ·
                        rfl

theorem cell23_2501897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_2501897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501897 prefixEnd_2501897 := by exact prefixLift 2501897
  have htrace : WordTrace (prefixWord ++ tailWord_2501897) baseStart_2501897 baseEnd_2501897 := by
    simpa [prefixWord, tailWord_2501897, baseEnd_2501897] using wordTrace_append hprefix tailTrace_2501897
  have hstable : (prefixWord ++ tailWord_2501897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501897).length < 2 ^ (prefixWord ++ tailWord_2501897).sum := by decide
  have hdescent : baseEnd_2501897 < baseStart_2501897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501938 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_2501938 : Nat := 118140960795 + 2501938 * 2 ^ 59
def prefixEnd_2501938 : Nat := 4983230072969 + 3 ^ 40 * 2501938 * 2
def baseEnd_2501938 : Nat := 428232253916245796589601

theorem tailTrace_2501938 : CollatzResearch.WordTrace tailWord_2501938 prefixEnd_2501938 428232253916245796589601 := by
  unfold tailWord_2501938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22813293902478349459164617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60835450406608931891105645 22813293902478349459164617)
  ·
    refine ⟨17109970426858762094373463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22813293902478349459164617 17109970426858762094373463)
    ·
      refine ⟨25664955640288143141560195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17109970426858762094373463 25664955640288143141560195)
      ·
        refine ⟨38497433460432214712340293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25664955640288143141560195 38497433460432214712340293)
        ·
          refine ⟨7218268773831040258563805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38497433460432214712340293 7218268773831040258563805)
          ·
            refine ⟨2706850790186640096961427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7218268773831040258563805 2706850790186640096961427)
            ·
              refine ⟨4060276185279960145442141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706850790186640096961427 4060276185279960145442141)
              ·
                refine ⟨1522603569479985054540803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4060276185279960145442141 1522603569479985054540803)
                ·
                  refine ⟨2283905354219977581811205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522603569479985054540803 2283905354219977581811205)
                  ·
                    refine ⟨428232253916245796589601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283905354219977581811205 428232253916245796589601)
                    ·
                      rfl

theorem cell23_2501938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_2501938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501938 prefixEnd_2501938 := by exact prefixLift 2501938
  have htrace : WordTrace (prefixWord ++ tailWord_2501938) baseStart_2501938 baseEnd_2501938 := by
    simpa [prefixWord, tailWord_2501938, baseEnd_2501938] using wordTrace_append hprefix tailTrace_2501938
  have hstable : (prefixWord ++ tailWord_2501938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501938).length < 2 ^ (prefixWord ++ tailWord_2501938).sum := by decide
  have hdescent : baseEnd_2501938 < baseStart_2501938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501961 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 1, 1, 3]
def baseStart_2501961 : Nat := 118140960795 + 2501961 * 2 ^ 59
def prefixEnd_2501961 : Nat := 4983230072969 + 3 ^ 40 * 2501961 * 2
def baseEnd_2501961 : Nat := 1284708571803790799781197

theorem tailTrace_2501961 : CollatzResearch.WordTrace tailWord_2501961 prefixEnd_2501961 1284708571803790799781197 := by
  unfold tailWord_2501961
  simp only [CollatzResearch.WordTrace]
  refine ⟨91254014488830072764745737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60836009659220048509830491 91254014488830072764745737)
  ·
    refine ⟨68440510866622554573559303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91254014488830072764745737 68440510866622554573559303)
    ·
      refine ⟨102660766299933831860338955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68440510866622554573559303 102660766299933831860338955)
      ·
        refine ⟨153991149449900747790508433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102660766299933831860338955 153991149449900747790508433)
        ·
          refine ⟨115493362087425560842881325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153991149449900747790508433 115493362087425560842881325)
          ·
            refine ⟨43310010782784585316080497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115493362087425560842881325 43310010782784585316080497)
            ·
              refine ⟨32482508087088438987060373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43310010782784585316080497 32482508087088438987060373)
              ·
                refine ⟨1522617566582270577518455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32482508087088438987060373 1522617566582270577518455)
                ·
                  refine ⟨2283926349873405866277683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522617566582270577518455 2283926349873405866277683)
                  ·
                    refine ⟨3425889524810108799416525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283926349873405866277683 3425889524810108799416525)
                    ·
                      refine ⟨1284708571803790799781197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3425889524810108799416525 1284708571803790799781197)
                      ·
                        rfl

theorem cell23_2501961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 1, 3].length) (baseStart_2501961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501961 prefixEnd_2501961 := by exact prefixLift 2501961
  have htrace : WordTrace (prefixWord ++ tailWord_2501961) baseStart_2501961 baseEnd_2501961 := by
    simpa [prefixWord, tailWord_2501961, baseEnd_2501961] using wordTrace_append hprefix tailTrace_2501961
  have hstable : (prefixWord ++ tailWord_2501961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501961).length < 2 ^ (prefixWord ++ tailWord_2501961).sum := by decide
  have hdescent : baseEnd_2501961 < baseStart_2501961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501984 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2501984 : Nat := 118140960795 + 2501984 * 2 ^ 59
def prefixEnd_2501984 : Nat := 4983230072969 + 3 ^ 40 * 2501984 * 2
def baseEnd_2501984 : Nat := 1284720381858844209793591

theorem tailTrace_2501984 : CollatzResearch.WordTrace tailWord_2501984 prefixEnd_2501984 1284720381858844209793591 := by
  unfold tailWord_2501984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45627426683873373846416503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60836568911831165128555337 45627426683873373846416503)
  ·
    refine ⟨68441140025810060769624755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45627426683873373846416503 68441140025810060769624755)
    ·
      refine ⟨102661710038715091154437133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68441140025810060769624755 102661710038715091154437133)
      ·
        refine ⟨38498141264518159182913925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102661710038715091154437133 38498141264518159182913925)
        ·
          refine ⟨7218401487097154846796361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38498141264518159182913925 7218401487097154846796361)
          ·
            refine ⟨5413801115322866135097271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7218401487097154846796361 5413801115322866135097271)
            ·
              refine ⟨8120701672984299202645907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413801115322866135097271 8120701672984299202645907)
              ·
                refine ⟨12181052509476448803968861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8120701672984299202645907 12181052509476448803968861)
                ·
                  refine ⟨4567894691053668301488323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12181052509476448803968861 4567894691053668301488323)
                  ·
                    refine ⟨6851842036580502452232485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567894691053668301488323 6851842036580502452232485)
                    ·
                      refine ⟨1284720381858844209793591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6851842036580502452232485 1284720381858844209793591)
                      ·
                        rfl

theorem cell23_2501984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2501984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501984 prefixEnd_2501984 := by exact prefixLift 2501984
  have htrace : WordTrace (prefixWord ++ tailWord_2501984) baseStart_2501984 baseEnd_2501984 := by
    simpa [prefixWord, tailWord_2501984, baseEnd_2501984] using wordTrace_append hprefix tailTrace_2501984
  have hstable : (prefixWord ++ tailWord_2501984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501984).length < 2 ^ (prefixWord ++ tailWord_2501984).sum := by decide
  have hdescent : baseEnd_2501984 < baseStart_2501984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502024 : List Nat := [2, 1, 3, 3, 1, 4, 1, 8]
def baseStart_2502024 : Nat := 118140960795 + 2502024 * 2 ^ 59
def prefixEnd_2502024 : Nat := 4983230072969 + 3 ^ 40 * 2502024 * 2
def baseEnd_2502024 : Nat := 47582997077223113084941

theorem tailTrace_2502024 : CollatzResearch.WordTrace tailWord_2502024 prefixEnd_2502024 47582997077223113084941 := by
  unfold tailWord_2502024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45628156143800917262144563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60837541525067889682859417 45628156143800917262144563)
  ·
    refine ⟨68442234215701375893216845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45628156143800917262144563 68442234215701375893216845)
    ·
      refine ⟨25665837830888015959956317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68442234215701375893216845 25665837830888015959956317)
      ·
        refine ⟨9624689186583005984983619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25665837830888015959956317 9624689186583005984983619)
        ·
          refine ⟨14437033779874508977475429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9624689186583005984983619 14437033779874508977475429)
          ·
            refine ⟨2706943833726470433276643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14437033779874508977475429 2706943833726470433276643)
            ·
              refine ⟨4060415750589705649914965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706943833726470433276643 4060415750589705649914965)
              ·
                refine ⟨47582997077223113084941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4060415750589705649914965 47582997077223113084941)
                ·
                  rfl

theorem cell23_2502024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 8].length) (baseStart_2502024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502024 prefixEnd_2502024 := by exact prefixLift 2502024
  have htrace : WordTrace (prefixWord ++ tailWord_2502024) baseStart_2502024 baseEnd_2502024 := by
    simpa [prefixWord, tailWord_2502024, baseEnd_2502024] using wordTrace_append hprefix tailTrace_2502024
  have hstable : (prefixWord ++ tailWord_2502024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502024).length < 2 ^ (prefixWord ++ tailWord_2502024).sum := by decide
  have hdescent : baseEnd_2502024 < baseStart_2502024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502074 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_2502074 : Nat := 118140960795 + 2502074 * 2 ^ 59
def prefixEnd_2502074 : Nat := 4983230072969 + 3 ^ 40 * 2502074 * 2
def baseEnd_2502074 : Nat := 1284766595117748857668177

theorem tailTrace_2502074 : CollatzResearch.WordTrace tailWord_2502074 prefixEnd_2502074 1284766595117748857668177 := by
  unfold tailWord_2502074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22814533984355173265902319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60838757291613795375739517 22814533984355173265902319)
  ·
    refine ⟨34221800976532759898853479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22814533984355173265902319 34221800976532759898853479)
    ·
      refine ⟨51332701464799139848280219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34221800976532759898853479 51332701464799139848280219)
      ·
        refine ⟨76999052197198709772420329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51332701464799139848280219 76999052197198709772420329)
        ·
          refine ⟨57749289147899032329315247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76999052197198709772420329 57749289147899032329315247)
          ·
            refine ⟨86623933721848548493972871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57749289147899032329315247 86623933721848548493972871)
            ·
              refine ⟨129935900582772822740959307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86623933721848548493972871 129935900582772822740959307)
              ·
                refine ⟨194903850874159234111438961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129935900582772822740959307 194903850874159234111438961)
                ·
                  refine ⟨146177888155619425583579221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194903850874159234111438961 146177888155619425583579221)
                  ·
                    refine ⟨1713022126823665143557569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 146177888155619425583579221 1713022126823665143557569)
                    ·
                      refine ⟨1284766595117748857668177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713022126823665143557569 1284766595117748857668177)
                      ·
                        rfl

theorem cell23_2502074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_2502074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502074 prefixEnd_2502074 := by exact prefixLift 2502074
  have htrace : WordTrace (prefixWord ++ tailWord_2502074) baseStart_2502074 baseEnd_2502074 := by
    simpa [prefixWord, tailWord_2502074, baseEnd_2502074] using wordTrace_append hprefix tailTrace_2502074
  have hstable : (prefixWord ++ tailWord_2502074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502074).length < 2 ^ (prefixWord ++ tailWord_2502074).sum := by decide
  have hdescent : baseEnd_2502074 < baseStart_2502074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502091 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 4, 2]
def baseStart_2502091 : Nat := 118140960795 + 2502091 * 2 ^ 59
def prefixEnd_2502091 : Nat := 4983230072969 + 3 ^ 40 * 2502091 * 2
def baseEnd_2502091 : Nat := 1284775324288875291155599

theorem tailTrace_2502091 : CollatzResearch.WordTrace tailWord_2502091 prefixEnd_2502091 1284775324288875291155599 := by
  unfold tailWord_2502091
  simp only [CollatzResearch.WordTrace]
  refine ⟨91258755978359104966978127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60839170652239403311318751 91258755978359104966978127)
  ·
    refine ⟨136888133967538657450467191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91258755978359104966978127 136888133967538657450467191)
    ·
      refine ⟨205332200951307986175700787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136888133967538657450467191 205332200951307986175700787)
      ·
        refine ⟨307998301426961979263551181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205332200951307986175700787 307998301426961979263551181)
        ·
          refine ⟨115499363035110742223831693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307998301426961979263551181 115499363035110742223831693)
          ·
            refine ⟨43312261138166528333936885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115499363035110742223831693 43312261138166528333936885)
            ·
              refine ⟨4060524481703112031306583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43312261138166528333936885 4060524481703112031306583)
              ·
                refine ⟨6090786722554668046959875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060524481703112031306583 6090786722554668046959875)
                ·
                  refine ⟨9136180083832002070439813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6090786722554668046959875 9136180083832002070439813)
                  ·
                    refine ⟨1713033765718500388207465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9136180083832002070439813 1713033765718500388207465)
                    ·
                      refine ⟨1284775324288875291155599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713033765718500388207465 1284775324288875291155599)
                      ·
                        rfl

theorem cell23_2502091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4, 2].length) (baseStart_2502091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502091 prefixEnd_2502091 := by exact prefixLift 2502091
  have htrace : WordTrace (prefixWord ++ tailWord_2502091) baseStart_2502091 baseEnd_2502091 := by
    simpa [prefixWord, tailWord_2502091, baseEnd_2502091] using wordTrace_append hprefix tailTrace_2502091
  have hstable : (prefixWord ++ tailWord_2502091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502091).length < 2 ^ (prefixWord ++ tailWord_2502091).sum := by decide
  have hdescent : baseEnd_2502091 < baseStart_2502091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502094 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2502094 : Nat := 118140960795 + 2502094 * 2 ^ 59
def prefixEnd_2502094 : Nat := 4983230072969 + 3 ^ 40 * 2502094 * 2
def baseEnd_2502094 : Nat := 1284776864730838779418085

theorem tailTrace_2502094 : CollatzResearch.WordTrace tailWord_2502094 prefixEnd_2502094 1284776864730838779418085 := by
  unfold tailWord_2502094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11407358174668529559917167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60839243598232157652891557 11407358174668529559917167)
  ·
    refine ⟨17111037262002794339875751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11407358174668529559917167 17111037262002794339875751)
    ·
      refine ⟨25666555893004191509813627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17111037262002794339875751 25666555893004191509813627)
      ·
        refine ⟨38499833839506287264720441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25666555893004191509813627 38499833839506287264720441)
        ·
          refine ⟨28874875379629715448540331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38499833839506287264720441 28874875379629715448540331)
          ·
            refine ⟨43312313069444573172810497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28874875379629715448540331 43312313069444573172810497)
            ·
              refine ⟨32484234802083429879607873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43312313069444573172810497 32484234802083429879607873)
              ·
                refine ⟨24363176101562572409705905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32484234802083429879607873 24363176101562572409705905)
                ·
                  refine ⟨18272382076171929307279429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24363176101562572409705905 18272382076171929307279429)
                  ·
                    refine ⟨3426071639282236745114893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18272382076171929307279429 3426071639282236745114893)
                    ·
                      refine ⟨1284776864730838779418085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426071639282236745114893 1284776864730838779418085)
                      ·
                        rfl

theorem cell23_2502094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2502094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502094 prefixEnd_2502094 := by exact prefixLift 2502094
  have htrace : WordTrace (prefixWord ++ tailWord_2502094) baseStart_2502094 baseEnd_2502094 := by
    simpa [prefixWord, tailWord_2502094, baseEnd_2502094] using wordTrace_append hprefix tailTrace_2502094
  have hstable : (prefixWord ++ tailWord_2502094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502094).length < 2 ^ (prefixWord ++ tailWord_2502094).sum := by decide
  have hdescent : baseEnd_2502094 < baseStart_2502094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502124 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2502124 : Nat := 118140960795 + 2502124 * 2 ^ 59
def prefixEnd_2502124 : Nat := 4983230072969 + 3 ^ 40 * 2502124 * 2
def baseEnd_2502124 : Nat := 1284792269150473662042947

theorem tailTrace_2502124 : CollatzResearch.WordTrace tailWord_2502124 prefixEnd_2502124 1284792269150473662042947 := by
  unfold tailWord_2502124
  simp only [CollatzResearch.WordTrace]
  refine ⟨45629979793619775801464713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60839973058159701068619617 45629979793619775801464713)
  ·
    refine ⟨34222484845214831851098535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45629979793619775801464713 34222484845214831851098535)
    ·
      refine ⟨51333727267822247776647803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34222484845214831851098535 51333727267822247776647803)
      ·
        refine ⟨77000590901733371664971705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51333727267822247776647803 77000590901733371664971705)
        ·
          refine ⟨57750443176300028748728779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77000590901733371664971705 57750443176300028748728779)
          ·
            refine ⟨86625664764450043123093169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57750443176300028748728779 86625664764450043123093169)
            ·
              refine ⟨64969248573337532342319877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86625664764450043123093169 64969248573337532342319877)
              ·
                refine ⟨12181734107500787314184977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64969248573337532342319877 12181734107500787314184977)
                ·
                  refine ⟨9136300580625590485638733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12181734107500787314184977 9136300580625590485638733)
                  ·
                    refine ⟨3426112717734596432114525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9136300580625590485638733 3426112717734596432114525)
                    ·
                      refine ⟨1284792269150473662042947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426112717734596432114525 1284792269150473662042947)
                      ·
                        rfl

theorem cell23_2502124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2502124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502124 prefixEnd_2502124 := by exact prefixLift 2502124
  have htrace : WordTrace (prefixWord ++ tailWord_2502124) baseStart_2502124 baseEnd_2502124 := by
    simpa [prefixWord, tailWord_2502124, baseEnd_2502124] using wordTrace_append hprefix tailTrace_2502124
  have hstable : (prefixWord ++ tailWord_2502124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502124).length < 2 ^ (prefixWord ++ tailWord_2502124).sum := by decide
  have hdescent : baseEnd_2502124 < baseStart_2502124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502181 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_2502181 : Nat := 118140960795 + 2502181 * 2 ^ 59
def prefixEnd_2502181 : Nat := 4983230072969 + 3 ^ 40 * 2502181 * 2
def baseEnd_2502181 : Nat := 1284821537547779939030185

theorem tailTrace_2502181 : CollatzResearch.WordTrace tailWord_2502181 prefixEnd_2502181 1284821537547779939030185 := by
  unfold tailWord_2502181
  simp only [CollatzResearch.WordTrace]
  refine ⟨91262038548033050337754397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60841359032022033558502931 91262038548033050337754397)
  ·
    refine ⟨34223264455512393876657899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91262038548033050337754397 34223264455512393876657899)
    ·
      refine ⟨51334896683268590814986849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34223264455512393876657899 51334896683268590814986849)
      ·
        refine ⟨38501172512451443111240137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51334896683268590814986849 38501172512451443111240137)
        ·
          refine ⟨28875879384338582333430103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38501172512451443111240137 28875879384338582333430103)
          ·
            refine ⟨43313819076507873500145155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28875879384338582333430103 43313819076507873500145155)
            ·
              refine ⟨64970728614761810250217733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43313819076507873500145155 64970728614761810250217733)
              ·
                refine ⟨12182011615267839421915825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64970728614761810250217733 12182011615267839421915825)
                ·
                  refine ⟨9136508711450879566436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12182011615267839421915825 9136508711450879566436869)
                  ·
                    refine ⟨1713095383397039918706913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9136508711450879566436869 1713095383397039918706913)
                    ·
                      refine ⟨1284821537547779939030185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713095383397039918706913 1284821537547779939030185)
                      ·
                        rfl

theorem cell23_2502181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_2502181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502181 prefixEnd_2502181 := by exact prefixLift 2502181
  have htrace : WordTrace (prefixWord ++ tailWord_2502181) baseStart_2502181 baseEnd_2502181 := by
    simpa [prefixWord, tailWord_2502181, baseEnd_2502181] using wordTrace_append hprefix tailTrace_2502181
  have hstable : (prefixWord ++ tailWord_2502181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502181).length < 2 ^ (prefixWord ++ tailWord_2502181).sum := by decide
  have hdescent : baseEnd_2502181 < baseStart_2502181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502194 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2502194 : Nat := 118140960795 + 2502194 * 2 ^ 59
def prefixEnd_2502194 : Nat := 4983230072969 + 3 ^ 40 * 2502194 * 2
def baseEnd_2502194 : Nat := 1284828212796288388167625

theorem tailTrace_2502194 : CollatzResearch.WordTrace tailWord_2502194 prefixEnd_2502194 1284828212796288388167625 := by
  unfold tailWord_2502194
  simp only [CollatzResearch.WordTrace]
  refine ⟨22815628174246488389494409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60841675131323969038651757 22815628174246488389494409)
  ·
    refine ⟨17111721130684866292120807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22815628174246488389494409 17111721130684866292120807)
    ·
      refine ⟨25667581696027299438181211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17111721130684866292120807 25667581696027299438181211)
      ·
        refine ⟨38501372544040949157271817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25667581696027299438181211 38501372544040949157271817)
        ·
          refine ⟨28876029408030711867953863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38501372544040949157271817 28876029408030711867953863)
          ·
            refine ⟨43314044112046067801930795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28876029408030711867953863 43314044112046067801930795)
            ·
              refine ⟨64971066168069101702896193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43314044112046067801930795 64971066168069101702896193)
              ·
                refine ⟨48728299626051826277172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64971066168069101702896193 48728299626051826277172145)
                ·
                  refine ⟨36546224719538869707879109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48728299626051826277172145 36546224719538869707879109)
                  ·
                    refine ⟨6852417134913538070227333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36546224719538869707879109 6852417134913538070227333)
                    ·
                      refine ⟨1284828212796288388167625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6852417134913538070227333 1284828212796288388167625)
                      ·
                        rfl

theorem cell23_2502194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2502194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502194 prefixEnd_2502194 := by exact prefixLift 2502194
  have htrace : WordTrace (prefixWord ++ tailWord_2502194) baseStart_2502194 baseEnd_2502194 := by
    simpa [prefixWord, tailWord_2502194, baseEnd_2502194] using wordTrace_append hprefix tailTrace_2502194
  have hstable : (prefixWord ++ tailWord_2502194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502194).length < 2 ^ (prefixWord ++ tailWord_2502194).sum := by decide
  have hdescent : baseEnd_2502194 < baseStart_2502194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502215 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_2502215 : Nat := 118140960795 + 2502215 * 2 ^ 59
def prefixEnd_2502215 : Nat := 4983230072969 + 3 ^ 40 * 2502215 * 2
def baseEnd_2502215 : Nat := 1284838995890032806005029

theorem tailTrace_2502215 : CollatzResearch.WordTrace tailWord_2502215 prefixEnd_2502215 1284838995890032806005029 := by
  unfold tailWord_2502215
  simp only [CollatzResearch.WordTrace]
  refine ⟨91263278629909874144492099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60842185753273249429661399 91263278629909874144492099)
  ·
    refine ⟨136894917944864811216738149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91263278629909874144492099 136894917944864811216738149)
    ·
      refine ⟨25667797114662152103138403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136894917944864811216738149 25667797114662152103138403)
      ·
        refine ⟨38501695671993228154707605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25667797114662152103138403 38501695671993228154707605)
        ·
          refine ⟨1804766984624682569751919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38501695671993228154707605 1804766984624682569751919)
          ·
            refine ⟨2707150476937023854627879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804766984624682569751919 2707150476937023854627879)
            ·
              refine ⟨4060725715405535781941819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707150476937023854627879 4060725715405535781941819)
              ·
                refine ⟨6091088573108303672912729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060725715405535781941819 6091088573108303672912729)
                ·
                  refine ⟨4568316429831227754684547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6091088573108303672912729 4568316429831227754684547)
                  ·
                    refine ⟨6852474644746841632026821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568316429831227754684547 6852474644746841632026821)
                    ·
                      refine ⟨1284838995890032806005029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6852474644746841632026821 1284838995890032806005029)
                      ·
                        rfl

theorem cell23_2502215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_2502215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502215 prefixEnd_2502215 := by exact prefixLift 2502215
  have htrace : WordTrace (prefixWord ++ tailWord_2502215) baseStart_2502215 baseEnd_2502215 := by
    simpa [prefixWord, tailWord_2502215, baseEnd_2502215] using wordTrace_append hprefix tailTrace_2502215
  have hstable : (prefixWord ++ tailWord_2502215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502215).length < 2 ^ (prefixWord ++ tailWord_2502215).sum := by decide
  have hdescent : baseEnd_2502215 < baseStart_2502215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502258 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_2502258 : Nat := 118140960795 + 2502258 * 2 ^ 59
def prefixEnd_2502258 : Nat := 4983230072969 + 3 ^ 40 * 2502258 * 2
def baseEnd_2502258 : Nat := 1284861075558176137767331

theorem tailTrace_2502258 : CollatzResearch.WordTrace tailWord_2502258 prefixEnd_2502258 1284861075558176137767331 := by
  unfold tailWord_2502258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816211742188523122076857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60843231312502728325538285 22816211742188523122076857)
  ·
    refine ⟨17112158806641392341557643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22816211742188523122076857 17112158806641392341557643)
    ·
      refine ⟨25668238209962088512336465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17112158806641392341557643 25668238209962088512336465)
      ·
        refine ⟨19251178657471566384252349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25668238209962088512336465 19251178657471566384252349)
        ·
          refine ⟨7219191996551837394094631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19251178657471566384252349 7219191996551837394094631)
          ·
            refine ⟨10828787994827756091141947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219191996551837394094631 10828787994827756091141947)
            ·
              refine ⟨16243181992241634136712921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10828787994827756091141947 16243181992241634136712921)
              ·
                refine ⟨12182386494181225602534691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16243181992241634136712921 12182386494181225602534691)
                ·
                  refine ⟨18273579741271838403802037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12182386494181225602534691 18273579741271838403802037)
                  ·
                    refine ⟨1713148100744234850356441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18273579741271838403802037 1713148100744234850356441)
                    ·
                      refine ⟨1284861075558176137767331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713148100744234850356441 1284861075558176137767331)
                      ·
                        rfl

theorem cell23_2502258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_2502258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502258 prefixEnd_2502258 := by exact prefixLift 2502258
  have htrace : WordTrace (prefixWord ++ tailWord_2502258) baseStart_2502258 baseEnd_2502258 := by
    simpa [prefixWord, tailWord_2502258, baseEnd_2502258] using wordTrace_append hprefix tailTrace_2502258
  have hstable : (prefixWord ++ tailWord_2502258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502258).length < 2 ^ (prefixWord ++ tailWord_2502258).sum := by decide
  have hdescent : baseEnd_2502258 < baseStart_2502258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502281 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_2502281 : Nat := 118140960795 + 2502281 * 2 ^ 59
def prefixEnd_2502281 : Nat := 4983230072969 + 3 ^ 40 * 2502281 * 2
def baseEnd_2502281 : Nat := 428290961871076515926575

theorem tailTrace_2502281 : CollatzResearch.WordTrace tailWord_2502281 prefixEnd_2502281 428290961871076515926575 := by
  unfold tailWord_2502281
  simp only [CollatzResearch.WordTrace]
  refine ⟨91265685847670767416394697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60843790565113844944263131 91265685847670767416394697)
  ·
    refine ⟨68449264385753075562296023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91265685847670767416394697 68449264385753075562296023)
    ·
      refine ⟨102673896578629613343444035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68449264385753075562296023 102673896578629613343444035)
      ·
        refine ⟨154010844867944420015166053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102673896578629613343444035 154010844867944420015166053)
        ·
          refine ⟨28877033412739578752843635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154010844867944420015166053 28877033412739578752843635)
          ·
            refine ⟨43315550119109368129265453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28877033412739578752843635 43315550119109368129265453)
            ·
              refine ⟨16243331294666013048474545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43315550119109368129265453 16243331294666013048474545)
              ·
                refine ⟨12182498470999509786355909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16243331294666013048474545 12182498470999509786355909)
                ·
                  refine ⟨2284218463312408084941733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12182498470999509786355909 2284218463312408084941733)
                  ·
                    refine ⟨428290961871076515926575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2284218463312408084941733 428290961871076515926575)
                    ·
                      rfl

theorem cell23_2502281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_2502281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502281 prefixEnd_2502281 := by exact prefixLift 2502281
  have htrace : WordTrace (prefixWord ++ tailWord_2502281) baseStart_2502281 baseEnd_2502281 := by
    simpa [prefixWord, tailWord_2502281, baseEnd_2502281] using wordTrace_append hprefix tailTrace_2502281
  have hstable : (prefixWord ++ tailWord_2502281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502281).length < 2 ^ (prefixWord ++ tailWord_2502281).sum := by decide
  have hdescent : baseEnd_2502281 < baseStart_2502281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502282 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_2502282 : Nat := 118140960795 + 2502282 * 2 ^ 59
def prefixEnd_2502282 : Nat := 4983230072969 + 3 ^ 40 * 2502282 * 2
def baseEnd_2502282 : Nat := 1284873399093884043867221

theorem tailTrace_2502282 : CollatzResearch.WordTrace tailWord_2502282 prefixEnd_2502282 1284873399093884043867221 := by
  unfold tailWord_2502282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816430580166786146795275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60843814880444763058120733 22816430580166786146795275)
  ·
    refine ⟨34224645870250179220192913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22816430580166786146795275 34224645870250179220192913)
    ·
      refine ⟨25668484402687634415144685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34224645870250179220192913 25668484402687634415144685)
      ·
        refine ⟨9625681651007862905679257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25668484402687634415144685 9625681651007862905679257)
        ·
          refine ⟨7219261238255897179259443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9625681651007862905679257 7219261238255897179259443)
          ·
            refine ⟨10828891857383845768889165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219261238255897179259443 10828891857383845768889165)
            ·
              refine ⟨4060834446518942163333437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10828891857383845768889165 4060834446518942163333437)
              ·
                refine ⟨1522812917444603311250039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4060834446518942163333437 1522812917444603311250039)
                ·
                  refine ⟨2284219376166904966875059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522812917444603311250039 2284219376166904966875059)
                  ·
                    refine ⟨3426329064250357450312589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284219376166904966875059 3426329064250357450312589)
                    ·
                      refine ⟨1284873399093884043867221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426329064250357450312589 1284873399093884043867221)
                      ·
                        rfl

theorem cell23_2502282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_2502282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502282 prefixEnd_2502282 := by exact prefixLift 2502282
  have htrace : WordTrace (prefixWord ++ tailWord_2502282) baseStart_2502282 baseEnd_2502282 := by
    simpa [prefixWord, tailWord_2502282, baseEnd_2502282] using wordTrace_append hprefix tailTrace_2502282
  have hstable : (prefixWord ++ tailWord_2502282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502282).length < 2 ^ (prefixWord ++ tailWord_2502282).sum := by decide
  have hdescent : baseEnd_2502282 < baseStart_2502282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502288 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2]
def baseStart_2502288 : Nat := 118140960795 + 2502288 * 2 ^ 59
def prefixEnd_2502288 : Nat := 4983230072969 + 3 ^ 40 * 2502288 * 2
def baseEnd_2502288 : Nat := 1284876479977811020392193

theorem tailTrace_2502288 : CollatzResearch.WordTrace tailWord_2502288 prefixEnd_2502288 1284876479977811020392193 := by
  unfold tailWord_2502288
  simp only [CollatzResearch.WordTrace]
  refine ⟨45632970579322703805949759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60843960772430271741266345 45632970579322703805949759)
  ·
    refine ⟨68449455868984055708924639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45632970579322703805949759 68449455868984055708924639)
    ·
      refine ⟨102674183803476083563386959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68449455868984055708924639 102674183803476083563386959)
      ·
        refine ⟨154011275705214125345080439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102674183803476083563386959 154011275705214125345080439)
        ·
          refine ⟨231016913557821188017620659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154011275705214125345080439 231016913557821188017620659)
          ·
            refine ⟨346525370336731782026430989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231016913557821188017620659 346525370336731782026430989)
            ·
              refine ⟨129947013876274418259911621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346525370336731782026430989 129947013876274418259911621)
              ·
                refine ⟨24365065101801453423733429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129947013876274418259911621 24365065101801453423733429)
                ·
                  refine ⟨2284224853293886258475009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24365065101801453423733429 2284224853293886258475009)
                  ·
                    refine ⟨1713168639970414693856257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284224853293886258475009 1713168639970414693856257)
                    ·
                      refine ⟨1284876479977811020392193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713168639970414693856257 1284876479977811020392193)
                      ·
                        rfl

theorem cell23_2502288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2].length) (baseStart_2502288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502288 prefixEnd_2502288 := by exact prefixLift 2502288
  have htrace : WordTrace (prefixWord ++ tailWord_2502288) baseStart_2502288 baseEnd_2502288 := by
    simpa [prefixWord, tailWord_2502288, baseEnd_2502288] using wordTrace_append hprefix tailTrace_2502288
  have hstable : (prefixWord ++ tailWord_2502288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502288).length < 2 ^ (prefixWord ++ tailWord_2502288).sum := by decide
  have hdescent : baseEnd_2502288 < baseStart_2502288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502292 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2502292 : Nat := 118140960795 + 2502292 * 2 ^ 59
def prefixEnd_2502292 : Nat := 4983230072969 + 3 ^ 40 * 2502292 * 2
def baseEnd_2502292 : Nat := 1284878533900429004742175

theorem tailTrace_2502292 : CollatzResearch.WordTrace tailWord_2502292 prefixEnd_2502292 1284878533900429004742175 := by
  unfold tailWord_2502292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45633043525315458147522565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60844058033753944196696753 45633043525315458147522565)
  ·
    refine ⟨8556195660996648402660481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45633043525315458147522565 8556195660996648402660481)
    ·
      refine ⟨6417146745747486301995361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8556195660996648402660481 6417146745747486301995361)
      ·
        refine ⟨4812860059310614726496521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6417146745747486301995361 4812860059310614726496521)
        ·
          refine ⟨3609645044482961044872391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4812860059310614726496521 3609645044482961044872391)
          ·
            refine ⟨5414467566724441567308587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609645044482961044872391 5414467566724441567308587)
            ·
              refine ⟨8121701350086662350962881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414467566724441567308587 8121701350086662350962881)
              ·
                refine ⟨6091276012564996763222161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8121701350086662350962881 6091276012564996763222161)
                ·
                  refine ⟨4568457009423747572416621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6091276012564996763222161 4568457009423747572416621)
                  ·
                    refine ⟨1713171378533905339656233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4568457009423747572416621 1713171378533905339656233)
                    ·
                      refine ⟨1284878533900429004742175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713171378533905339656233 1284878533900429004742175)
                      ·
                        rfl

theorem cell23_2502292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2502292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502292 prefixEnd_2502292 := by exact prefixLift 2502292
  have htrace : WordTrace (prefixWord ++ tailWord_2502292) baseStart_2502292 baseEnd_2502292 := by
    simpa [prefixWord, tailWord_2502292, baseEnd_2502292] using wordTrace_append hprefix tailTrace_2502292
  have hstable : (prefixWord ++ tailWord_2502292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502292).length < 2 ^ (prefixWord ++ tailWord_2502292).sum := by decide
  have hdescent : baseEnd_2502292 < baseStart_2502292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502325 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2502325 : Nat := 118140960795 + 2502325 * 2 ^ 59
def prefixEnd_2502325 : Nat := 4983230072969 + 3 ^ 40 * 2502325 * 2
def baseEnd_2502325 : Nat := 1284895478762027375629523

theorem tailTrace_2502325 : CollatzResearch.WordTrace tailWord_2502325 prefixEnd_2502325 1284895478762027375629523 := by
  unfold tailWord_2502325
  simp only [CollatzResearch.WordTrace]
  refine ⟨91267290659511362930996429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60844860439674241953997619 91267290659511362930996429)
  ·
    refine ⟨34225233997316761099123661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91267290659511362930996429 34225233997316761099123661)
    ·
      refine ⟨12834462748993785412171373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34225233997316761099123661 12834462748993785412171373)
      ·
        refine ⟨4812923530872669529564265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12834462748993785412171373 4812923530872669529564265)
        ·
          refine ⟨3609692648154502147173199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4812923530872669529564265 3609692648154502147173199)
          ·
            refine ⟨5414538972231753220759799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609692648154502147173199 5414538972231753220759799)
            ·
              refine ⟨8121808458347629831139699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414538972231753220759799 8121808458347629831139699)
              ·
                refine ⟨12182712687521444746709549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121808458347629831139699 12182712687521444746709549)
                ·
                  refine ⟨4568517257820541780016081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12182712687521444746709549 4568517257820541780016081)
                  ·
                    refine ⟨3426387943365406335012061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4568517257820541780016081 3426387943365406335012061)
                    ·
                      refine ⟨1284895478762027375629523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426387943365406335012061 1284895478762027375629523)
                      ·
                        rfl

theorem cell23_2502325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2502325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502325 prefixEnd_2502325 := by exact prefixLift 2502325
  have htrace : WordTrace (prefixWord ++ tailWord_2502325) baseStart_2502325 baseEnd_2502325 := by
    simpa [prefixWord, tailWord_2502325, baseEnd_2502325] using wordTrace_append hprefix tailTrace_2502325
  have hstable : (prefixWord ++ tailWord_2502325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502325).length < 2 ^ (prefixWord ++ tailWord_2502325).sum := by decide
  have hdescent : baseEnd_2502325 < baseStart_2502325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502342 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2502342 : Nat := 118140960795 + 2502342 * 2 ^ 59
def prefixEnd_2502342 : Nat := 4983230072969 + 3 ^ 40 * 2502342 * 2
def baseEnd_2502342 : Nat := 1284904207933153809116945

theorem tailTrace_2502342 : CollatzResearch.WordTrace tailWord_2502342 prefixEnd_2502342 1284904207933153809116945 := by
  unfold tailWord_2502342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852122209389055463573915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60845273800299849889576853 2852122209389055463573915)
  ·
    refine ⟨4278183314083583195360873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852122209389055463573915 4278183314083583195360873)
    ·
      refine ⟨3208637485562687396520655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4278183314083583195360873 3208637485562687396520655)
      ·
        refine ⟨4812956228344031094780983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3208637485562687396520655 4812956228344031094780983)
        ·
          refine ⟨7219434342516046642171475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812956228344031094780983 7219434342516046642171475)
          ·
            refine ⟨10829151513774069963257213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219434342516046642171475 10829151513774069963257213)
            ·
              refine ⟨4060931817665276236221455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10829151513774069963257213 4060931817665276236221455)
              ·
                refine ⟨6091397726497914354332183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060931817665276236221455 6091397726497914354332183)
                ·
                  refine ⟨9137096589746871531498275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6091397726497914354332183 9137096589746871531498275)
                  ·
                    refine ⟨13705644884620307297247413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9137096589746871531498275 13705644884620307297247413)
                    ·
                      refine ⟨1284904207933153809116945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13705644884620307297247413 1284904207933153809116945)
                      ·
                        rfl

theorem cell23_2502342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2502342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502342 prefixEnd_2502342 := by exact prefixLift 2502342
  have htrace : WordTrace (prefixWord ++ tailWord_2502342) baseStart_2502342 baseEnd_2502342 := by
    simpa [prefixWord, tailWord_2502342, baseEnd_2502342] using wordTrace_append hprefix tailTrace_2502342
  have hstable : (prefixWord ++ tailWord_2502342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502342).length < 2 ^ (prefixWord ++ tailWord_2502342).sum := by decide
  have hdescent : baseEnd_2502342 < baseStart_2502342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502356 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2502356 : Nat := 118140960795 + 2502356 * 2 ^ 59
def prefixEnd_2502356 : Nat := 4983230072969 + 3 ^ 40 * 2502356 * 2
def baseEnd_2502356 : Nat := 1284911396662316754341881

theorem tailTrace_2502356 : CollatzResearch.WordTrace tailWord_2502356 prefixEnd_2502356 1284911396662316754341881 := by
  unfold tailWord_2502356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45634210661199527612687461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60845614214932703483583281 45634210661199527612687461)
  ·
    refine ⟨8556414498974911427378899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45634210661199527612687461 8556414498974911427378899)
    ·
      refine ⟨12834621748462367141068349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8556414498974911427378899 12834621748462367141068349)
      ·
        refine ⟨4812983155673387677900631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12834621748462367141068349 4812983155673387677900631)
        ·
          refine ⟨7219474733510081516850947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812983155673387677900631 7219474733510081516850947)
          ·
            refine ⟨10829212100265122275276421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219474733510081516850947 10829212100265122275276421)
            ·
              refine ⟨2030477268799710426614329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10829212100265122275276421 2030477268799710426614329)
              ·
                refine ⟨1522857951599782819960747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030477268799710426614329 1522857951599782819960747)
                ·
                  refine ⟨2284286927399674229941121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522857951599782819960747 2284286927399674229941121)
                  ·
                    refine ⟨1713215195549755672455841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284286927399674229941121 1713215195549755672455841)
                    ·
                      refine ⟨1284911396662316754341881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713215195549755672455841 1284911396662316754341881)
                      ·
                        rfl

theorem cell23_2502356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2502356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502356 prefixEnd_2502356 := by exact prefixLift 2502356
  have htrace : WordTrace (prefixWord ++ tailWord_2502356) baseStart_2502356 baseEnd_2502356 := by
    simpa [prefixWord, tailWord_2502356, baseEnd_2502356] using wordTrace_append hprefix tailTrace_2502356
  have hstable : (prefixWord ++ tailWord_2502356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502356).length < 2 ^ (prefixWord ++ tailWord_2502356).sum := by decide
  have hdescent : baseEnd_2502356 < baseStart_2502356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502361 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2502361 : Nat := 118140960795 + 2502361 * 2 ^ 59
def prefixEnd_2502361 : Nat := 4983230072969 + 3 ^ 40 * 2502361 * 2
def baseEnd_2502361 : Nat := 1284913964065589234779357

theorem tailTrace_2502361 : CollatzResearch.WordTrace tailWord_2502361 prefixEnd_2502361 1284913964065589234779357 := by
  unfold tailWord_2502361
  simp only [CollatzResearch.WordTrace]
  refine ⟨91268603687380941079306937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60845735791587294052871291 91268603687380941079306937)
  ·
    refine ⟨68451452765535705809480203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91268603687380941079306937 68451452765535705809480203)
    ·
      refine ⟨102677179148303558714220305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68451452765535705809480203 102677179148303558714220305)
      ·
        refine ⟨77007884361227669035665229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102677179148303558714220305 77007884361227669035665229)
        ·
          refine ⟨28877956635460375888374461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77007884361227669035665229 28877956635460375888374461)
          ·
            refine ⟨10829233738297640958140423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28877956635460375888374461 10829233738297640958140423)
            ·
              refine ⟨16243850607446461437210635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829233738297640958140423 16243850607446461437210635)
              ·
                refine ⟨24365775911169692155815953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16243850607446461437210635 24365775911169692155815953)
                ·
                  refine ⟨18274331933377269116861965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24365775911169692155815953 18274331933377269116861965)
                  ·
                    refine ⟨6852874475016475918823237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18274331933377269116861965 6852874475016475918823237)
                    ·
                      refine ⟨1284913964065589234779357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6852874475016475918823237 1284913964065589234779357)
                      ·
                        rfl

theorem cell23_2502361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2502361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502361 prefixEnd_2502361 := by exact prefixLift 2502361
  have htrace : WordTrace (prefixWord ++ tailWord_2502361) baseStart_2502361 baseEnd_2502361 := by
    simpa [prefixWord, tailWord_2502361, baseEnd_2502361] using wordTrace_append hprefix tailTrace_2502361
  have hstable : (prefixWord ++ tailWord_2502361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502361).length < 2 ^ (prefixWord ++ tailWord_2502361).sum := by decide
  have hdescent : baseEnd_2502361 < baseStart_2502361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502412 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_2502412 : Nat := 118140960795 + 2502412 * 2 ^ 59
def prefixEnd_2502412 : Nat := 4983230072969 + 3 ^ 40 * 2502412 * 2
def baseEnd_2502412 : Nat := 1284940151578968535241623

theorem tailTrace_2502412 : CollatzResearch.WordTrace tailWord_2502412 prefixEnd_2502412 1284940151578968535241623 := by
  unfold tailWord_2502412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45635231905098088394706745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60846975873464117859608993 45635231905098088394706745)
  ·
    refine ⟨34226423928823566296030059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45635231905098088394706745 34226423928823566296030059)
    ·
      refine ⟨51339635893235349444045089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34226423928823566296030059 51339635893235349444045089)
      ·
        refine ⟨38504726919926512083033817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51339635893235349444045089 38504726919926512083033817)
        ·
          refine ⟨28878545189944884062275363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38504726919926512083033817 28878545189944884062275363)
          ·
            refine ⟨43317817784917326093413045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28878545189944884062275363 43317817784917326093413045)
            ·
              refine ⟨4061045417335999321257473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43317817784917326093413045 4061045417335999321257473)
              ·
                refine ⟨3045784063001999490943105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4061045417335999321257473 3045784063001999490943105)
                ·
                  refine ⟨2284338047251499618207329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045784063001999490943105 2284338047251499618207329)
                  ·
                    refine ⟨1713253535438624713655497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284338047251499618207329 1713253535438624713655497)
                    ·
                      refine ⟨1284940151578968535241623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713253535438624713655497 1284940151578968535241623)
                      ·
                        rfl

theorem cell23_2502412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_2502412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502412 prefixEnd_2502412 := by exact prefixLift 2502412
  have htrace : WordTrace (prefixWord ++ tailWord_2502412) baseStart_2502412 baseEnd_2502412 := by
    simpa [prefixWord, tailWord_2502412, baseEnd_2502412] using wordTrace_append hprefix tailTrace_2502412
  have hstable : (prefixWord ++ tailWord_2502412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502412).length < 2 ^ (prefixWord ++ tailWord_2502412).sum := by decide
  have hdescent : baseEnd_2502412 < baseStart_2502412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502428 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2502428 : Nat := 118140960795 + 2502428 * 2 ^ 59
def prefixEnd_2502428 : Nat := 4983230072969 + 3 ^ 40 * 2502428 * 2
def baseEnd_2502428 : Nat := 1284948367269440472641549

theorem tailTrace_2502428 : CollatzResearch.WordTrace tailWord_2502428 prefixEnd_2502428 1284948367269440472641549 := by
  unfold tailWord_2502428
  simp only [CollatzResearch.WordTrace]
  refine ⟨45635523689069105760997969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60847364918758807681330625 45635523689069105760997969)
  ·
    refine ⟨34226642766801829320748477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45635523689069105760997969 34226642766801829320748477)
    ·
      refine ⟨12834991037550685995280679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34226642766801829320748477 12834991037550685995280679)
      ·
        refine ⟨19252486556326028992921019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12834991037550685995280679 19252486556326028992921019)
        ·
          refine ⟨28878729834489043489381529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19252486556326028992921019 28878729834489043489381529)
          ·
            refine ⟨21659047375866782617036147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28878729834489043489381529 21659047375866782617036147)
            ·
              refine ⟨32488571063800173925554221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21659047375866782617036147 32488571063800173925554221)
              ·
                refine ⟨12183214148925065222082833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32488571063800173925554221 12183214148925065222082833)
                ·
                  refine ⟨9137410611693798916562125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12183214148925065222082833 9137410611693798916562125)
                  ·
                    refine ⟨3426528979385174593710797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9137410611693798916562125 3426528979385174593710797)
                    ·
                      refine ⟨1284948367269440472641549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426528979385174593710797 1284948367269440472641549)
                      ·
                        rfl

theorem cell23_2502428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2502428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502428 prefixEnd_2502428 := by exact prefixLift 2502428
  have htrace : WordTrace (prefixWord ++ tailWord_2502428) baseStart_2502428 baseEnd_2502428 := by
    simpa [prefixWord, tailWord_2502428, baseEnd_2502428] using wordTrace_append hprefix tailTrace_2502428
  have hstable : (prefixWord ++ tailWord_2502428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502428).length < 2 ^ (prefixWord ++ tailWord_2502428).sum := by decide
  have hdescent : baseEnd_2502428 < baseStart_2502428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502431 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 7]
def baseStart_2502431 : Nat := 118140960795 + 2502431 * 2 ^ 59
def prefixEnd_2502431 : Nat := 4983230072969 + 3 ^ 40 * 2502431 * 2
def baseEnd_2502431 : Nat := 428316635903801320301345

theorem tailTrace_2502431 : CollatzResearch.WordTrace tailWord_2502431 prefixEnd_2502431 428316635903801320301345 := by
  unfold tailWord_2502431
  simp only [CollatzResearch.WordTrace]
  refine ⟨91271156797127343034355147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60847437864751562022903431 91271156797127343034355147)
  ·
    refine ⟨136906735195691014551532721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91271156797127343034355147 136906735195691014551532721)
    ·
      refine ⟨102680051396768260913649541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136906735195691014551532721 102680051396768260913649541)
      ·
        refine ⟨19252509636894048921309289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102680051396768260913649541 19252509636894048921309289)
        ·
          refine ⟨14439382227670536690981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19252509636894048921309289 14439382227670536690981967)
          ·
            refine ⟨21659073341505805036472951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14439382227670536690981967 21659073341505805036472951)
            ·
              refine ⟨32488610012258707554709427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21659073341505805036472951 32488610012258707554709427)
              ·
                refine ⟨48732915018388061332064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32488610012258707554709427 48732915018388061332064141)
                ·
                  refine ⟨18274843131895522999524053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48732915018388061332064141 18274843131895522999524053)
                  ·
                    refine ⟨428316635903801320301345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18274843131895522999524053 428316635903801320301345)
                    ·
                      rfl

theorem cell23_2502431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_2502431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502431 prefixEnd_2502431 := by exact prefixLift 2502431
  have htrace : WordTrace (prefixWord ++ tailWord_2502431) baseStart_2502431 baseEnd_2502431 := by
    simpa [prefixWord, tailWord_2502431, baseEnd_2502431] using wordTrace_append hprefix tailTrace_2502431
  have hstable : (prefixWord ++ tailWord_2502431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502431).length < 2 ^ (prefixWord ++ tailWord_2502431).sum := by decide
  have hdescent : baseEnd_2502431 < baseStart_2502431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502452 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2502452 : Nat := 118140960795 + 2502452 * 2 ^ 59
def prefixEnd_2502452 : Nat := 4983230072969 + 3 ^ 40 * 2502452 * 2
def baseEnd_2502452 : Nat := 142773410089460930971271

theorem tailTrace_2502452 : CollatzResearch.WordTrace tailWord_2502452 prefixEnd_2502452 142773410089460930971271 := by
  unfold tailWord_2502452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45635961365025631810434805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60847948486700842413913073 45635961365025631810434805)
  ·
    refine ⟨4278371377971152982228263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45635961365025631810434805 4278371377971152982228263)
    ·
      refine ⟨6417557066956729473342395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278371377971152982228263 6417557066956729473342395)
      ·
        refine ⟨9626335600435094210013593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417557066956729473342395 9626335600435094210013593)
        ·
          refine ⟨7219751700326320657510195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9626335600435094210013593 7219751700326320657510195)
          ·
            refine ⟨10829627550489480986265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219751700326320657510195 10829627550489480986265293)
            ·
              refine ⟨4061110331433555369849485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10829627550489480986265293 4061110331433555369849485)
              ·
                refine ⟨1522916374287583263693557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4061110331433555369849485 1522916374287583263693557)
                ·
                  refine ⟨142773410089460930971271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522916374287583263693557 142773410089460930971271)
                  ·
                    rfl

theorem cell23_2502452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2502452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502452 prefixEnd_2502452 := by exact prefixLift 2502452
  have htrace : WordTrace (prefixWord ++ tailWord_2502452) baseStart_2502452 baseEnd_2502452 := by
    simpa [prefixWord, tailWord_2502452, baseEnd_2502452] using wordTrace_append hprefix tailTrace_2502452
  have hstable : (prefixWord ++ tailWord_2502452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502452).length < 2 ^ (prefixWord ++ tailWord_2502452).sum := by decide
  have hdescent : baseEnd_2502452 < baseStart_2502452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502511 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_2502511 : Nat := 118140960795 + 2502511 * 2 ^ 59
def prefixEnd_2502511 : Nat := 4983230072969 + 3 ^ 40 * 2502511 * 2
def baseEnd_2502511 : Nat := 1284990986163763647903667

theorem tailTrace_2502511 : CollatzResearch.WordTrace tailWord_2502511 prefixEnd_2502511 1284990986163763647903667 := by
  unfold tailWord_2502511
  simp only [CollatzResearch.WordTrace]
  refine ⟨91274074636837516697267387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60849383091225011131511591 91274074636837516697267387)
  ·
    refine ⟨136911111955256275045901081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91274074636837516697267387 136911111955256275045901081)
    ·
      refine ⟨102683333966442206284425811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136911111955256275045901081 102683333966442206284425811)
      ·
        refine ⟨154025000949663309426638717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102683333966442206284425811 154025000949663309426638717)
        ·
          refine ⟨57759375356123741034989519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154025000949663309426638717 57759375356123741034989519)
          ·
            refine ⟨86639063034185611552484279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57759375356123741034989519 86639063034185611552484279)
            ·
              refine ⟨129958594551278417328726419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86639063034185611552484279 129958594551278417328726419)
              ·
                refine ⟨194937891826917625993089629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129958594551278417328726419 194937891826917625993089629)
                ·
                  refine ⟨73101709435094109747408611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194937891826917625993089629 73101709435094109747408611)
                  ·
                    refine ⟨109652564152641164621112917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73101709435094109747408611 109652564152641164621112917)
                    ·
                      refine ⟨1284990986163763647903667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 109652564152641164621112917 1284990986163763647903667)
                      ·
                        rfl

theorem cell23_2502511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_2502511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502511 prefixEnd_2502511 := by exact prefixLift 2502511
  have htrace : WordTrace (prefixWord ++ tailWord_2502511) baseStart_2502511 baseEnd_2502511 := by
    simpa [prefixWord, tailWord_2502511, baseEnd_2502511] using wordTrace_append hprefix tailTrace_2502511
  have hstable : (prefixWord ++ tailWord_2502511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502511).length < 2 ^ (prefixWord ++ tailWord_2502511).sum := by decide
  have hdescent : baseEnd_2502511 < baseStart_2502511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502545 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_2502545 : Nat := 118140960795 + 2502545 * 2 ^ 59
def prefixEnd_2502545 : Nat := 4983230072969 + 3 ^ 40 * 2502545 * 2
def baseEnd_2502545 : Nat := 1285008444506016514878511

theorem tailTrace_2502545 : CollatzResearch.WordTrace tailWord_2502545 prefixEnd_2502545 1285008444506016514878511 := by
  unfold tailWord_2502545
  simp only [CollatzResearch.WordTrace]
  refine ⟨91275314718714340504005089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60850209812476227002670059 91275314718714340504005089)
  ·
    refine ⟨68456486039035755378003817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91275314718714340504005089 68456486039035755378003817)
    ·
      refine ⟨51342364529276816533502863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68456486039035755378003817 51342364529276816533502863)
      ·
        refine ⟨77013546793915224800254295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51342364529276816533502863 77013546793915224800254295)
        ·
          refine ⟨115520320190872837200381443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77013546793915224800254295 115520320190872837200381443)
          ·
            refine ⟨173280480286309255800572165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115520320190872837200381443 173280480286309255800572165)
            ·
              refine ⟨32490090053682985462607281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173280480286309255800572165 32490090053682985462607281)
              ·
                refine ⟨24367567540262239096955461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32490090053682985462607281 24367567540262239096955461)
                ·
                  refine ⟨4568918913799169830679149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24367567540262239096955461 4568918913799169830679149)
                  ·
                    refine ⟨1713344592674688686504681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4568918913799169830679149 1713344592674688686504681)
                    ·
                      refine ⟨1285008444506016514878511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713344592674688686504681 1285008444506016514878511)
                      ·
                        rfl

theorem cell23_2502545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_2502545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502545 prefixEnd_2502545 := by exact prefixLift 2502545
  have htrace : WordTrace (prefixWord ++ tailWord_2502545) baseStart_2502545 baseEnd_2502545 := by
    simpa [prefixWord, tailWord_2502545, baseEnd_2502545] using wordTrace_append hprefix tailTrace_2502545
  have hstable : (prefixWord ++ tailWord_2502545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502545).length < 2 ^ (prefixWord ++ tailWord_2502545).sum := by decide
  have hdescent : baseEnd_2502545 < baseStart_2502545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502575 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_2502575 : Nat := 118140960795 + 2502575 * 2 ^ 59
def prefixEnd_2502575 : Nat := 4983230072969 + 3 ^ 40 * 2502575 * 2
def baseEnd_2502575 : Nat := 1285023848925651397503373

theorem tailTrace_2502575 : CollatzResearch.WordTrace tailWord_2502575 prefixEnd_2502575 1285023848925651397503373 := by
  unfold tailWord_2502575
  simp only [CollatzResearch.WordTrace]
  refine ⟨91276408908605655627597179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60850939272403770418398119 91276408908605655627597179)
  ·
    refine ⟨136914613362908483441395769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91276408908605655627597179 136914613362908483441395769)
    ·
      refine ⟨102685960022181362581046827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136914613362908483441395769 102685960022181362581046827)
      ·
        refine ⟨154028940033272043871570241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102685960022181362581046827 154028940033272043871570241)
        ·
          refine ⟨115521705024954032903677681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154028940033272043871570241 115521705024954032903677681)
          ·
            refine ⟨86641278768715524677758261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115521705024954032903677681 86641278768715524677758261)
            ·
              refine ⟨8122619884567080438539837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86641278768715524677758261 8122619884567080438539837)
              ·
                refine ⟨3045982456712655164452439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8122619884567080438539837 3045982456712655164452439)
                ·
                  refine ⟨4568973685068982746678659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045982456712655164452439 4568973685068982746678659)
                  ·
                    refine ⟨6853460527603474120017989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568973685068982746678659 6853460527603474120017989)
                    ·
                      refine ⟨1285023848925651397503373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6853460527603474120017989 1285023848925651397503373)
                      ·
                        rfl

theorem cell23_2502575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_2502575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502575 prefixEnd_2502575 := by exact prefixLift 2502575
  have htrace : WordTrace (prefixWord ++ tailWord_2502575) baseStart_2502575 baseEnd_2502575 := by
    simpa [prefixWord, tailWord_2502575, baseEnd_2502575] using wordTrace_append hprefix tailTrace_2502575
  have hstable : (prefixWord ++ tailWord_2502575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502575).length < 2 ^ (prefixWord ++ tailWord_2502575).sum := by decide
  have hdescent : baseEnd_2502575 < baseStart_2502575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2502578 : Nat := 118140960795 + 2502578 * 2 ^ 59
def prefixEnd_2502578 : Nat := 4983230072969 + 3 ^ 40 * 2502578 * 2
def baseEnd_2502578 : Nat := 1285025389367614885765859

theorem tailTrace_2502578 : CollatzResearch.WordTrace tailWord_2502578 prefixEnd_2502578 1285025389367614885765859 := by
  unfold tailWord_2502578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22819129581898696784989097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60851012218396524759970925 22819129581898696784989097)
  ·
    refine ⟨17114347186424022588741823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22819129581898696784989097 17114347186424022588741823)
    ·
      refine ⟨25671520779636033883112735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17114347186424022588741823 25671520779636033883112735)
      ·
        refine ⟨38507281169454050824669103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25671520779636033883112735 38507281169454050824669103)
        ·
          refine ⟨57760921754181076237003655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38507281169454050824669103 57760921754181076237003655)
          ·
            refine ⟨86641382631271614355505483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57760921754181076237003655 86641382631271614355505483)
            ·
              refine ⟨129962073946907421533258225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86641382631271614355505483 129962073946907421533258225)
              ·
                refine ⟨97471555460180566149943669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129962073946907421533258225 97471555460180566149943669)
                ·
                  refine ⟨9137958324391928076557219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97471555460180566149943669 9137958324391928076557219)
                  ·
                    refine ⟨13706937486587892114835829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9137958324391928076557219 13706937486587892114835829)
                    ·
                      refine ⟨1285025389367614885765859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13706937486587892114835829 1285025389367614885765859)
                      ·
                        rfl

theorem cell23_2502578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2502578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502578 prefixEnd_2502578 := by exact prefixLift 2502578
  have htrace : WordTrace (prefixWord ++ tailWord_2502578) baseStart_2502578 baseEnd_2502578 := by
    simpa [prefixWord, tailWord_2502578, baseEnd_2502578] using wordTrace_append hprefix tailTrace_2502578
  have hstable : (prefixWord ++ tailWord_2502578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502578).length < 2 ^ (prefixWord ++ tailWord_2502578).sum := by decide
  have hdescent : baseEnd_2502578 < baseStart_2502578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502585 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_2502585 : Nat := 118140960795 + 2502585 * 2 ^ 59
def prefixEnd_2502585 : Nat := 4983230072969 + 3 ^ 40 * 2502585 * 2
def baseEnd_2502585 : Nat := 428342994577398786126109

theorem tailTrace_2502585 : CollatzResearch.WordTrace tailWord_2502585 prefixEnd_2502585 428342994577398786126109 := by
  unfold tailWord_2502585
  simp only [CollatzResearch.WordTrace]
  refine ⟨91276773638569427335461209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60851182425712951556974139 91276773638569427335461209)
  ·
    refine ⟨68457580228927070501595907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91276773638569427335461209 68457580228927070501595907)
    ·
      refine ⟨102686370343390605752393861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68457580228927070501595907 102686370343390605752393861)
      ·
        refine ⟨19253694439385738578573849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102686370343390605752393861 19253694439385738578573849)
        ·
          refine ⟨14440270829539303933930387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19253694439385738578573849 14440270829539303933930387)
          ·
            refine ⟨21660406244308955900895581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14440270829539303933930387 21660406244308955900895581)
            ·
              refine ⟨8122652341615858462835843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21660406244308955900895581 8122652341615858462835843)
              ·
                refine ⟨12183978512423787694253765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8122652341615858462835843 12183978512423787694253765)
                ·
                  refine ⟨2284495971079460192672581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12183978512423787694253765 2284495971079460192672581)
                  ·
                    refine ⟨428342994577398786126109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2284495971079460192672581 428342994577398786126109)
                    ·
                      rfl

theorem cell23_2502585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_2502585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502585 prefixEnd_2502585 := by exact prefixLift 2502585
  have htrace : WordTrace (prefixWord ++ tailWord_2502585) baseStart_2502585 baseEnd_2502585 := by
    simpa [prefixWord, tailWord_2502585, baseEnd_2502585] using wordTrace_append hprefix tailTrace_2502585
  have hstable : (prefixWord ++ tailWord_2502585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502585).length < 2 ^ (prefixWord ++ tailWord_2502585).sum := by decide
  have hdescent : baseEnd_2502585 < baseStart_2502585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502625 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_2502625 : Nat := 118140960795 + 2502625 * 2 ^ 59
def prefixEnd_2502625 : Nat := 4983230072969 + 3 ^ 40 * 2502625 * 2
def baseEnd_2502625 : Nat := 1285049522958376201878143

theorem tailTrace_2502625 : CollatzResearch.WordTrace tailWord_2502625 prefixEnd_2502625 1285049522958376201878143 := by
  unfold tailWord_2502625
  simp only [CollatzResearch.WordTrace]
  refine ⟨91278232558424514166917329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60852155038949676111278219 91278232558424514166917329)
  ·
    refine ⟨68458674418818385625187997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91278232558424514166917329 68458674418818385625187997)
    ·
      refine ⟨25672002907056894609445499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68458674418818385625187997 25672002907056894609445499)
      ·
        refine ⟨38508004360585341914168249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25672002907056894609445499 38508004360585341914168249)
        ·
          refine ⟨28881003270439006435626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38508004360585341914168249 28881003270439006435626187)
          ·
            refine ⟨43321504905658509653439281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28881003270439006435626187 43321504905658509653439281)
            ·
              refine ⟨32491128679243882240079461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43321504905658509653439281 32491128679243882240079461)
              ·
                refine ⟨6092086627358227920014899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32491128679243882240079461 6092086627358227920014899)
                ·
                  refine ⟨9138129941037341880022349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092086627358227920014899 9138129941037341880022349)
                  ·
                    refine ⟨3426798727889003205008381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138129941037341880022349 3426798727889003205008381)
                    ·
                      refine ⟨1285049522958376201878143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426798727889003205008381 1285049522958376201878143)
                      ·
                        rfl

theorem cell23_2502625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_2502625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502625 prefixEnd_2502625 := by exact prefixLift 2502625
  have htrace : WordTrace (prefixWord ++ tailWord_2502625) baseStart_2502625 baseEnd_2502625 := by
    simpa [prefixWord, tailWord_2502625, baseEnd_2502625] using wordTrace_append hprefix tailTrace_2502625
  have hstable : (prefixWord ++ tailWord_2502625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502625).length < 2 ^ (prefixWord ++ tailWord_2502625).sum := by decide
  have hdescent : baseEnd_2502625 < baseStart_2502625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502652 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_2502652 : Nat := 118140960795 + 2502652 * 2 ^ 59
def prefixEnd_2502652 : Nat := 4983230072969 + 3 ^ 40 * 2502652 * 2
def baseEnd_2502652 : Nat := 1285063386936047596240519

theorem tailTrace_2502652 : CollatzResearch.WordTrace tailWord_2502652 prefixEnd_2502652 1285063386936047596240519 := by
  unfold tailWord_2502652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45639608664663348889075105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60852811552884465185433473 45639608664663348889075105)
  ·
    refine ⟨34229706498497511666806329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45639608664663348889075105 34229706498497511666806329)
    ·
      refine ⟨25672279873873133750104747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34229706498497511666806329 25672279873873133750104747)
      ·
        refine ⟨38508419810809700625157121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25672279873873133750104747 38508419810809700625157121)
        ·
          refine ⟨28881314858107275468867841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38508419810809700625157121 28881314858107275468867841)
          ·
            refine ⟨21660986143580456601650881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28881314858107275468867841 21660986143580456601650881)
            ·
              refine ⟨16245739607685342451238161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21660986143580456601650881 16245739607685342451238161)
              ·
                refine ⟨12184304705764006838428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16245739607685342451238161 12184304705764006838428621)
                ·
                  refine ⟨4569114264661502564410733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12184304705764006838428621 4569114264661502564410733)
                  ·
                    refine ⟨1713417849248063461654025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4569114264661502564410733 1713417849248063461654025)
                    ·
                      refine ⟨1285063386936047596240519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713417849248063461654025 1285063386936047596240519)
                      ·
                        rfl

theorem cell23_2502652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_2502652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502652 prefixEnd_2502652 := by exact prefixLift 2502652
  have htrace : WordTrace (prefixWord ++ tailWord_2502652) baseStart_2502652 baseEnd_2502652 := by
    simpa [prefixWord, tailWord_2502652, baseEnd_2502652] using wordTrace_append hprefix tailTrace_2502652
  have hstable : (prefixWord ++ tailWord_2502652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502652).length < 2 ^ (prefixWord ++ tailWord_2502652).sum := by decide
  have hdescent : baseEnd_2502652 < baseStart_2502652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502676 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2502676 : Nat := 118140960795 + 2502676 * 2 ^ 59
def prefixEnd_2502676 : Nat := 4983230072969 + 3 ^ 40 * 2502676 * 2
def baseEnd_2502676 : Nat := 1285075710471755502340409

theorem tailTrace_2502676 : CollatzResearch.WordTrace tailWord_2502676 prefixEnd_2502676 1285075710471755502340409 := by
  unfold tailWord_2502676
  simp only [CollatzResearch.WordTrace]
  refine ⟨45640046340619874938511941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60853395120826499918015921 45640046340619874938511941)
  ·
    refine ⟨8557508688866226550970989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45640046340619874938511941 8557508688866226550970989)
    ·
      refine ⟨3209065758324834956614121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8557508688866226550970989 3209065758324834956614121)
      ·
        refine ⟨2406799318743626217460591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209065758324834956614121 2406799318743626217460591)
        ·
          refine ⟨3610198978115439326190887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406799318743626217460591 3610198978115439326190887)
          ·
            refine ⟨5415298467173158989286331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610198978115439326190887 5415298467173158989286331)
            ·
              refine ⟨8122947700759738483929497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415298467173158989286331 8122947700759738483929497)
              ·
                refine ⟨6092210775569803862947123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8122947700759738483929497 6092210775569803862947123)
                ·
                  refine ⟨9138316163354705794420685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092210775569803862947123 9138316163354705794420685)
                  ·
                    refine ⟨3426868561258014672907757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138316163354705794420685 3426868561258014672907757)
                    ·
                      refine ⟨1285075710471755502340409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426868561258014672907757 1285075710471755502340409)
                      ·
                        rfl

theorem cell23_2502676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2502676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502676 prefixEnd_2502676 := by exact prefixLift 2502676
  have htrace : WordTrace (prefixWord ++ tailWord_2502676) baseStart_2502676 baseEnd_2502676 := by
    simpa [prefixWord, tailWord_2502676, baseEnd_2502676] using wordTrace_append hprefix tailTrace_2502676
  have hstable : (prefixWord ++ tailWord_2502676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502676).length < 2 ^ (prefixWord ++ tailWord_2502676).sum := by decide
  have hdescent : baseEnd_2502676 < baseStart_2502676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502682 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_2502682 : Nat := 118140960795 + 2502682 * 2 ^ 59
def prefixEnd_2502682 : Nat := 4983230072969 + 3 ^ 40 * 2502682 * 2
def baseEnd_2502682 : Nat := 1285078791355682478865381

theorem tailTrace_2502682 : CollatzResearch.WordTrace tailWord_2502682 prefixEnd_2502682 1285078791355682478865381 := by
  unfold tailWord_2502682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820077879804503225435575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60853541012812008601161533 22820077879804503225435575)
  ·
    refine ⟨34230116819706754838153363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22820077879804503225435575 34230116819706754838153363)
    ·
      refine ⟨51345175229560132257230045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34230116819706754838153363 51345175229560132257230045)
      ·
        refine ⟨19254440711085049596461267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51345175229560132257230045 19254440711085049596461267)
        ·
          refine ⟨28881661066627574394691901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19254440711085049596461267 28881661066627574394691901)
          ·
            refine ⟨10830622899985340398009463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28881661066627574394691901 10830622899985340398009463)
            ·
              refine ⟨16245934349978010597014195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830622899985340398009463 16245934349978010597014195)
              ·
                refine ⟨24368901524967015895521293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16245934349978010597014195 24368901524967015895521293)
                ·
                  refine ⟨9138338071862630960820485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24368901524967015895521293 9138338071862630960820485)
                  ·
                    refine ⟨1713438388474243305153841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9138338071862630960820485 1713438388474243305153841)
                    ·
                      refine ⟨1285078791355682478865381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713438388474243305153841 1285078791355682478865381)
                      ·
                        rfl

theorem cell23_2502682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_2502682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502682 prefixEnd_2502682 := by exact prefixLift 2502682
  have htrace : WordTrace (prefixWord ++ tailWord_2502682) baseStart_2502682 baseEnd_2502682 := by
    simpa [prefixWord, tailWord_2502682, baseEnd_2502682] using wordTrace_append hprefix tailTrace_2502682
  have hstable : (prefixWord ++ tailWord_2502682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502682).length < 2 ^ (prefixWord ++ tailWord_2502682).sum := by decide
  have hdescent : baseEnd_2502682 < baseStart_2502682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502702 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2502702 : Nat := 118140960795 + 2502702 * 2 ^ 59
def prefixEnd_2502702 : Nat := 4983230072969 + 3 ^ 40 * 2502702 * 2
def baseEnd_2502702 : Nat := 1285089060968772400615289

theorem tailTrace_2502702 : CollatzResearch.WordTrace tailWord_2502702 prefixEnd_2502702 1285089060968772400615289 := by
  unfold tailWord_2502702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410130122393194539683795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60854027319430370878313573 11410130122393194539683795)
  ·
    refine ⟨17115195183589791809525693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11410130122393194539683795 17115195183589791809525693)
    ·
      refine ⟨6418198193846171928572135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17115195183589791809525693 6418198193846171928572135)
      ·
        refine ⟨9627297290769257892858203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6418198193846171928572135 9627297290769257892858203)
        ·
          refine ⟨14440945936153886839287305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9627297290769257892858203 14440945936153886839287305)
          ·
            refine ⟨10830709452115415129465479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14440945936153886839287305 10830709452115415129465479)
            ·
              refine ⟨16246064178173122694198219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830709452115415129465479 16246064178173122694198219)
              ·
                refine ⟨24369096267259684041297329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16246064178173122694198219 24369096267259684041297329)
                ·
                  refine ⟨18276822200444763030972997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24369096267259684041297329 18276822200444763030972997)
                  ·
                    refine ⟨3426904162583393068307437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18276822200444763030972997 3426904162583393068307437)
                    ·
                      refine ⟨1285089060968772400615289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426904162583393068307437 1285089060968772400615289)
                      ·
                        rfl

theorem cell23_2502702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2502702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502702 prefixEnd_2502702 := by exact prefixLift 2502702
  have htrace : WordTrace (prefixWord ++ tailWord_2502702) baseStart_2502702 baseEnd_2502702 := by
    simpa [prefixWord, tailWord_2502702, baseEnd_2502702] using wordTrace_append hprefix tailTrace_2502702
  have hstable : (prefixWord ++ tailWord_2502702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502702).length < 2 ^ (prefixWord ++ tailWord_2502702).sum := by decide
  have hdescent : baseEnd_2502702 < baseStart_2502702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502712 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2502712 : Nat := 118140960795 + 2502712 * 2 ^ 59
def prefixEnd_2502712 : Nat := 4983230072969 + 3 ^ 40 * 2502712 * 2
def baseEnd_2502712 : Nat := 1285094195775317361490243

theorem tailTrace_2502712 : CollatzResearch.WordTrace tailWord_2502712 prefixEnd_2502712 1285094195775317361490243 := by
  unfold tailWord_2502712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45640702854554664012667195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60854270472739552016889593 45640702854554664012667195)
  ·
    refine ⟨68461054281831996019000793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45640702854554664012667195 68461054281831996019000793)
    ·
      refine ⟨51345790711373997014250595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68461054281831996019000793 51345790711373997014250595)
      ·
        refine ⟨77018686067060995521375893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51345790711373997014250595 77018686067060995521375893)
        ·
          refine ⟨3610250909393484165064495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77018686067060995521375893 3610250909393484165064495)
          ·
            refine ⟨5415376364090226247596743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610250909393484165064495 5415376364090226247596743)
            ·
              refine ⟨8123064546135339371395115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415376364090226247596743 8123064546135339371395115)
              ·
                refine ⟨12184596819203009057092673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123064546135339371395115 12184596819203009057092673)
                ·
                  refine ⟨9138447614402256792819505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184596819203009057092673 9138447614402256792819505)
                  ·
                    refine ⟨6853835710801692594614629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9138447614402256792819505 6853835710801692594614629)
                    ·
                      refine ⟨1285094195775317361490243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6853835710801692594614629 1285094195775317361490243)
                      ·
                        rfl

theorem cell23_2502712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2502712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502712 prefixEnd_2502712 := by exact prefixLift 2502712
  have htrace : WordTrace (prefixWord ++ tailWord_2502712) baseStart_2502712 baseEnd_2502712 := by
    simpa [prefixWord, tailWord_2502712, baseEnd_2502712] using wordTrace_append hprefix tailTrace_2502712
  have hstable : (prefixWord ++ tailWord_2502712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502712).length < 2 ^ (prefixWord ++ tailWord_2502712).sum := by decide
  have hdescent : baseEnd_2502712 < baseStart_2502712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502715 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3]
def baseStart_2502715 : Nat := 118140960795 + 2502715 * 2 ^ 59
def prefixEnd_2502715 : Nat := 4983230072969 + 3 ^ 40 * 2502715 * 2
def baseEnd_2502715 : Nat := 1285095736217280849752729

theorem tailTrace_2502715 : CollatzResearch.WordTrace tailWord_2502715 prefixEnd_2502715 1285095736217280849752729 := by
  unfold tailWord_2502715
  simp only [CollatzResearch.WordTrace]
  refine ⟨91281515128098459537693599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60854343418732306358462399 91281515128098459537693599)
  ·
    refine ⟨136922272692147689306540399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91281515128098459537693599 136922272692147689306540399)
    ·
      refine ⟨205383409038221533959810599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136922272692147689306540399 205383409038221533959810599)
      ·
        refine ⟨308075113557332300939715899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205383409038221533959810599 308075113557332300939715899)
        ·
          refine ⟨462112670335998451409573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308075113557332300939715899 462112670335998451409573849)
          ·
            refine ⟨346584502751998838557180387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462112670335998451409573849 346584502751998838557180387)
            ·
              refine ⟨519876754127998257835770581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346584502751998838557180387 519876754127998257835770581)
              ·
                refine ⟨12184611424874959168025873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 519876754127998257835770581 12184611424874959168025873)
                ·
                  refine ⟨9138458568656219376019405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184611424874959168025873 9138458568656219376019405)
                  ·
                    refine ⟨3426921963246082266007277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138458568656219376019405 3426921963246082266007277)
                    ·
                      refine ⟨1285095736217280849752729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426921963246082266007277 1285095736217280849752729)
                      ·
                        rfl

theorem cell23_2502715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].length) (baseStart_2502715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502715 prefixEnd_2502715 := by exact prefixLift 2502715
  have htrace : WordTrace (prefixWord ++ tailWord_2502715) baseStart_2502715 baseEnd_2502715 := by
    simpa [prefixWord, tailWord_2502715, baseEnd_2502715] using wordTrace_append hprefix tailTrace_2502715
  have hstable : (prefixWord ++ tailWord_2502715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502715).length < 2 ^ (prefixWord ++ tailWord_2502715).sum := by decide
  have hdescent : baseEnd_2502715 < baseStart_2502715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502749 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2502749 : Nat := 118140960795 + 2502749 * 2 ^ 59
def prefixEnd_2502749 : Nat := 4983230072969 + 3 ^ 40 * 2502749 * 2
def baseEnd_2502749 : Nat := 1285113194559533716727573

theorem tailTrace_2502749 : CollatzResearch.WordTrace tailWord_2502749 prefixEnd_2502749 1285113194559533716727573 := by
  unfold tailWord_2502749
  simp only [CollatzResearch.WordTrace]
  refine ⟨91282755209975283344431301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60855170139983522229620867 91282755209975283344431301)
  ·
    refine ⟨17115516601870365627080869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91282755209975283344431301 17115516601870365627080869)
    ·
      refine ⟨3209159362850693555077663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17115516601870365627080869 3209159362850693555077663)
      ·
        refine ⟨4813739044276040332616495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209159362850693555077663 4813739044276040332616495)
        ·
          refine ⟨7220608566414060498924743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813739044276040332616495 7220608566414060498924743)
          ·
            refine ⟨10830912849621090748387115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220608566414060498924743 10830912849621090748387115)
            ·
              refine ⟨16246369274431636122580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830912849621090748387115 16246369274431636122580673)
              ·
                refine ⟨12184776955823727091935505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16246369274431636122580673 12184776955823727091935505)
                ·
                  refine ⟨9138582716867795318951629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184776955823727091935505 9138582716867795318951629)
                  ·
                    refine ⟨3426968518825423244606861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138582716867795318951629 3426968518825423244606861)
                    ·
                      refine ⟨1285113194559533716727573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3426968518825423244606861 1285113194559533716727573)
                      ·
                        rfl

theorem cell23_2502749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2502749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502749 prefixEnd_2502749 := by exact prefixLift 2502749
  have htrace : WordTrace (prefixWord ++ tailWord_2502749) baseStart_2502749 baseEnd_2502749 := by
    simpa [prefixWord, tailWord_2502749, baseEnd_2502749] using wordTrace_append hprefix tailTrace_2502749
  have hstable : (prefixWord ++ tailWord_2502749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502749).length < 2 ^ (prefixWord ++ tailWord_2502749).sum := by decide
  have hdescent : baseEnd_2502749 < baseStart_2502749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502750 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2502750 : Nat := 118140960795 + 2502750 * 2 ^ 59
def prefixEnd_2502750 : Nat := 4983230072969 + 3 ^ 40 * 2502750 * 2
def baseEnd_2502750 : Nat := 1285113708040188212815069

theorem tailTrace_2502750 : CollatzResearch.WordTrace tailWord_2502750 prefixEnd_2502750 1285113708040188212815069 := by
  unfold tailWord_2502750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410348960371457564402213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60855194455314440343478469 11410348960371457564402213)
  ·
    refine ⟨2139440430069648293325415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11410348960371457564402213 2139440430069648293325415)
    ·
      refine ⟨3209160645104472439988123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139440430069648293325415 3209160645104472439988123)
      ·
        refine ⟨4813740967656708659982185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209160645104472439988123 4813740967656708659982185)
        ·
          refine ⟨3610305725742531494986639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4813740967656708659982185 3610305725742531494986639)
          ·
            refine ⟨5415458588613797242479959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610305725742531494986639 5415458588613797242479959)
            ·
              refine ⟨8123187882920695863719939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415458588613797242479959 8123187882920695863719939)
              ·
                refine ⟨12184781824381043795579909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123187882920695863719939 12184781824381043795579909)
                ·
                  refine ⟨2284646592071445711671233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12184781824381043795579909 2284646592071445711671233)
                  ·
                    refine ⟨1713484944053584283753425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284646592071445711671233 1713484944053584283753425)
                    ·
                      refine ⟨1285113708040188212815069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713484944053584283753425 1285113708040188212815069)
                      ·
                        rfl

theorem cell23_2502750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2502750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502750 prefixEnd_2502750 := by exact prefixLift 2502750
  have htrace : WordTrace (prefixWord ++ tailWord_2502750) baseStart_2502750 baseEnd_2502750 := by
    simpa [prefixWord, tailWord_2502750, baseEnd_2502750] using wordTrace_append hprefix tailTrace_2502750
  have hstable : (prefixWord ++ tailWord_2502750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502750).length < 2 ^ (prefixWord ++ tailWord_2502750).sum := by decide
  have hdescent : baseEnd_2502750 < baseStart_2502750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502812 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 6]
def baseStart_2502812 : Nat := 118140960795 + 2502812 * 2 ^ 59
def prefixEnd_2502812 : Nat := 4983230072969 + 3 ^ 40 * 2502812 * 2
def baseEnd_2502812 : Nat := 142793949315640774471087

theorem tailTrace_2502812 : CollatzResearch.WordTrace tailWord_2502812 prefixEnd_2502812 142793949315640774471087 := by
  unfold tailWord_2502812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45642526504373522551987345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60856702005831363402649793 45642526504373522551987345)
  ·
    refine ⟨34231894878280141913990509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45642526504373522551987345 34231894878280141913990509)
    ·
      refine ⟨12836960579355053217746441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34231894878280141913990509 12836960579355053217746441)
      ·
        refine ⟨9627720434516289913309831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12836960579355053217746441 9627720434516289913309831)
        ·
          refine ⟨14441580651774434869964747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9627720434516289913309831 14441580651774434869964747)
          ·
            refine ⟨21662370977661652304947121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14441580651774434869964747 21662370977661652304947121)
            ·
              refine ⟨16246778233246239228710341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21662370977661652304947121 16246778233246239228710341)
              ·
                refine ⟨3046270918733669855383189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16246778233246239228710341 3046270918733669855383189)
                ·
                  refine ⟨142793949315640774471087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3046270918733669855383189 142793949315640774471087)
                  ·
                    rfl

theorem cell23_2502812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_2502812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502812 prefixEnd_2502812 := by exact prefixLift 2502812
  have htrace : WordTrace (prefixWord ++ tailWord_2502812) baseStart_2502812 baseEnd_2502812 := by
    simpa [prefixWord, tailWord_2502812, baseEnd_2502812] using wordTrace_append hprefix tailTrace_2502812
  have hstable : (prefixWord ++ tailWord_2502812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502812).length < 2 ^ (prefixWord ++ tailWord_2502812).sum := by decide
  have hdescent : baseEnd_2502812 < baseStart_2502812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502829 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2502829 : Nat := 118140960795 + 2502829 * 2 ^ 59
def prefixEnd_2502829 : Nat := 4983230072969 + 3 ^ 40 * 2502829 * 2
def baseEnd_2502829 : Nat := 142794919223543711525245

theorem tailTrace_2502829 : CollatzResearch.WordTrace tailWord_2502829 prefixEnd_2502829 142794919223543711525245 := by
  unfold tailWord_2502829
  simp only [CollatzResearch.WordTrace]
  refine ⟨91285673049685457007343541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60857115366456971338229027 91285673049685457007343541)
  ·
    refine ⟨8558031848408011594438457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91285673049685457007343541 8558031848408011594438457)
    ·
      refine ⟨6418523886306008695828843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8558031848408011594438457 6418523886306008695828843)
      ·
        refine ⟨9627785829459013043743265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6418523886306008695828843 9627785829459013043743265)
        ·
          refine ⟨7220839372094259782807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9627785829459013043743265 7220839372094259782807449)
          ·
            refine ⟨5415629529070694837105587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7220839372094259782807449 5415629529070694837105587)
            ·
              refine ⟨8123444293606042255658381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415629529070694837105587 8123444293606042255658381)
              ·
                refine ⟨3046291610102265845871893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8123444293606042255658381 3046291610102265845871893)
                ·
                  refine ⟨142794919223543711525245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3046291610102265845871893 142794919223543711525245)
                  ·
                    rfl

theorem cell23_2502829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2502829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502829 prefixEnd_2502829 := by exact prefixLift 2502829
  have htrace : WordTrace (prefixWord ++ tailWord_2502829) baseStart_2502829 baseEnd_2502829 := by
    simpa [prefixWord, tailWord_2502829, baseEnd_2502829] using wordTrace_append hprefix tailTrace_2502829
  have hstable : (prefixWord ++ tailWord_2502829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502829).length < 2 ^ (prefixWord ++ tailWord_2502829).sum := by decide
  have hdescent : baseEnd_2502829 < baseStart_2502829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502856 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_2502856 : Nat := 118140960795 + 2502856 * 2 ^ 59
def prefixEnd_2502856 : Nat := 4983230072969 + 3 ^ 40 * 2502856 * 2
def baseEnd_2502856 : Nat := 1285168136989564798089581

theorem tailTrace_2502856 : CollatzResearch.WordTrace tailWord_2502856 prefixEnd_2502856 1285168136989564798089581 := by
  unfold tailWord_2502856
  simp only [CollatzResearch.WordTrace]
  refine ⟨45643328910293820309288211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60857771880391760412384281 45643328910293820309288211)
  ·
    refine ⟨68464993365440730463932317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45643328910293820309288211 68464993365440730463932317)
    ·
      refine ⟨25674372512040273923974619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68464993365440730463932317 25674372512040273923974619)
      ·
        refine ⟨38511558768060410885961929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25674372512040273923974619 38511558768060410885961929)
        ·
          refine ⟨28883669076045308164471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38511558768060410885961929 28883669076045308164471447)
          ·
            refine ⟨43325503614067962246707171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28883669076045308164471447 43325503614067962246707171)
            ·
              refine ⟨64988255421101943370060757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43325503614067962246707171 64988255421101943370060757)
              ·
                refine ⟨1523162236432076797735799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64988255421101943370060757 1523162236432076797735799)
                ·
                  refine ⟨2284743354648115196603699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523162236432076797735799 2284743354648115196603699)
                  ·
                    refine ⟨3427115031972172794905549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284743354648115196603699 3427115031972172794905549)
                    ·
                      refine ⟨1285168136989564798089581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427115031972172794905549 1285168136989564798089581)
                      ·
                        rfl

theorem cell23_2502856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_2502856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502856 prefixEnd_2502856 := by exact prefixLift 2502856
  have htrace : WordTrace (prefixWord ++ tailWord_2502856) baseStart_2502856 baseEnd_2502856 := by
    simpa [prefixWord, tailWord_2502856, baseEnd_2502856] using wordTrace_append hprefix tailTrace_2502856
  have hstable : (prefixWord ++ tailWord_2502856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502856).length < 2 ^ (prefixWord ++ tailWord_2502856).sum := by decide
  have hdescent : baseEnd_2502856 < baseStart_2502856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502859 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 1, 5]
def baseStart_2502859 : Nat := 118140960795 + 2502859 * 2 ^ 59
def prefixEnd_2502859 : Nat := 4983230072969 + 3 ^ 40 * 2502859 * 2
def baseEnd_2502859 : Nat := 428389892477176095450689

theorem tailTrace_2502859 : CollatzResearch.WordTrace tailWord_2502859 prefixEnd_2502859 428389892477176095450689 := by
  unfold tailWord_2502859
  simp only [CollatzResearch.WordTrace]
  refine ⟨91286767239576772130935631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60857844826384514753957087 91286767239576772130935631)
  ·
    refine ⟨136930150859365158196403447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91286767239576772130935631 136930150859365158196403447)
    ·
      refine ⟨205395226289047737294605171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136930150859365158196403447 205395226289047737294605171)
      ·
        refine ⟨308092839433571605941907757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205395226289047737294605171 308092839433571605941907757)
        ·
          refine ⟨115534814787589352228215409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308092839433571605941907757 115534814787589352228215409)
          ·
            refine ⟨86651111090692014171161557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115534814787589352228215409 86651111090692014171161557)
            ·
              refine ⟨2030885416188094082136599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86651111090692014171161557 2030885416188094082136599)
              ·
                refine ⟨3046328124282141123204899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030885416188094082136599 3046328124282141123204899)
                ·
                  refine ⟨4569492186423211684807349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046328124282141123204899 4569492186423211684807349)
                  ·
                    refine ⟨428389892477176095450689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4569492186423211684807349 428389892477176095450689)
                    ·
                      rfl

theorem cell23_2502859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 5].length) (baseStart_2502859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502859 prefixEnd_2502859 := by exact prefixLift 2502859
  have htrace : WordTrace (prefixWord ++ tailWord_2502859) baseStart_2502859 baseEnd_2502859 := by
    simpa [prefixWord, tailWord_2502859, baseEnd_2502859] using wordTrace_append hprefix tailTrace_2502859
  have hstable : (prefixWord ++ tailWord_2502859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502859).length < 2 ^ (prefixWord ++ tailWord_2502859).sum := by decide
  have hdescent : baseEnd_2502859 < baseStart_2502859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502866 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2502866 : Nat := 118140960795 + 2502866 * 2 ^ 59
def prefixEnd_2502866 : Nat := 4983230072969 + 3 ^ 40 * 2502866 * 2
def baseEnd_2502866 : Nat := 1285173271796109758964535

theorem tailTrace_2502866 : CollatzResearch.WordTrace tailWord_2502866 prefixEnd_2502866 1285173271796109758964535 := by
  unfold tailWord_2502866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22821755637637853081610113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60858015033700941550960301 22821755637637853081610113)
  ·
    refine ⟨17116316728228389811207585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22821755637637853081610113 17116316728228389811207585)
    ·
      refine ⟨12837237546171292358405689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17116316728228389811207585 12837237546171292358405689)
      ·
        refine ⟨9627928159628469268804267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12837237546171292358405689 9627928159628469268804267)
        ·
          refine ⟨14441892239442703903206401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9627928159628469268804267 14441892239442703903206401)
          ·
            refine ⟨10831419179582027927404801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14441892239442703903206401 10831419179582027927404801)
            ·
              refine ⟨8123564384686520945553601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10831419179582027927404801 8123564384686520945553601)
              ·
                refine ⟨6092673288514890709165201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8123564384686520945553601 6092673288514890709165201)
                ·
                  refine ⟨4569504966386168031873901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6092673288514890709165201 4569504966386168031873901)
                  ·
                    refine ⟨1713564362394813011952713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4569504966386168031873901 1713564362394813011952713)
                    ·
                      refine ⟨1285173271796109758964535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713564362394813011952713 1285173271796109758964535)
                      ·
                        rfl

theorem cell23_2502866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2502866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502866 prefixEnd_2502866 := by exact prefixLift 2502866
  have htrace : WordTrace (prefixWord ++ tailWord_2502866) baseStart_2502866 baseEnd_2502866 := by
    simpa [prefixWord, tailWord_2502866, baseEnd_2502866] using wordTrace_append hprefix tailTrace_2502866
  have hstable : (prefixWord ++ tailWord_2502866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502866).length < 2 ^ (prefixWord ++ tailWord_2502866).sum := by decide
  have hdescent : baseEnd_2502866 < baseStart_2502866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502873 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 1, 1, 3]
def baseStart_2502873 : Nat := 118140960795 + 2502873 * 2 ^ 59
def prefixEnd_2502873 : Nat := 4983230072969 + 3 ^ 40 * 2502873 * 2
def baseEnd_2502873 : Nat := 1285176866160691231577003

theorem tailTrace_2502873 : CollatzResearch.WordTrace tailWord_2502873 prefixEnd_2502873 1285176866160691231577003 := by
  unfold tailWord_2502873
  simp only [CollatzResearch.WordTrace]
  refine ⟨91287277861526052521945273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60858185241017368347963515 91287277861526052521945273)
  ·
    refine ⟨68465458396144539391458955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91287277861526052521945273 68465458396144539391458955)
    ·
      refine ⟨102698187594216809087188433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68465458396144539391458955 102698187594216809087188433)
      ·
        refine ⟨77023640695662606815391325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102698187594216809087188433 77023640695662606815391325)
        ·
          refine ⟨28883865260873477555771747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77023640695662606815391325 28883865260873477555771747)
          ·
            refine ⟨43325797891310216333657621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28883865260873477555771747 43325797891310216333657621)
            ·
              refine ⟨2030896776155166390640201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43325797891310216333657621 2030896776155166390640201)
              ·
                refine ⟨1523172582116374792980151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030896776155166390640201 1523172582116374792980151)
                ·
                  refine ⟨2284758873174562189470227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523172582116374792980151 2284758873174562189470227)
                  ·
                    refine ⟨3427138309761843284205341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284758873174562189470227 3427138309761843284205341)
                    ·
                      refine ⟨1285176866160691231577003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427138309761843284205341 1285176866160691231577003)
                      ·
                        rfl

theorem cell23_2502873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_2502873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502873 prefixEnd_2502873 := by exact prefixLift 2502873
  have htrace : WordTrace (prefixWord ++ tailWord_2502873) baseStart_2502873 baseEnd_2502873 := by
    simpa [prefixWord, tailWord_2502873, baseEnd_2502873] using wordTrace_append hprefix tailTrace_2502873
  have hstable : (prefixWord ++ tailWord_2502873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502873).length < 2 ^ (prefixWord ++ tailWord_2502873).sum := by decide
  have hdescent : baseEnd_2502873 < baseStart_2502873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502899 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 3]
def baseStart_2502899 : Nat := 118140960795 + 2502899 * 2 ^ 59
def prefixEnd_2502899 : Nat := 4983230072969 + 3 ^ 40 * 2502899 * 2
def baseEnd_2502899 : Nat := 1285190216657708129851883

theorem tailTrace_2502899 : CollatzResearch.WordTrace tailWord_2502899 prefixEnd_2502899 1285190216657708129851883 := by
  unfold tailWord_2502899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91288226159431858962391751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60858817439621239308261167 91288226159431858962391751)
  ·
    refine ⟨136932339239147788443587627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91288226159431858962391751 136932339239147788443587627)
    ·
      refine ⟨205398508858721682665381441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136932339239147788443587627 205398508858721682665381441)
      ·
        refine ⟨154048881644041261999036081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205398508858721682665381441 154048881644041261999036081)
        ·
          refine ⟨115536661233030946499277061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154048881644041261999036081 115536661233030946499277061)
          ·
            refine ⟨21663123981193302468614449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115536661233030946499277061 21663123981193302468614449)
            ·
              refine ⟨16247342985894976851460837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21663123981193302468614449 16247342985894976851460837)
              ·
                refine ⟨3046376809855308159648907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16247342985894976851460837 3046376809855308159648907)
                ·
                  refine ⟨4569565214782962239473361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046376809855308159648907 4569565214782962239473361)
                  ·
                    refine ⟨3427173911087221679605021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4569565214782962239473361 3427173911087221679605021)
                    ·
                      refine ⟨1285190216657708129851883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427173911087221679605021 1285190216657708129851883)
                      ·
                        rfl

theorem cell23_2502899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_2502899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502899 prefixEnd_2502899 := by exact prefixLift 2502899
  have htrace : WordTrace (prefixWord ++ tailWord_2502899) baseStart_2502899 baseEnd_2502899 := by
    simpa [prefixWord, tailWord_2502899, baseEnd_2502899] using wordTrace_append hprefix tailTrace_2502899
  have hstable : (prefixWord ++ tailWord_2502899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502899).length < 2 ^ (prefixWord ++ tailWord_2502899).sum := by decide
  have hdescent : baseEnd_2502899 < baseStart_2502899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502902 : List Nat := [5, 1, 1, 1, 1, 1, 2, 11]
def baseStart_2502902 : Nat := 118140960795 + 2502902 * 2 ^ 59
def prefixEnd_2502902 : Nat := 4983230072969 + 3 ^ 40 * 2502902 * 2
def baseEnd_2502902 : Nat := 47599694707395245115347

theorem tailTrace_2502902 : CollatzResearch.WordTrace tailWord_2502902 prefixEnd_2502902 47599694707395245115347 := by
  unfold tailWord_2502902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705520973651311904671935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60858890385613993649833973 5705520973651311904671935)
  ·
    refine ⟨8558281460476967857007903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5705520973651311904671935 8558281460476967857007903)
    ·
      refine ⟨12837422190715451785511855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558281460476967857007903 12837422190715451785511855)
      ·
        refine ⟨19256133286073177678267783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12837422190715451785511855 19256133286073177678267783)
        ·
          refine ⟨28884199929109766517401675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19256133286073177678267783 28884199929109766517401675)
          ·
            refine ⟨43326299893664649776102513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28884199929109766517401675 43326299893664649776102513)
            ·
              refine ⟨32494724920248487332076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43326299893664649776102513 32494724920248487332076885)
              ·
                refine ⟨47599694707395245115347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32494724920248487332076885 47599694707395245115347)
                ·
                  rfl

theorem cell23_2502902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_2502902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502902 prefixEnd_2502902 := by exact prefixLift 2502902
  have htrace : WordTrace (prefixWord ++ tailWord_2502902) baseStart_2502902 baseEnd_2502902 := by
    simpa [prefixWord, tailWord_2502902, baseEnd_2502902] using wordTrace_append hprefix tailTrace_2502902
  have hstable : (prefixWord ++ tailWord_2502902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502902).length < 2 ^ (prefixWord ++ tailWord_2502902).sum := by decide
  have hdescent : baseEnd_2502902 < baseStart_2502902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502919 : List Nat := [1, 1, 4, 5, 1, 1, 10]
def baseStart_2502919 : Nat := 118140960795 + 2502919 * 2 ^ 59
def prefixEnd_2502919 : Nat := 4983230072969 + 3 ^ 40 * 2502919 * 2
def baseEnd_2502919 : Nat := 15866672670009852488911

theorem tailTrace_2502919 : CollatzResearch.WordTrace tailWord_2502919 prefixEnd_2502919 15866672670009852488911 := by
  unfold tailWord_2502919
  simp only [CollatzResearch.WordTrace]
  refine ⟨91288955619359402378119811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60859303746239601585413207 91288955619359402378119811)
  ·
    refine ⟨136933433429039103567179717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91288955619359402378119811 136933433429039103567179717)
    ·
      refine ⟨25675018767944831918846197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136933433429039103567179717 25675018767944831918846197)
      ·
        refine ⟨2407033009494827992391831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25675018767944831918846197 2407033009494827992391831)
        ·
          refine ⟨3610549514242241988587747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407033009494827992391831 3610549514242241988587747)
          ·
            refine ⟨5415824271363362982881621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610549514242241988587747 5415824271363362982881621)
            ·
              refine ⟨15866672670009852488911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5415824271363362982881621 15866672670009852488911)
              ·
                rfl

theorem cell23_2502919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 10].length) (baseStart_2502919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502919 prefixEnd_2502919 := by exact prefixLift 2502919
  have htrace : WordTrace (prefixWord ++ tailWord_2502919) baseStart_2502919 baseEnd_2502919 := by
    simpa [prefixWord, tailWord_2502919, baseEnd_2502919] using wordTrace_append hprefix tailTrace_2502919
  have hstable : (prefixWord ++ tailWord_2502919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502919).length < 2 ^ (prefixWord ++ tailWord_2502919).sum := by decide
  have hdescent : baseEnd_2502919 < baseStart_2502919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502939 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 5, 3, 2]
def baseStart_2502939 : Nat := 118140960795 + 2502939 * 2 ^ 59
def prefixEnd_2502939 : Nat := 4983230072969 + 3 ^ 40 * 2502939 * 2
def baseEnd_2502939 : Nat := 1285210755883887973351699

theorem tailTrace_2502939 : CollatzResearch.WordTrace tailWord_2502939 prefixEnd_2502939 1285210755883887973351699 := by
  unfold tailWord_2502939
  simp only [CollatzResearch.WordTrace]
  refine ⟨91289685079286945793847871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60859790052857963862565247 91289685079286945793847871)
  ·
    refine ⟨136934527618930418690771807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91289685079286945793847871 136934527618930418690771807)
    ·
      refine ⟨205401791428395628036157711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136934527618930418690771807 205401791428395628036157711)
      ·
        refine ⟨308102687142593442054236567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205401791428395628036157711 308102687142593442054236567)
        ·
          refine ⟨462154030713890163081354851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308102687142593442054236567 462154030713890163081354851)
          ·
            refine ⟨693231046070835244622032277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462154030713890163081354851 693231046070835244622032277)
            ·
              refine ⟨32495205284570402091657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 693231046070835244622032277 32495205284570402091657763)
              ·
                refine ⟨48742807926855603137486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32495205284570402091657763 48742807926855603137486645)
                ·
                  refine ⟨4569638243142712794139373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48742807926855603137486645 4569638243142712794139373)
                  ·
                    refine ⟨1713614341178517297802265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4569638243142712794139373 1713614341178517297802265)
                    ·
                      refine ⟨1285210755883887973351699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713614341178517297802265 1285210755883887973351699)
                      ·
                        rfl

theorem cell23_2502939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3, 2].length) (baseStart_2502939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502939 prefixEnd_2502939 := by exact prefixLift 2502939
  have htrace : WordTrace (prefixWord ++ tailWord_2502939) baseStart_2502939 baseEnd_2502939 := by
    simpa [prefixWord, tailWord_2502939, baseEnd_2502939] using wordTrace_append hprefix tailTrace_2502939
  have hstable : (prefixWord ++ tailWord_2502939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502939).length < 2 ^ (prefixWord ++ tailWord_2502939).sum := by decide
  have hdescent : baseEnd_2502939 < baseStart_2502939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502946 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2502946 : Nat := 118140960795 + 2502946 * 2 ^ 59
def prefixEnd_2502946 : Nat := 4983230072969 + 3 ^ 40 * 2502946 * 2
def baseEnd_2502946 : Nat := 1285214350248469445964167

theorem tailTrace_2502946 : CollatzResearch.WordTrace tailWord_2502946 prefixEnd_2502946 1285214350248469445964167 := by
  unfold tailWord_2502946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22822485097565396497338173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60859960260174390659568461 22822485097565396497338173)
  ·
    refine ⟨8558431911587023686501815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22822485097565396497338173 8558431911587023686501815)
    ·
      refine ⟨12837647867380535529752723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558431911587023686501815 12837647867380535529752723)
      ·
        refine ⟨19256471801070803294629085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12837647867380535529752723 19256471801070803294629085)
        ·
          refine ⟨7221176925401551235485907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19256471801070803294629085 7221176925401551235485907)
          ·
            refine ⟨10831765388102326853228861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221176925401551235485907 10831765388102326853228861)
            ·
              refine ⟨4061912020538372569960823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10831765388102326853228861 4061912020538372569960823)
              ·
                refine ⟨6092868030807558854941235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061912020538372569960823 6092868030807558854941235)
                ·
                  refine ⟨9139302046211338282411853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092868030807558854941235 9139302046211338282411853)
                  ·
                    refine ⟨3427238267329251855904445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9139302046211338282411853 3427238267329251855904445)
                    ·
                      refine ⟨1285214350248469445964167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427238267329251855904445 1285214350248469445964167)
                      ·
                        rfl

theorem cell23_2502946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2502946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502946 prefixEnd_2502946 := by exact prefixLift 2502946
  have htrace : WordTrace (prefixWord ++ tailWord_2502946) baseStart_2502946 baseEnd_2502946 := by
    simpa [prefixWord, tailWord_2502946, baseEnd_2502946] using wordTrace_append hprefix tailTrace_2502946
  have hstable : (prefixWord ++ tailWord_2502946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502946).length < 2 ^ (prefixWord ++ tailWord_2502946).sum := by decide
  have hdescent : baseEnd_2502946 < baseStart_2502946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502956 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_2502956 : Nat := 118140960795 + 2502956 * 2 ^ 59
def prefixEnd_2502956 : Nat := 4983230072969 + 3 ^ 40 * 2502956 * 2
def baseEnd_2502956 : Nat := 1285219485055014406839121

theorem tailTrace_2502956 : CollatzResearch.WordTrace tailWord_2502956 prefixEnd_2502956 1285219485055014406839121 := by
  unfold tailWord_2502956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45645152560112678848608361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60860203413483571798144481 45645152560112678848608361)
  ·
    refine ⟨34233864420084509136456271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45645152560112678848608361 34233864420084509136456271)
    ·
      refine ⟨51350796630126763704684407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34233864420084509136456271 51350796630126763704684407)
      ·
        refine ⟨77026194945190145557026611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51350796630126763704684407 77026194945190145557026611)
        ·
          refine ⟨115539292417785218335539917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77026194945190145557026611 115539292417785218335539917)
          ·
            refine ⟨43327234656669456875827469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115539292417785218335539917 43327234656669456875827469)
            ·
              refine ⟨16247712996251046328435301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43327234656669456875827469 16247712996251046328435301)
              ·
                refine ⟨3046446186797071186581619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16247712996251046328435301 3046446186797071186581619)
                ·
                  refine ⟨4569669280195606779872429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046446186797071186581619 4569669280195606779872429)
                  ·
                    refine ⟨1713625980073352542452161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4569669280195606779872429 1713625980073352542452161)
                    ·
                      refine ⟨1285219485055014406839121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713625980073352542452161 1285219485055014406839121)
                      ·
                        rfl

theorem cell23_2502956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_2502956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502956 prefixEnd_2502956 := by exact prefixLift 2502956
  have htrace : WordTrace (prefixWord ++ tailWord_2502956) baseStart_2502956 baseEnd_2502956 := by
    simpa [prefixWord, tailWord_2502956, baseEnd_2502956] using wordTrace_append hprefix tailTrace_2502956
  have hstable : (prefixWord ++ tailWord_2502956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502956).length < 2 ^ (prefixWord ++ tailWord_2502956).sum := by decide
  have hdescent : baseEnd_2502956 < baseStart_2502956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502997 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2502997 : Nat := 118140960795 + 2502997 * 2 ^ 59
def prefixEnd_2502997 : Nat := 4983230072969 + 3 ^ 40 * 2502997 * 2
def baseEnd_2502997 : Nat := 1285240537761848746426433

theorem tailTrace_2502997 : CollatzResearch.WordTrace tailWord_2502997 prefixEnd_2502997 1285240537761848746426433 := by
  unfold tailWord_2502997
  simp only [CollatzResearch.WordTrace]
  refine ⟨91291800513076821699459245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60861200342051214466306163 91291800513076821699459245)
  ·
    refine ⟨34234425192403808137297217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91291800513076821699459245 34234425192403808137297217)
    ·
      refine ⟨25675818894302856102972913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34234425192403808137297217 25675818894302856102972913)
      ·
        refine ⟨19256864170727142077229685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25675818894302856102972913 19256864170727142077229685)
        ·
          refine ⟨1805331016005669569740283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19256864170727142077229685 1805331016005669569740283)
          ·
            refine ⟨2707996524008504354610425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805331016005669569740283 2707996524008504354610425)
            ·
              refine ⟨2030997393006378265957819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707996524008504354610425 2030997393006378265957819)
              ·
                refine ⟨3046496089509567398936729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030997393006378265957819 3046496089509567398936729)
                ·
                  refine ⟨2284872067132175549202547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3046496089509567398936729 2284872067132175549202547)
                  ·
                    refine ⟨3427308100698263323803821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284872067132175549202547 3427308100698263323803821)
                    ·
                      refine ⟨1285240537761848746426433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427308100698263323803821 1285240537761848746426433)
                      ·
                        rfl

theorem cell23_2502997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2502997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2502997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2502997 prefixEnd_2502997 := by exact prefixLift 2502997
  have htrace : WordTrace (prefixWord ++ tailWord_2502997) baseStart_2502997 baseEnd_2502997 := by
    simpa [prefixWord, tailWord_2502997, baseEnd_2502997] using wordTrace_append hprefix tailTrace_2502997
  have hstable : (prefixWord ++ tailWord_2502997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502997).length < 2 ^ (prefixWord ++ tailWord_2502997).sum := by decide
  have hdescent : baseEnd_2502997 < baseStart_2502997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503049 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_2503049 : Nat := 118140960795 + 2503049 * 2 ^ 59
def prefixEnd_2503049 : Nat := 4983230072969 + 3 ^ 40 * 2503049 * 2
def baseEnd_2503049 : Nat := 1285267238755882542976193

theorem tailTrace_2503049 : CollatzResearch.WordTrace tailWord_2503049 prefixEnd_2503049 1285267238755882542976193 := by
  unfold tailWord_2503049
  simp only [CollatzResearch.WordTrace]
  refine ⟨91293697108888434580352201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60862464739258956386901467 91293697108888434580352201)
  ·
    refine ⟨68470272831666325935264151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91293697108888434580352201 68470272831666325935264151)
    ·
      refine ⟨102705409247499488902896227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68470272831666325935264151 102705409247499488902896227)
      ·
        refine ⟨154058113871249233354344341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102705409247499488902896227 154058113871249233354344341)
        ·
          refine ⟨7221474087714807813484891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154058113871249233354344341 7221474087714807813484891)
          ·
            refine ⟨10832211131572211720227337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221474087714807813484891 10832211131572211720227337)
            ·
              refine ⟨8124158348679158790170503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10832211131572211720227337 8124158348679158790170503)
              ·
                refine ⟨12186237523018738185255755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124158348679158790170503 12186237523018738185255755)
                ·
                  refine ⟨18279356284528107277883633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12186237523018738185255755 18279356284528107277883633)
                  ·
                    refine ⟨13709517213396080458412725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18279356284528107277883633 13709517213396080458412725)
                    ·
                      refine ⟨1285267238755882542976193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13709517213396080458412725 1285267238755882542976193)
                      ·
                        rfl

theorem cell23_2503049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_2503049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503049 prefixEnd_2503049 := by exact prefixLift 2503049
  have htrace : WordTrace (prefixWord ++ tailWord_2503049) baseStart_2503049 baseEnd_2503049 := by
    simpa [prefixWord, tailWord_2503049, baseEnd_2503049] using wordTrace_append hprefix tailTrace_2503049
  have hstable : (prefixWord ++ tailWord_2503049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503049).length < 2 ^ (prefixWord ++ tailWord_2503049).sum := by decide
  have hdescent : baseEnd_2503049 < baseStart_2503049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503076 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_2503076 : Nat := 118140960795 + 2503076 * 2 ^ 59
def prefixEnd_2503076 : Nat := 4983230072969 + 3 ^ 40 * 2503076 * 2
def baseEnd_2503076 : Nat := 1285281102733553937338569

theorem tailTrace_2503076 : CollatzResearch.WordTrace tailWord_2503076 prefixEnd_2503076 1285281102733553937338569 := by
  unfold tailWord_2503076
  simp only [CollatzResearch.WordTrace]
  refine ⟨45647340939895309095792541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60863121253193745461056721 45647340939895309095792541)
  ·
    refine ⟨17117752852460740910922203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45647340939895309095792541 17117752852460740910922203)
    ·
      refine ⟨25676629278691111366383305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117752852460740910922203 25676629278691111366383305)
      ·
        refine ⟨19257471959018333524787479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25676629278691111366383305 19257471959018333524787479)
        ·
          refine ⟨28886207938527500287181219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257471959018333524787479 28886207938527500287181219)
          ·
            refine ⟨43329311907791250430771829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886207938527500287181219 43329311907791250430771829)
            ·
              refine ⟨4062122991355429727884859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43329311907791250430771829 4062122991355429727884859)
              ·
                refine ⟨6093184487033144591827289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062122991355429727884859 6093184487033144591827289)
                ·
                  refine ⟨4569888365274858443870467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093184487033144591827289 4569888365274858443870467)
                  ·
                    refine ⟨6854832547912287665805701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569888365274858443870467 6854832547912287665805701)
                    ·
                      refine ⟨1285281102733553937338569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6854832547912287665805701 1285281102733553937338569)
                      ·
                        rfl

theorem cell23_2503076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_2503076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503076 prefixEnd_2503076 := by exact prefixLift 2503076
  have htrace : WordTrace (prefixWord ++ tailWord_2503076) baseStart_2503076 baseEnd_2503076 := by
    simpa [prefixWord, tailWord_2503076, baseEnd_2503076] using wordTrace_append hprefix tailTrace_2503076
  have hstable : (prefixWord ++ tailWord_2503076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503076).length < 2 ^ (prefixWord ++ tailWord_2503076).sum := by decide
  have hdescent : baseEnd_2503076 < baseStart_2503076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503089 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2503089 : Nat := 118140960795 + 2503089 * 2 ^ 59
def prefixEnd_2503089 : Nat := 4983230072969 + 3 ^ 40 * 2503089 * 2
def baseEnd_2503089 : Nat := 1285287777982062386476009

theorem tailTrace_2503089 : CollatzResearch.WordTrace tailWord_2503089 prefixEnd_2503089 1285287777982062386476009 := by
  unfold tailWord_2503089
  simp only [CollatzResearch.WordTrace]
  refine ⟨91295156028743521411808321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60863437352495680941205547 91295156028743521411808321)
  ·
    refine ⟨68471367021557641058856241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91295156028743521411808321 68471367021557641058856241)
    ·
      refine ⟨51353525266168230794142181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68471367021557641058856241 51353525266168230794142181)
      ·
        refine ⟨9628785987406543273901659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51353525266168230794142181 9628785987406543273901659)
        ·
          refine ⟨14443178981109814910852489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628785987406543273901659 14443178981109814910852489)
          ·
            refine ⟨10832384235832361183139367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14443178981109814910852489 10832384235832361183139367)
            ·
              refine ⟨16248576353748541774709051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832384235832361183139367 16248576353748541774709051)
              ·
                refine ⟨24372864530622812662063577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16248576353748541774709051 24372864530622812662063577)
                ·
                  refine ⟨18279648397967109496547683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24372864530622812662063577 18279648397967109496547683)
                  ·
                    refine ⟨27419472596950664244821525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18279648397967109496547683 27419472596950664244821525)
                    ·
                      refine ⟨1285287777982062386476009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27419472596950664244821525 1285287777982062386476009)
                      ·
                        rfl

theorem cell23_2503089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2503089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503089 prefixEnd_2503089 := by exact prefixLift 2503089
  have htrace : WordTrace (prefixWord ++ tailWord_2503089) baseStart_2503089 baseEnd_2503089 := by
    simpa [prefixWord, tailWord_2503089, baseEnd_2503089] using wordTrace_append hprefix tailTrace_2503089
  have hstable : (prefixWord ++ tailWord_2503089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503089).length < 2 ^ (prefixWord ++ tailWord_2503089).sum := by decide
  have hdescent : baseEnd_2503089 < baseStart_2503089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503136 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2]
def baseStart_2503136 : Nat := 118140960795 + 2503136 * 2 ^ 59
def prefixEnd_2503136 : Nat := 4983230072969 + 3 ^ 40 * 2503136 * 2
def baseEnd_2503136 : Nat := 1285311911572823702588293

theorem tailTrace_2503136 : CollatzResearch.WordTrace tailWord_2503136 prefixEnd_2503136 1285311911572823702588293 := by
  unfold tailWord_2503136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45648435129786624219384631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60864580173048832292512841 45648435129786624219384631)
  ·
    refine ⟨68472652694679936329076947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45648435129786624219384631 68472652694679936329076947)
    ·
      refine ⟨102708979042019904493615421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68472652694679936329076947 102708979042019904493615421)
      ·
        refine ⟨38515867140757464185105783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102708979042019904493615421 38515867140757464185105783)
        ·
          refine ⟨57773800711136196277658675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38515867140757464185105783 57773800711136196277658675)
          ·
            refine ⟨86660701066704294416488013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57773800711136196277658675 86660701066704294416488013)
            ·
              refine ⟨32497762900014110406183005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86660701066704294416488013 32497762900014110406183005)
              ·
                refine ⟨12186661087505291402318627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32497762900014110406183005 12186661087505291402318627)
                ·
                  refine ⟨18279991631257937103477941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12186661087505291402318627 18279991631257937103477941)
                  ·
                    refine ⟨1713749215430431603451057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18279991631257937103477941 1713749215430431603451057)
                    ·
                      refine ⟨1285311911572823702588293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713749215430431603451057 1285311911572823702588293)
                      ·
                        rfl

theorem cell23_2503136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_2503136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503136 prefixEnd_2503136 := by exact prefixLift 2503136
  have htrace : WordTrace (prefixWord ++ tailWord_2503136) baseStart_2503136 baseEnd_2503136 := by
    simpa [prefixWord, tailWord_2503136, baseEnd_2503136] using wordTrace_append hprefix tailTrace_2503136
  have hstable : (prefixWord ++ tailWord_2503136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503136).length < 2 ^ (prefixWord ++ tailWord_2503136).sum := by decide
  have hdescent : baseEnd_2503136 < baseStart_2503136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503153 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_2503153 : Nat := 118140960795 + 2503153 * 2 ^ 59
def prefixEnd_2503153 : Nat := 4983230072969 + 3 ^ 40 * 2503153 * 2
def baseEnd_2503153 : Nat := 1285320640743950136075715

theorem tailTrace_2503153 : CollatzResearch.WordTrace tailWord_2503153 prefixEnd_2503153 1285320640743950136075715 := by
  unfold tailWord_2503153
  simp only [CollatzResearch.WordTrace]
  refine ⟨91297490300511660342138113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60864993533674440228092075 91297490300511660342138113)
  ·
    refine ⟨68473117725383745256603585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91297490300511660342138113 68473117725383745256603585)
    ·
      refine ⟨51354838294037808942452689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68473117725383745256603585 51354838294037808942452689)
      ·
        refine ⟨38516128720528356706839517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51354838294037808942452689 38516128720528356706839517)
        ·
          refine ⟨14443548270198133765064819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38516128720528356706839517 14443548270198133765064819)
          ·
            refine ⟨21665322405297200647597229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14443548270198133765064819 21665322405297200647597229)
            ·
              refine ⟨8124495901986450242848961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21665322405297200647597229 8124495901986450242848961)
              ·
                refine ⟨6093371926489837682136721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8124495901986450242848961 6093371926489837682136721)
                ·
                  refine ⟨4570028944867378261602541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093371926489837682136721 4570028944867378261602541)
                  ·
                    refine ⟨1713760854325266848100953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4570028944867378261602541 1713760854325266848100953)
                    ·
                      refine ⟨1285320640743950136075715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713760854325266848100953 1285320640743950136075715)
                      ·
                        rfl

theorem cell23_2503153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_2503153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503153 prefixEnd_2503153 := by exact prefixLift 2503153
  have htrace : WordTrace (prefixWord ++ tailWord_2503153) baseStart_2503153 baseEnd_2503153 := by
    simpa [prefixWord, tailWord_2503153, baseEnd_2503153] using wordTrace_append hprefix tailTrace_2503153
  have hstable : (prefixWord ++ tailWord_2503153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503153).length < 2 ^ (prefixWord ++ tailWord_2503153).sum := by decide
  have hdescent : baseEnd_2503153 < baseStart_2503153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503189 : List Nat := [1, 3, 2, 1, 3, 1, 1, 11]
def baseStart_2503189 : Nat := 118140960795 + 2503189 * 2 ^ 59
def prefixEnd_2503189 : Nat := 4983230072969 + 3 ^ 40 * 2503189 * 2
def baseEnd_2503189 : Nat := 47605152816574518341687

theorem tailTrace_2503189 : CollatzResearch.WordTrace tailWord_2503189 prefixEnd_2503189 47605152816574518341687 := by
  unfold tailWord_2503189
  simp only [CollatzResearch.WordTrace]
  refine ⟨91298803328381238490448621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60865868885587492326965747 91298803328381238490448621)
  ·
    refine ⟨34237051248142964433918233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91298803328381238490448621 34237051248142964433918233)
    ·
      refine ⟨25677788436107223325438675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34237051248142964433918233 25677788436107223325438675)
      ·
        refine ⟨38516682654160834988158013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25677788436107223325438675 38516682654160834988158013)
        ·
          refine ⟨14443755995310313120559255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38516682654160834988158013 14443755995310313120559255)
          ·
            refine ⟨21665633992965469680838883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14443755995310313120559255 21665633992965469680838883)
            ·
              refine ⟨32498450989448204521258325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21665633992965469680838883 32498450989448204521258325)
              ·
                refine ⟨47605152816574518341687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32498450989448204521258325 47605152816574518341687)
                ·
                  rfl

theorem cell23_2503189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 11].length) (baseStart_2503189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503189 prefixEnd_2503189 := by exact prefixLift 2503189
  have htrace : WordTrace (prefixWord ++ tailWord_2503189) baseStart_2503189 baseEnd_2503189 := by
    simpa [prefixWord, tailWord_2503189, baseEnd_2503189] using wordTrace_append hprefix tailTrace_2503189
  have hstable : (prefixWord ++ tailWord_2503189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503189).length < 2 ^ (prefixWord ++ tailWord_2503189).sum := by decide
  have hdescent : baseEnd_2503189 < baseStart_2503189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503196 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2503196 : Nat := 118140960795 + 2503196 * 2 ^ 59
def prefixEnd_2503196 : Nat := 4983230072969 + 3 ^ 40 * 2503196 * 2
def baseEnd_2503196 : Nat := 1285342720412093467838017

theorem tailTrace_2503196 : CollatzResearch.WordTrace tailWord_2503196 prefixEnd_2503196 1285342720412093467838017 := by
  unfold tailWord_2503196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45649529319677939342976721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60866039092903919123968961 45649529319677939342976721)
  ·
    refine ⟨34237146989758454507232541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45649529319677939342976721 34237146989758454507232541)
    ·
      refine ⟨12838930121159420440212203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34237146989758454507232541 12838930121159420440212203)
      ·
        refine ⟨19258395181739130660318305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838930121159420440212203 19258395181739130660318305)
        ·
          refine ⟨14443796386304347995238729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19258395181739130660318305 14443796386304347995238729)
          ·
            refine ⟨10832847289728260996429047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14443796386304347995238729 10832847289728260996429047)
            ·
              refine ⟨16249270934592391494643571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832847289728260996429047 16249270934592391494643571)
              ·
                refine ⟨24373906401888587241965357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16249270934592391494643571 24373906401888587241965357)
                ·
                  refine ⟨9140214900708220215737009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24373906401888587241965357 9140214900708220215737009)
                  ·
                    refine ⟨6855161175531165161802757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9140214900708220215737009 6855161175531165161802757)
                    ·
                      refine ⟨1285342720412093467838017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6855161175531165161802757 1285342720412093467838017)
                      ·
                        rfl

theorem cell23_2503196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2503196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503196 prefixEnd_2503196 := by exact prefixLift 2503196
  have htrace : WordTrace (prefixWord ++ tailWord_2503196) baseStart_2503196 baseEnd_2503196 := by
    simpa [prefixWord, tailWord_2503196, baseEnd_2503196] using wordTrace_append hprefix tailTrace_2503196
  have hstable : (prefixWord ++ tailWord_2503196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503196).length < 2 ^ (prefixWord ++ tailWord_2503196).sum := by decide
  have hdescent : baseEnd_2503196 < baseStart_2503196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503203 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 5]
def baseStart_2503203 : Nat := 118140960795 + 2503203 * 2 ^ 59
def prefixEnd_2503203 : Nat := 4983230072969 + 3 ^ 40 * 2503203 * 2
def baseEnd_2503203 : Nat := 1285346314776674940450485

theorem tailTrace_2503203 : CollatzResearch.WordTrace tailWord_2503203 prefixEnd_2503203 1285346314776674940450485 := by
  unfold tailWord_2503203
  simp only [CollatzResearch.WordTrace]
  refine ⟨91299313950330518881458263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60866209300220345920972175 91299313950330518881458263)
  ·
    refine ⟨136948970925495778322187395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91299313950330518881458263 136948970925495778322187395)
    ·
      refine ⟨205423456388243667483281093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136948970925495778322187395 205423456388243667483281093)
      ·
        refine ⟨38516898072795687653115205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205423456388243667483281093 38516898072795687653115205)
        ·
          refine ⟨7221918388649191434959101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38516898072795687653115205 7221918388649191434959101)
          ·
            refine ⟨2708219395743446788109663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7221918388649191434959101 2708219395743446788109663)
            ·
              refine ⟨4062329093615170182164495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708219395743446788109663 4062329093615170182164495)
              ·
                refine ⟨6093493640422755273246743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062329093615170182164495 6093493640422755273246743)
                ·
                  refine ⟨9140240460634132909870115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093493640422755273246743 9140240460634132909870115)
                  ·
                    refine ⟨13710360690951199364805173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9140240460634132909870115 13710360690951199364805173)
                    ·
                      refine ⟨1285346314776674940450485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13710360690951199364805173 1285346314776674940450485)
                      ·
                        rfl

theorem cell23_2503203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_2503203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503203 prefixEnd_2503203 := by exact prefixLift 2503203
  have htrace : WordTrace (prefixWord ++ tailWord_2503203) baseStart_2503203 baseEnd_2503203 := by
    simpa [prefixWord, tailWord_2503203, baseEnd_2503203] using wordTrace_append hprefix tailTrace_2503203
  have hstable : (prefixWord ++ tailWord_2503203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503203).length < 2 ^ (prefixWord ++ tailWord_2503203).sum := by decide
  have hdescent : baseEnd_2503203 < baseStart_2503203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503210 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2503210 : Nat := 118140960795 + 2503210 * 2 ^ 59
def prefixEnd_2503210 : Nat := 4983230072969 + 3 ^ 40 * 2503210 * 2
def baseEnd_2503210 : Nat := 428449969713752137687651

theorem tailTrace_2503210 : CollatzResearch.WordTrace tailWord_2503210 prefixEnd_2503210 428449969713752137687651 := by
  unfold tailWord_2503210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22824892315326289769240771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60866379507536772717975389 22824892315326289769240771)
  ·
    refine ⟨34237338472989434653861157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22824892315326289769240771 34237338472989434653861157)
    ·
      refine ⟨6419500963685518997598967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34237338472989434653861157 6419500963685518997598967)
      ·
        refine ⟨9629251445528278496398451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419500963685518997598967 9629251445528278496398451)
        ·
          refine ⟨14443877168292417744597677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9629251445528278496398451 14443877168292417744597677)
          ·
            refine ⟨5416453938109656654224129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14443877168292417744597677 5416453938109656654224129)
            ·
              refine ⟨4062340453582242490668097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5416453938109656654224129 4062340453582242490668097)
              ·
                refine ⟨3046755340186681868001073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4062340453582242490668097 3046755340186681868001073)
                ·
                  refine ⟨2285066505140011401000805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3046755340186681868001073 2285066505140011401000805)
                  ·
                    refine ⟨428449969713752137687651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285066505140011401000805 428449969713752137687651)
                    ·
                      rfl

theorem cell23_2503210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2503210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503210 prefixEnd_2503210 := by exact prefixLift 2503210
  have htrace : WordTrace (prefixWord ++ tailWord_2503210) baseStart_2503210 baseEnd_2503210 := by
    simpa [prefixWord, tailWord_2503210, baseEnd_2503210] using wordTrace_append hprefix tailTrace_2503210
  have hstable : (prefixWord ++ tailWord_2503210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503210).length < 2 ^ (prefixWord ++ tailWord_2503210).sum := by decide
  have hdescent : baseEnd_2503210 < baseStart_2503210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503219 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 9]
def baseStart_2503219 : Nat := 118140960795 + 2503219 * 2 ^ 59
def prefixEnd_2503219 : Nat := 4983230072969 + 3 ^ 40 * 2503219 * 2
def baseEnd_2503219 : Nat := 428451510155715625950137

theorem tailTrace_2503219 : CollatzResearch.WordTrace tailWord_2503219 prefixEnd_2503219 428451510155715625950137 := by
  unfold tailWord_2503219
  simp only [CollatzResearch.WordTrace]
  refine ⟨91299897518272553614040711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60866598345515035742693807 91299897518272553614040711)
  ·
    refine ⟨136949846277408830421061067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91299897518272553614040711 136949846277408830421061067)
    ·
      refine ⟨205424769416113245631591601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136949846277408830421061067 205424769416113245631591601)
      ·
        refine ⟨154068577062084934223693701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205424769416113245631591601 154068577062084934223693701)
        ·
          refine ⟨28887858199140925166942569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154068577062084934223693701 28887858199140925166942569)
          ·
            refine ⟨21665893649355693875206927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28887858199140925166942569 21665893649355693875206927)
            ·
              refine ⟨32498840474033540812810391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21665893649355693875206927 32498840474033540812810391)
              ·
                refine ⟨48748260711050311219215587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32498840474033540812810391 48748260711050311219215587)
                ·
                  refine ⟨73122391066575466828823381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48748260711050311219215587 73122391066575466828823381)
                  ·
                    refine ⟨428451510155715625950137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73122391066575466828823381 428451510155715625950137)
                    ·
                      rfl

theorem cell23_2503219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_2503219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503219 prefixEnd_2503219 := by exact prefixLift 2503219
  have htrace : WordTrace (prefixWord ++ tailWord_2503219) baseStart_2503219 baseEnd_2503219 := by
    simpa [prefixWord, tailWord_2503219, baseEnd_2503219] using wordTrace_append hprefix tailTrace_2503219
  have hstable : (prefixWord ++ tailWord_2503219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503219).length < 2 ^ (prefixWord ++ tailWord_2503219).sum := by decide
  have hdescent : baseEnd_2503219 < baseStart_2503219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503233 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2503233 : Nat := 118140960795 + 2503233 * 2 ^ 59
def prefixEnd_2503233 : Nat := 4983230072969 + 3 ^ 40 * 2503233 * 2
def baseEnd_2503233 : Nat := 1285361719196309823075347

theorem tailTrace_2503233 : CollatzResearch.WordTrace tailWord_2503233 prefixEnd_2503233 1285361719196309823075347 := by
  unfold tailWord_2503233
  simp only [CollatzResearch.WordTrace]
  refine ⟨91300408140221834005050353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60866938760147889336700235 91300408140221834005050353)
  ·
    refine ⟨68475306105166375503787765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91300408140221834005050353 68475306105166375503787765)
    ·
      refine ⟨6419559947359347703480103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68475306105166375503787765 6419559947359347703480103)
      ·
        refine ⟨9629339921039021555220155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419559947359347703480103 9629339921039021555220155)
        ·
          refine ⟨14444009881558532332830233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9629339921039021555220155 14444009881558532332830233)
          ·
            refine ⟨10833007411168899249622675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14444009881558532332830233 10833007411168899249622675)
            ·
              refine ⟨16249511116753348874434013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10833007411168899249622675 16249511116753348874434013)
              ·
                refine ⟨6093566668782505827912755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16249511116753348874434013 6093566668782505827912755)
                ·
                  refine ⟨9140350003173758741869133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093566668782505827912755 9140350003173758741869133)
                  ·
                    refine ⟨3427631251190159528200925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9140350003173758741869133 3427631251190159528200925)
                    ·
                      refine ⟨1285361719196309823075347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427631251190159528200925 1285361719196309823075347)
                      ·
                        rfl

theorem cell23_2503233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2503233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503233 prefixEnd_2503233 := by exact prefixLift 2503233
  have htrace : WordTrace (prefixWord ++ tailWord_2503233) baseStart_2503233 baseEnd_2503233 := by
    simpa [prefixWord, tailWord_2503233, baseEnd_2503233] using wordTrace_append hprefix tailTrace_2503233
  have hstable : (prefixWord ++ tailWord_2503233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503233).length < 2 ^ (prefixWord ++ tailWord_2503233).sum := by decide
  have hdescent : baseEnd_2503233 < baseStart_2503233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503243 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 3, 3, 2]
def baseStart_2503243 : Nat := 118140960795 + 2503243 * 2 ^ 59
def prefixEnd_2503243 : Nat := 4983230072969 + 3 ^ 40 * 2503243 * 2
def baseEnd_2503243 : Nat := 1285366854002854783950301

theorem tailTrace_2503243 : CollatzResearch.WordTrace tailWord_2503243 prefixEnd_2503243 1285366854002854783950301 := by
  unfold tailWord_2503243
  simp only [CollatzResearch.WordTrace]
  refine ⟨91300772870185605712914383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60867181913457070475276255 91300772870185605712914383)
  ·
    refine ⟨136951159305278408569371575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91300772870185605712914383 136951159305278408569371575)
    ·
      refine ⟨205426738957917612854057363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136951159305278408569371575 205426738957917612854057363)
      ·
        refine ⟨308140108436876419281086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205426738957917612854057363 308140108436876419281086045)
        ·
          refine ⟨115552540663828657230407267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308140108436876419281086045 115552540663828657230407267)
          ·
            refine ⟨173328810995742985845610901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115552540663828657230407267 173328810995742985845610901)
            ·
              refine ⟨8124788015425452461513011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173328810995742985845610901 8124788015425452461513011)
              ·
                refine ⟨12187182023138178692269517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124788015425452461513011 12187182023138178692269517)
                ·
                  refine ⟨4570193258676817009601069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12187182023138178692269517 4570193258676817009601069)
                  ·
                    refine ⟨1713822472003806378600401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4570193258676817009601069 1713822472003806378600401)
                    ·
                      refine ⟨1285366854002854783950301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713822472003806378600401 1285366854002854783950301)
                      ·
                        rfl

theorem cell23_2503243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3, 2].length) (baseStart_2503243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503243 prefixEnd_2503243 := by exact prefixLift 2503243
  have htrace : WordTrace (prefixWord ++ tailWord_2503243) baseStart_2503243 baseEnd_2503243 := by
    simpa [prefixWord, tailWord_2503243, baseEnd_2503243] using wordTrace_append hprefix tailTrace_2503243
  have hstable : (prefixWord ++ tailWord_2503243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503243).length < 2 ^ (prefixWord ++ tailWord_2503243).sum := by decide
  have hdescent : baseEnd_2503243 < baseStart_2503243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503276 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2503276 : Nat := 118140960795 + 2503276 * 2 ^ 59
def prefixEnd_2503276 : Nat := 4983230072969 + 3 ^ 40 * 2503276 * 2
def baseEnd_2503276 : Nat := 1285383798864453154837649

theorem tailTrace_2503276 : CollatzResearch.WordTrace tailWord_2503276 prefixEnd_2503276 1285383798864453154837649 := by
  unfold tailWord_2503276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45650988239533026174432841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60867984319377368232577121 45650988239533026174432841)
  ·
    refine ⟨34238241179649769630824631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45650988239533026174432841 34238241179649769630824631)
    ·
      refine ⟨51357361769474654446236947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34238241179649769630824631 51357361769474654446236947)
      ·
        refine ⟨77036042654211981669355421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51357361769474654446236947 77036042654211981669355421)
        ·
          refine ⟨28888515995329493126008283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77036042654211981669355421 28888515995329493126008283)
          ·
            refine ⟨43332773992994239689012425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28888515995329493126008283 43332773992994239689012425)
            ·
              refine ⟨32499580494745679766759319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43332773992994239689012425 32499580494745679766759319)
              ·
                refine ⟨48749370742118519650138979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32499580494745679766759319 48749370742118519650138979)
                ·
                  refine ⟨73124056113177779475208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48749370742118519650138979 73124056113177779475208469)
                  ·
                    refine ⟨3427690130305208412900397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73124056113177779475208469 3427690130305208412900397)
                    ·
                      refine ⟨1285383798864453154837649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3427690130305208412900397 1285383798864453154837649)
                      ·
                        rfl

theorem cell23_2503276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2503276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503276 prefixEnd_2503276 := by exact prefixLift 2503276
  have htrace : WordTrace (prefixWord ++ tailWord_2503276) baseStart_2503276 baseEnd_2503276 := by
    simpa [prefixWord, tailWord_2503276, baseEnd_2503276] using wordTrace_append hprefix tailTrace_2503276
  have hstable : (prefixWord ++ tailWord_2503276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503276).length < 2 ^ (prefixWord ++ tailWord_2503276).sum := by decide
  have hdescent : baseEnd_2503276 < baseStart_2503276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503296 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 7]
def baseStart_2503296 : Nat := 118140960795 + 2503296 * 2 ^ 59
def prefixEnd_2503296 : Nat := 4983230072969 + 3 ^ 40 * 2503296 * 2
def baseEnd_2503296 : Nat := 142821563164171452954173

theorem tailTrace_2503296 : CollatzResearch.WordTrace tailWord_2503296 prefixEnd_2503296 142821563164171452954173 := by
  unfold tailWord_2503296
  simp only [CollatzResearch.WordTrace]
  refine ⟨45651352969496797882296871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60868470625995730509729161 45651352969496797882296871)
  ·
    refine ⟨68477029454245196823445307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45651352969496797882296871 68477029454245196823445307)
    ·
      refine ⟨102715544181367795235167961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68477029454245196823445307 102715544181367795235167961)
      ·
        refine ⟨77036658136025846426375971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102715544181367795235167961 77036658136025846426375971)
        ·
          refine ⟨115554987204038769639563957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77036658136025846426375971 115554987204038769639563957)
          ·
            refine ⟨10833280050378634653709121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115554987204038769639563957 10833280050378634653709121)
            ·
              refine ⟨8124960037783975990281841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10833280050378634653709121 8124960037783975990281841)
              ·
                refine ⟨6093720028337981992711381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8124960037783975990281841 6093720028337981992711381)
                ·
                  refine ⟨142821563164171452954173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6093720028337981992711381 142821563164171452954173)
                  ·
                    rfl

theorem cell23_2503296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_2503296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503296 prefixEnd_2503296 := by exact prefixLift 2503296
  have htrace : WordTrace (prefixWord ++ tailWord_2503296) baseStart_2503296 baseEnd_2503296 := by
    simpa [prefixWord, tailWord_2503296, baseEnd_2503296] using wordTrace_append hprefix tailTrace_2503296
  have hstable : (prefixWord ++ tailWord_2503296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503296).length < 2 ^ (prefixWord ++ tailWord_2503296).sum := by decide
  have hdescent : baseEnd_2503296 < baseStart_2503296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503333 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_2503333 : Nat := 118140960795 + 2503333 * 2 ^ 59
def prefixEnd_2503333 : Nat := 4983230072969 + 3 ^ 40 * 2503333 * 2
def baseEnd_2503333 : Nat := 1285413067261759431824887

theorem tailTrace_2503333 : CollatzResearch.WordTrace tailWord_2503333 prefixEnd_2503333 1285413067261759431824887 := by
  unfold tailWord_2503333
  simp only [CollatzResearch.WordTrace]
  refine ⟨91304055439859551083690653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60869370293239700722460435 91304055439859551083690653)
  ·
    refine ⟨34239020789947331656383995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91304055439859551083690653 34239020789947331656383995)
    ·
      refine ⟨51358531184920997484575993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34239020789947331656383995 51358531184920997484575993)
      ·
        refine ⟨38518898388690748113431995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51358531184920997484575993 38518898388690748113431995)
        ·
          refine ⟨57778347583036122170147993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38518898388690748113431995 57778347583036122170147993)
          ·
            refine ⟨43333760687277091627610995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57778347583036122170147993 43333760687277091627610995)
            ·
              refine ⟨65000641030915637441416493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43333760687277091627610995 65000641030915637441416493)
              ·
                refine ⟨24375240386593364040531185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65000641030915637441416493 24375240386593364040531185)
                ·
                  refine ⟨18281430289945023030398389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24375240386593364040531185 18281430289945023030398389)
                  ·
                    refine ⟨1713884089682345909099849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18281430289945023030398389 1713884089682345909099849)
                    ·
                      refine ⟨1285413067261759431824887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713884089682345909099849 1285413067261759431824887)
                      ·
                        rfl

theorem cell23_2503333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_2503333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503333 prefixEnd_2503333 := by exact prefixLift 2503333
  have htrace : WordTrace (prefixWord ++ tailWord_2503333) baseStart_2503333 baseEnd_2503333 := by
    simpa [prefixWord, tailWord_2503333, baseEnd_2503333] using wordTrace_append hprefix tailTrace_2503333
  have hstable : (prefixWord ++ tailWord_2503333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503333).length < 2 ^ (prefixWord ++ tailWord_2503333).sum := by decide
  have hdescent : baseEnd_2503333 < baseStart_2503333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503341 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_2503341 : Nat := 118140960795 + 2503341 * 2 ^ 59
def prefixEnd_2503341 : Nat := 4983230072969 + 3 ^ 40 * 2503341 * 2
def baseEnd_2503341 : Nat := 1285417175106995400524851

theorem tailTrace_2503341 : CollatzResearch.WordTrace tailWord_2503341 prefixEnd_2503341 1285417175106995400524851 := by
  unfold tailWord_2503341
  simp only [CollatzResearch.WordTrace]
  refine ⟨91304347223830568449981877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60869564815887045633321251 91304347223830568449981877)
  ·
    refine ⟨8559782552234115792185801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91304347223830568449981877 8559782552234115792185801)
    ·
      refine ⟨6419836914175586844139351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8559782552234115792185801 6419836914175586844139351)
      ·
        refine ⟨9629755371263380266209027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419836914175586844139351 9629755371263380266209027)
        ·
          refine ⟨14444633056895070399313541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9629755371263380266209027 14444633056895070399313541)
          ·
            refine ⟨2708368698167825699871289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14444633056895070399313541 2708368698167825699871289)
            ·
              refine ⟨2031276523625869274903467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708368698167825699871289 2031276523625869274903467)
              ·
                refine ⟨3046914785438803912355201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031276523625869274903467 3046914785438803912355201)
                ·
                  refine ⟨2285186089079102934266401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3046914785438803912355201 2285186089079102934266401)
                  ·
                    refine ⟨1713889566809327200699801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285186089079102934266401 1713889566809327200699801)
                    ·
                      refine ⟨1285417175106995400524851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1713889566809327200699801 1285417175106995400524851)
                      ·
                        rfl

theorem cell23_2503341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_2503341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503341 prefixEnd_2503341 := by exact prefixLift 2503341
  have htrace : WordTrace (prefixWord ++ tailWord_2503341) baseStart_2503341 baseEnd_2503341 := by
    simpa [prefixWord, tailWord_2503341, baseEnd_2503341] using wordTrace_append hprefix tailTrace_2503341
  have hstable : (prefixWord ++ tailWord_2503341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503341).length < 2 ^ (prefixWord ++ tailWord_2503341).sum := by decide
  have hdescent : baseEnd_2503341 < baseStart_2503341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503376 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_2503376 : Nat := 118140960795 + 2503376 * 2 ^ 59
def prefixEnd_2503376 : Nat := 4983230072969 + 3 ^ 40 * 2503376 * 2
def baseEnd_2503376 : Nat := 1285435146929902763587189

theorem tailTrace_2503376 : CollatzResearch.WordTrace tailWord_2503376 prefixEnd_2503376 1285435146929902763587189 := by
  unfold tailWord_2503376
  simp only [CollatzResearch.WordTrace]
  refine ⟨45652811889351884713752991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60870415852469179618337321 45652811889351884713752991)
  ·
    refine ⟨68479217834027827070629487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45652811889351884713752991 68479217834027827070629487)
    ·
      refine ⟨102718826751041740605944231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68479217834027827070629487 102718826751041740605944231)
      ·
        refine ⟨154078240126562610908916347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102718826751041740605944231 154078240126562610908916347)
        ·
          refine ⟨231117360189843916363374521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154078240126562610908916347 231117360189843916363374521)
          ·
            refine ⟨173338020142382937272530891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231117360189843916363374521 173338020142382937272530891)
            ·
              refine ⟨260007030213574405908796337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173338020142382937272530891 260007030213574405908796337)
              ·
                refine ⟨195005272660180804431597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260007030213574405908796337 195005272660180804431597253)
                ·
                  refine ⟨36563488623783900830924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195005272660180804431597253 36563488623783900830924485)
                  ·
                    refine ⟨6855654116959481405798341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36563488623783900830924485 6855654116959481405798341)
                    ·
                      refine ⟨1285435146929902763587189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6855654116959481405798341 1285435146929902763587189)
                      ·
                        rfl

theorem cell23_2503376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_2503376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503376 prefixEnd_2503376 := by exact prefixLift 2503376
  have htrace : WordTrace (prefixWord ++ tailWord_2503376) baseStart_2503376 baseEnd_2503376 := by
    simpa [prefixWord, tailWord_2503376, baseEnd_2503376] using wordTrace_append hprefix tailTrace_2503376
  have hstable : (prefixWord ++ tailWord_2503376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503376).length < 2 ^ (prefixWord ++ tailWord_2503376).sum := by decide
  have hdescent : baseEnd_2503376 < baseStart_2503376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503381 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 5]
def baseStart_2503381 : Nat := 118140960795 + 2503381 * 2 ^ 59
def prefixEnd_2503381 : Nat := 4983230072969 + 3 ^ 40 * 2503381 * 2
def baseEnd_2503381 : Nat := 142826412703686138224963

theorem tailTrace_2503381 : CollatzResearch.WordTrace tailWord_2503381 prefixEnd_2503381 142826412703686138224963 := by
  unfold tailWord_2503381
  simp only [CollatzResearch.WordTrace]
  refine ⟨91305806143685655281437997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60870537429123770187625331 91305806143685655281437997)
  ·
    refine ⟨34239677303882120730539249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91305806143685655281437997 34239677303882120730539249)
    ·
      refine ⟨25679757977911590547904437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34239677303882120730539249 25679757977911590547904437)
      ·
        refine ⟨2407477310429211613866041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25679757977911590547904437 2407477310429211613866041)
        ·
          refine ⟨1805607982821908710399531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407477310429211613866041 1805607982821908710399531)
          ·
            refine ⟨2708411974232863065599297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805607982821908710399531 2708411974232863065599297)
            ·
              refine ⟨2031308980674647299199473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708411974232863065599297 2031308980674647299199473)
              ·
                refine ⟨1523481735505985474399605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031308980674647299199473 1523481735505985474399605)
                ·
                  refine ⟨142826412703686138224963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523481735505985474399605 142826412703686138224963)
                  ·
                    rfl

theorem cell23_2503381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_2503381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503381 prefixEnd_2503381 := by exact prefixLift 2503381
  have htrace : WordTrace (prefixWord ++ tailWord_2503381) baseStart_2503381 baseEnd_2503381 := by
    simpa [prefixWord, tailWord_2503381, baseEnd_2503381] using wordTrace_append hprefix tailTrace_2503381
  have hstable : (prefixWord ++ tailWord_2503381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503381).length < 2 ^ (prefixWord ++ tailWord_2503381).sum := by decide
  have hdescent : baseEnd_2503381 < baseStart_2503381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503473 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2503473 : Nat := 118140960795 + 2503473 * 2 ^ 59
def prefixEnd_2503473 : Nat := 4983230072969 + 3 ^ 40 * 2503473 * 2
def baseEnd_2503473 : Nat := 1285484954553388884074243

theorem tailTrace_2503473 : CollatzResearch.WordTrace tailWord_2503473 prefixEnd_2503473 1285484954553388884074243 := by
  unfold tailWord_2503473
  simp only [CollatzResearch.WordTrace]
  refine ⟨91309161659352354993787073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60872774439568236662524715 91309161659352354993787073)
  ·
    refine ⟨68481871244514266245340305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91309161659352354993787073 68481871244514266245340305)
    ·
      refine ⟨51361403433385699684005229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68481871244514266245340305 51361403433385699684005229)
      ·
        refine ⟨19260526287519637381501961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51361403433385699684005229 19260526287519637381501961)
        ·
          refine ⟨14445394715639728036126471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19260526287519637381501961 14445394715639728036126471)
          ·
            refine ⟨21668092073459592054189707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14445394715639728036126471 21668092073459592054189707)
            ·
              refine ⟨32502138110189388081284561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21668092073459592054189707 32502138110189388081284561)
              ·
                refine ⟨24376603582642041060963421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32502138110189388081284561 24376603582642041060963421)
                ·
                  refine ⟨9141226343490765397861283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24376603582642041060963421 9141226343490765397861283)
                  ·
                    refine ⟨13711839515236148096791925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9141226343490765397861283 13711839515236148096791925)
                    ·
                      refine ⟨1285484954553388884074243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13711839515236148096791925 1285484954553388884074243)
                      ·
                        rfl

theorem cell23_2503473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2503473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503473 prefixEnd_2503473 := by exact prefixLift 2503473
  have htrace : WordTrace (prefixWord ++ tailWord_2503473) baseStart_2503473 baseEnd_2503473 := by
    simpa [prefixWord, tailWord_2503473, baseEnd_2503473] using wordTrace_append hprefix tailTrace_2503473
  have hstable : (prefixWord ++ tailWord_2503473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503473).length < 2 ^ (prefixWord ++ tailWord_2503473).sum := by decide
  have hdescent : baseEnd_2503473 < baseStart_2503473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503504 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 1, 2, 2]
def baseStart_2503504 : Nat := 118140960795 + 2503504 * 2 ^ 59
def prefixEnd_2503504 : Nat := 4983230072969 + 3 ^ 40 * 2503504 * 2
def baseEnd_2503504 : Nat := 1285500872453678262786601

theorem tailTrace_2503504 : CollatzResearch.WordTrace tailWord_2503504 prefixEnd_2503504 1285500872453678262786601 := by
  unfold tailWord_2503504
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655146161120023644082783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60873528214826698192110377 45655146161120023644082783)
  ·
    refine ⟨68482719241680035466124175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45655146161120023644082783 68482719241680035466124175)
    ·
      refine ⟨102724078862520053199186263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68482719241680035466124175 102724078862520053199186263)
      ·
        refine ⟨154086118293780079798779395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102724078862520053199186263 154086118293780079798779395)
        ·
          refine ⟨231129177440670119698169093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154086118293780079798779395 231129177440670119698169093)
          ·
            refine ⟨43336720770125647443406705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231129177440670119698169093 43336720770125647443406705)
            ·
              refine ⟨32502540577594235582555029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43336720770125647443406705 32502540577594235582555029)
              ·
                refine ⟨1523556589574729792932267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32502540577594235582555029 1523556589574729792932267)
                ·
                  refine ⟨2285334884362094689398401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523556589574729792932267 2285334884362094689398401)
                  ·
                    refine ⟨1714001163271571017048801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285334884362094689398401 1714001163271571017048801)
                    ·
                      refine ⟨1285500872453678262786601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714001163271571017048801 1285500872453678262786601)
                      ·
                        rfl

theorem cell23_2503504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 2, 2].length) (baseStart_2503504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503504 prefixEnd_2503504 := by exact prefixLift 2503504
  have htrace : WordTrace (prefixWord ++ tailWord_2503504) baseStart_2503504 baseEnd_2503504 := by
    simpa [prefixWord, tailWord_2503504, baseEnd_2503504] using wordTrace_append hprefix tailTrace_2503504
  have hstable : (prefixWord ++ tailWord_2503504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503504).length < 2 ^ (prefixWord ++ tailWord_2503504).sum := by decide
  have hdescent : baseEnd_2503504 < baseStart_2503504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503514 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_2503514 : Nat := 118140960795 + 2503514 * 2 ^ 59
def prefixEnd_2503514 : Nat := 4983230072969 + 3 ^ 40 * 2503514 * 2
def baseEnd_2503514 : Nat := 428502002420074407887185

theorem tailTrace_2503514 : CollatzResearch.WordTrace tailWord_2503514 prefixEnd_2503514 428502002420074407887185 := by
  unfold tailWord_2503514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22827664263050954749007399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60873771368135879330686397 22827664263050954749007399)
  ·
    refine ⟨34241496394576432123511099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22827664263050954749007399 34241496394576432123511099)
    ·
      refine ⟨51362244591864648185266649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34241496394576432123511099 51362244591864648185266649)
      ·
        refine ⟨38521683443898486138949987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51362244591864648185266649 38521683443898486138949987)
        ·
          refine ⟨57782525165847729208424981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38521683443898486138949987 57782525165847729208424981)
          ·
            refine ⟨2708555867149112306644921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57782525165847729208424981 2708555867149112306644921)
            ·
              refine ⟨2031416900361834229983691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708555867149112306644921 2031416900361834229983691)
              ·
                refine ⟨3047125350542751344975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031416900361834229983691 3047125350542751344975537)
                ·
                  refine ⟨2285344012907063508731653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047125350542751344975537 2285344012907063508731653)
                  ·
                    refine ⟨428502002420074407887185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285344012907063508731653 428502002420074407887185)
                    ·
                      rfl

theorem cell23_2503514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_2503514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503514 prefixEnd_2503514 := by exact prefixLift 2503514
  have htrace : WordTrace (prefixWord ++ tailWord_2503514) baseStart_2503514 baseEnd_2503514 := by
    simpa [prefixWord, tailWord_2503514, baseEnd_2503514] using wordTrace_append hprefix tailTrace_2503514
  have hstable : (prefixWord ++ tailWord_2503514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503514).length < 2 ^ (prefixWord ++ tailWord_2503514).sum := by decide
  have hdescent : baseEnd_2503514 < baseStart_2503514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503520 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_2503520 : Nat := 118140960795 + 2503520 * 2 ^ 59
def prefixEnd_2503520 : Nat := 4983230072969 + 3 ^ 40 * 2503520 * 2
def baseEnd_2503520 : Nat := 1285509088144150200186527

theorem tailTrace_2503520 : CollatzResearch.WordTrace tailWord_2503520 prefixEnd_2503520 1285509088144150200186527 := by
  unfold tailWord_2503520
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655437945091041010374007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60873917260121388013832009 45655437945091041010374007)
  ·
    refine ⟨68483156917636561515561011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45655437945091041010374007 68483156917636561515561011)
    ·
      refine ⟨102724735376454842273341517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68483156917636561515561011 102724735376454842273341517)
      ·
        refine ⟨38521775766170565852503069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102724735376454842273341517 38521775766170565852503069)
        ·
          refine ⟨14445665912313962194688651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38521775766170565852503069 14445665912313962194688651)
          ·
            refine ⟨21668498868470943292032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14445665912313962194688651 21668498868470943292032977)
            ·
              refine ⟨16251374151353207469024733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21668498868470943292032977 16251374151353207469024733)
              ·
                refine ⟨6094265306757452800884275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16251374151353207469024733 6094265306757452800884275)
                ·
                  refine ⟨9141397960136179201326413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094265306757452800884275 9141397960136179201326413)
                  ·
                    refine ⟨3428024235051067200497405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9141397960136179201326413 3428024235051067200497405)
                    ·
                      refine ⟨1285509088144150200186527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428024235051067200497405 1285509088144150200186527)
                      ·
                        rfl

theorem cell23_2503520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_2503520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503520 prefixEnd_2503520 := by exact prefixLift 2503520
  have htrace : WordTrace (prefixWord ++ tailWord_2503520) baseStart_2503520 baseEnd_2503520 := by
    simpa [prefixWord, tailWord_2503520, baseEnd_2503520] using wordTrace_append hprefix tailTrace_2503520
  have hstable : (prefixWord ++ tailWord_2503520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503520).length < 2 ^ (prefixWord ++ tailWord_2503520).sum := by decide
  have hdescent : baseEnd_2503520 < baseStart_2503520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503524 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_2503524 : Nat := 118140960795 + 2503524 * 2 ^ 59
def prefixEnd_2503524 : Nat := 4983230072969 + 3 ^ 40 * 2503524 * 2
def baseEnd_2503524 : Nat := 1285511142066768184536509

theorem tailTrace_2503524 : CollatzResearch.WordTrace tailWord_2503524 prefixEnd_2503524 1285511142066768184536509 := by
  unfold tailWord_2503524
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655510891083795351946813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60874014521445060469262417 45655510891083795351946813)
  ·
    refine ⟨17120816584156423256980055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45655510891083795351946813 17120816584156423256980055)
    ·
      refine ⟨25681224876234634885470083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17120816584156423256980055 25681224876234634885470083)
      ·
        refine ⟨38521837314351952328205125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25681224876234634885470083 38521837314351952328205125)
        ·
          refine ⟨7222844496440991061538461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38521837314351952328205125 7222844496440991061538461)
          ·
            refine ⟨2708566686165371648076923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7222844496440991061538461 2708566686165371648076923)
            ·
              refine ⟨4062850029248057472115385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708566686165371648076923 4062850029248057472115385)
              ·
                refine ⟨3047137521936043104086539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4062850029248057472115385 3047137521936043104086539)
                ·
                  refine ⟨4570706282904064656129809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047137521936043104086539 4570706282904064656129809)
                  ·
                    refine ⟨3428029712178048492097357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4570706282904064656129809 3428029712178048492097357)
                    ·
                      refine ⟨1285511142066768184536509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428029712178048492097357 1285511142066768184536509)
                      ·
                        rfl

theorem cell23_2503524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_2503524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503524 prefixEnd_2503524 := by exact prefixLift 2503524
  have htrace : WordTrace (prefixWord ++ tailWord_2503524) baseStart_2503524 baseEnd_2503524 := by
    simpa [prefixWord, tailWord_2503524, baseEnd_2503524] using wordTrace_append hprefix tailTrace_2503524
  have hstable : (prefixWord ++ tailWord_2503524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503524).length < 2 ^ (prefixWord ++ tailWord_2503524).sum := by decide
  have hdescent : baseEnd_2503524 < baseStart_2503524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503543 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2503543 : Nat := 118140960795 + 2503543 * 2 ^ 59
def prefixEnd_2503543 : Nat := 4983230072969 + 3 ^ 40 * 2503543 * 2
def baseEnd_2503543 : Nat := 1285520898199203610198921

theorem tailTrace_2503543 : CollatzResearch.WordTrace tailWord_2503543 prefixEnd_2503543 1285520898199203610198921 := by
  unfold tailWord_2503543
  simp only [CollatzResearch.WordTrace]
  refine ⟨91311714769098756948835283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60874476512732504632556855 91311714769098756948835283)
  ·
    refine ⟨136967572153648135423252925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91311714769098756948835283 136967572153648135423252925)
    ·
      refine ⟨51362839557618050783719847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136967572153648135423252925 51362839557618050783719847)
      ·
        refine ⟨77044259336427076175579771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51362839557618050783719847 77044259336427076175579771)
        ·
          refine ⟨115566389004640614263369657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77044259336427076175579771 115566389004640614263369657)
          ·
            refine ⟨86674791753480460697527243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115566389004640614263369657 86674791753480460697527243)
            ·
              refine ⟨130012187630220691046290865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86674791753480460697527243 130012187630220691046290865)
              ·
                refine ⟨97509140722665518284718149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130012187630220691046290865 97509140722665518284718149)
                ·
                  refine ⟨18282963885499784678384653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97509140722665518284718149 18282963885499784678384653)
                  ·
                    refine ⟨6856111457062419254394245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18282963885499784678384653 6856111457062419254394245)
                    ·
                      refine ⟨1285520898199203610198921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6856111457062419254394245 1285520898199203610198921)
                      ·
                        rfl

theorem cell23_2503543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2503543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503543 prefixEnd_2503543 := by exact prefixLift 2503543
  have htrace : WordTrace (prefixWord ++ tailWord_2503543) baseStart_2503543 baseEnd_2503543 := by
    simpa [prefixWord, tailWord_2503543, baseEnd_2503543] using wordTrace_append hprefix tailTrace_2503543
  have hstable : (prefixWord ++ tailWord_2503543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503543).length < 2 ^ (prefixWord ++ tailWord_2503543).sum := by decide
  have hdescent : baseEnd_2503543 < baseStart_2503543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503547 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 1, 3, 2]
def baseStart_2503547 : Nat := 118140960795 + 2503547 * 2 ^ 59
def prefixEnd_2503547 : Nat := 4983230072969 + 3 ^ 40 * 2503547 * 2
def baseEnd_2503547 : Nat := 1285522952121821594548903

theorem tailTrace_2503547 : CollatzResearch.WordTrace tailWord_2503547 prefixEnd_2503547 1285522952121821594548903 := by
  unfold tailWord_2503547
  simp only [CollatzResearch.WordTrace]
  refine ⟨91311860661084265631980895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60874573774056177087987263 91311860661084265631980895)
  ·
    refine ⟨136967790991626398447971343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91311860661084265631980895 136967790991626398447971343)
    ·
      refine ⟨205451686487439597671957015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136967790991626398447971343 205451686487439597671957015)
      ·
        refine ⟨308177529731159396507935523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205451686487439597671957015 308177529731159396507935523)
        ·
          refine ⟨462266294596739094761903285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308177529731159396507935523 462266294596739094761903285)
          ·
            refine ⟨43337465118444290133928433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462266294596739094761903285 43337465118444290133928433)
            ·
              refine ⟨32503098838833217600446325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43337465118444290133928433 32503098838833217600446325)
              ·
                refine ⟨3047165516140614150041843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32503098838833217600446325 3047165516140614150041843)
                ·
                  refine ⟨4570748274210921225062765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047165516140614150041843 4570748274210921225062765)
                  ·
                    refine ⟨1714030602829095459398537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4570748274210921225062765 1714030602829095459398537)
                    ·
                      refine ⟨1285522952121821594548903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714030602829095459398537 1285522952121821594548903)
                      ·
                        rfl

theorem cell23_2503547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3, 2].length) (baseStart_2503547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503547 prefixEnd_2503547 := by exact prefixLift 2503547
  have htrace : WordTrace (prefixWord ++ tailWord_2503547) baseStart_2503547 baseEnd_2503547 := by
    simpa [prefixWord, tailWord_2503547, baseEnd_2503547] using wordTrace_append hprefix tailTrace_2503547
  have hstable : (prefixWord ++ tailWord_2503547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503547).length < 2 ^ (prefixWord ++ tailWord_2503547).sum := by decide
  have hdescent : baseEnd_2503547 < baseStart_2503547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503560 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2503560 : Nat := 118140960795 + 2503560 * 2 ^ 59
def prefixEnd_2503560 : Nat := 4983230072969 + 3 ^ 40 * 2503560 * 2
def baseEnd_2503560 : Nat := 1285529627370330043686343

theorem tailTrace_2503560 : CollatzResearch.WordTrace tailWord_2503560 prefixEnd_2503560 1285529627370330043686343 := by
  unfold tailWord_2503560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45656167405018584426102067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60874889873358112568136089 45656167405018584426102067)
  ·
    refine ⟨68484251107527876639153101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45656167405018584426102067 68484251107527876639153101)
    ·
      refine ⟨25681594165322953739682413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68484251107527876639153101 25681594165322953739682413)
      ·
        refine ⟨9630597811996107652380905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25681594165322953739682413 9630597811996107652380905)
        ·
          refine ⟨7222948358997080739285679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9630597811996107652380905 7222948358997080739285679)
          ·
            refine ⟨10834422538495621108928519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222948358997080739285679 10834422538495621108928519)
            ·
              refine ⟨16251633807743431663392779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834422538495621108928519 16251633807743431663392779)
              ·
                refine ⟨24377450711615147495089169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16251633807743431663392779 24377450711615147495089169)
                ·
                  refine ⟨18283088033711360621316877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24377450711615147495089169 18283088033711360621316877)
                  ·
                    refine ⟨6856158012641760232993829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18283088033711360621316877 6856158012641760232993829)
                    ·
                      refine ⟨1285529627370330043686343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6856158012641760232993829 1285529627370330043686343)
                      ·
                        rfl

theorem cell23_2503560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2503560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503560 prefixEnd_2503560 := by exact prefixLift 2503560
  have htrace : WordTrace (prefixWord ++ tailWord_2503560) baseStart_2503560 baseEnd_2503560 := by
    simpa [prefixWord, tailWord_2503560, baseEnd_2503560] using wordTrace_append hprefix tailTrace_2503560
  have hstable : (prefixWord ++ tailWord_2503560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503560).length < 2 ^ (prefixWord ++ tailWord_2503560).sum := by decide
  have hdescent : baseEnd_2503560 < baseStart_2503560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503563 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_2503563 : Nat := 118140960795 + 2503563 * 2 ^ 59
def prefixEnd_2503563 : Nat := 4983230072969 + 3 ^ 40 * 2503563 * 2
def baseEnd_2503563 : Nat := 1285531167812293531948829

theorem tailTrace_2503563 : CollatzResearch.WordTrace tailWord_2503563 prefixEnd_2503563 1285531167812293531948829 := by
  unfold tailWord_2503563
  simp only [CollatzResearch.WordTrace]
  refine ⟨91312444229026300364563343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60874962819350866909708895 91312444229026300364563343)
  ·
    refine ⟨136968666343539450546845015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91312444229026300364563343 136968666343539450546845015)
    ·
      refine ⟨205452999515309175820267523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136968666343539450546845015 205452999515309175820267523)
      ·
        refine ⟨308179499272963763730401285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205452999515309175820267523 308179499272963763730401285)
        ·
          refine ⟨57783656113680705699450241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308179499272963763730401285 57783656113680705699450241)
          ·
            refine ⟨43337742085260529274587681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57783656113680705699450241 43337742085260529274587681)
            ·
              refine ⟨32503306563945396955940761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43337742085260529274587681 32503306563945396955940761)
              ·
                refine ⟨24377479922959047716955571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32503306563945396955940761 24377479922959047716955571)
                ·
                  refine ⟨36566219884438571575433357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24377479922959047716955571 36566219884438571575433357)
                  ·
                    refine ⟨13712332456664464340787509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36566219884438571575433357 13712332456664464340787509)
                    ·
                      refine ⟨1285531167812293531948829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13712332456664464340787509 1285531167812293531948829)
                      ·
                        rfl

theorem cell23_2503563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_2503563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503563 prefixEnd_2503563 := by exact prefixLift 2503563
  have htrace : WordTrace (prefixWord ++ tailWord_2503563) baseStart_2503563 baseEnd_2503563 := by
    simpa [prefixWord, tailWord_2503563, baseEnd_2503563] using wordTrace_append hprefix tailTrace_2503563
  have hstable : (prefixWord ++ tailWord_2503563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503563).length < 2 ^ (prefixWord ++ tailWord_2503563).sum := by decide
  have hdescent : baseEnd_2503563 < baseStart_2503563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503577 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 6, 2, 2]
def baseStart_2503577 : Nat := 118140960795 + 2503577 * 2 ^ 59
def prefixEnd_2503577 : Nat := 4983230072969 + 3 ^ 40 * 2503577 * 2
def baseEnd_2503577 : Nat := 1285538356541456477173765

theorem tailTrace_2503577 : CollatzResearch.WordTrace tailWord_2503577 prefixEnd_2503577 1285538356541456477173765 := by
  unfold tailWord_2503577
  simp only [CollatzResearch.WordTrace]
  refine ⟨91312954850975580755572985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60875303233983720503715323 91312954850975580755572985)
  ·
    refine ⟨68484716138231685566679739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91312954850975580755572985 68484716138231685566679739)
    ·
      refine ⟨102727074207347528350019609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68484716138231685566679739 102727074207347528350019609)
      ·
        refine ⟨77045305655510646262514707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102727074207347528350019609 77045305655510646262514707)
        ·
          refine ⟨115567958483265969393772061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77045305655510646262514707 115567958483265969393772061)
          ·
            refine ⟨43337984431224738522664523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115567958483265969393772061 43337984431224738522664523)
            ·
              refine ⟨65006976646837107783996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43337984431224738522664523 65006976646837107783996785)
              ·
                refine ⟨48755232485127830837997589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65006976646837107783996785 48755232485127830837997589)
                ·
                  refine ⟨2285401522740367070531137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48755232485127830837997589 2285401522740367070531137)
                  ·
                    refine ⟨1714051142055275302898353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285401522740367070531137 1714051142055275302898353)
                    ·
                      refine ⟨1285538356541456477173765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714051142055275302898353 1285538356541456477173765)
                      ·
                        rfl

theorem cell23_2503577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_2503577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503577 prefixEnd_2503577 := by exact prefixLift 2503577
  have htrace : WordTrace (prefixWord ++ tailWord_2503577) baseStart_2503577 baseEnd_2503577 := by
    simpa [prefixWord, tailWord_2503577, baseEnd_2503577] using wordTrace_append hprefix tailTrace_2503577
  have hstable : (prefixWord ++ tailWord_2503577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503577).length < 2 ^ (prefixWord ++ tailWord_2503577).sum := by decide
  have hdescent : baseEnd_2503577 < baseStart_2503577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503610 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2503610 : Nat := 118140960795 + 2503610 * 2 ^ 59
def prefixEnd_2503610 : Nat := 4983230072969 + 3 ^ 40 * 2503610 * 2
def baseEnd_2503610 : Nat := 1285555301403054848061113

theorem tailTrace_2503610 : CollatzResearch.WordTrace tailWord_2503610 prefixEnd_2503610 1285555301403054848061113 := by
  unfold tailWord_2503610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22828539614964006847881071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60876105639904018261016189 22828539614964006847881071)
  ·
    refine ⟨34242809422446010271821607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22828539614964006847881071 34242809422446010271821607)
    ·
      refine ⟨51364214133669015407732411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34242809422446010271821607 51364214133669015407732411)
      ·
        refine ⟨77046321200503523111598617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51364214133669015407732411 77046321200503523111598617)
        ·
          refine ⟨57784740900377642333698963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77046321200503523111598617 57784740900377642333698963)
          ·
            refine ⟨86677111350566463500548445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57784740900377642333698963 86677111350566463500548445)
            ·
              refine ⟨32503916756462423812705667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86677111350566463500548445 32503916756462423812705667)
              ·
                refine ⟨48755875134693635719058501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32503916756462423812705667 48755875134693635719058501)
                ·
                  refine ⟨9141726587755056697323469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48755875134693635719058501 9141726587755056697323469)
                  ·
                    refine ⟨3428147470408146261496301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9141726587755056697323469 3428147470408146261496301)
                    ·
                      refine ⟨1285555301403054848061113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428147470408146261496301 1285555301403054848061113)
                      ·
                        rfl

theorem cell23_2503610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2503610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503610 prefixEnd_2503610 := by exact prefixLift 2503610
  have htrace : WordTrace (prefixWord ++ tailWord_2503610) baseStart_2503610 baseEnd_2503610 := by
    simpa [prefixWord, tailWord_2503610, baseEnd_2503610] using wordTrace_append hprefix tailTrace_2503610
  have hstable : (prefixWord ++ tailWord_2503610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503610).length < 2 ^ (prefixWord ++ tailWord_2503610).sum := by decide
  have hdescent : baseEnd_2503610 < baseStart_2503610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503622 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2503622 : Nat := 118140960795 + 2503622 * 2 ^ 59
def prefixEnd_2503622 : Nat := 4983230072969 + 3 ^ 40 * 2503622 * 2
def baseEnd_2503622 : Nat := 1285561463170908801111059

theorem tailTrace_2503622 : CollatzResearch.WordTrace tailWord_2503622 prefixEnd_2503622 1285561463170908801111059 := by
  unfold tailWord_2503622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853581129244142295030035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60876397423875035627307413 2853581129244142295030035)
  ·
    refine ⟨4280371693866213442545053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853581129244142295030035 4280371693866213442545053)
    ·
      refine ⟨1605139385199830040954395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4280371693866213442545053 1605139385199830040954395)
      ·
        refine ⟨2407709077799745061431593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605139385199830040954395 2407709077799745061431593)
        ·
          refine ⟨1805781808349808796073695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407709077799745061431593 1805781808349808796073695)
          ·
            refine ⟨2708672712524713194110543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805781808349808796073695 2708672712524713194110543)
            ·
              refine ⟨4063009068787069791165815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708672712524713194110543 4063009068787069791165815)
              ·
                refine ⟨6094513603180604686748723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063009068787069791165815 6094513603180604686748723)
                ·
                  refine ⟨9141770404770907030123085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094513603180604686748723 9141770404770907030123085)
                  ·
                    refine ⟨3428163901789090136296157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9141770404770907030123085 3428163901789090136296157)
                    ·
                      refine ⟨1285561463170908801111059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428163901789090136296157 1285561463170908801111059)
                      ·
                        rfl

theorem cell23_2503622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2503622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503622 prefixEnd_2503622 := by exact prefixLift 2503622
  have htrace : WordTrace (prefixWord ++ tailWord_2503622) baseStart_2503622 baseEnd_2503622 := by
    simpa [prefixWord, tailWord_2503622, baseEnd_2503622] using wordTrace_append hprefix tailTrace_2503622
  have hstable : (prefixWord ++ tailWord_2503622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503622).length < 2 ^ (prefixWord ++ tailWord_2503622).sum := by decide
  have hdescent : baseEnd_2503622 < baseStart_2503622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503630 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2503630 : Nat := 118140960795 + 2503630 * 2 ^ 59
def prefixEnd_2503630 : Nat := 4983230072969 + 3 ^ 40 * 2503630 * 2
def baseEnd_2503630 : Nat := 428521857005381589937007

theorem tailTrace_2503630 : CollatzResearch.WordTrace tailWord_2503630 prefixEnd_2503630 428521857005381589937007 := by
  unfold tailWord_2503630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414360989972946350906543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60876591946522380538168229 11414360989972946350906543)
  ·
    refine ⟨17121541484959419526359815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11414360989972946350906543 17121541484959419526359815)
    ·
      refine ⟨25682312227439129289539723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17121541484959419526359815 25682312227439129289539723)
      ·
        refine ⟨38523468341158693934309585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25682312227439129289539723 38523468341158693934309585)
        ·
          refine ⟨28892601255869020450732189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38523468341158693934309585 28892601255869020450732189)
          ·
            refine ⟨10834725470950882669024571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28892601255869020450732189 10834725470950882669024571)
            ·
              refine ⟨16252088206426324003536857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834725470950882669024571 16252088206426324003536857)
              ·
                refine ⟨12189066154819743002652643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16252088206426324003536857 12189066154819743002652643)
                ·
                  refine ⟨18283599232229614503978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12189066154819743002652643 18283599232229614503978965)
                  ·
                    refine ⟨428521857005381589937007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18283599232229614503978965 428521857005381589937007)
                    ·
                      rfl

theorem cell23_2503630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2503630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503630 prefixEnd_2503630 := by exact prefixLift 2503630
  have htrace : WordTrace (prefixWord ++ tailWord_2503630) baseStart_2503630 baseEnd_2503630 := by
    simpa [prefixWord, tailWord_2503630, baseEnd_2503630] using wordTrace_append hprefix tailTrace_2503630
  have hstable : (prefixWord ++ tailWord_2503630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503630).length < 2 ^ (prefixWord ++ tailWord_2503630).sum := by decide
  have hdescent : baseEnd_2503630 < baseStart_2503630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503687 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2503687 : Nat := 118140960795 + 2503687 * 2 ^ 59
def prefixEnd_2503687 : Nat := 4983230072969 + 3 ^ 40 * 2503687 * 2
def baseEnd_2503687 : Nat := 1285594839413451046798259

theorem tailTrace_2503687 : CollatzResearch.WordTrace tailWord_2503687 prefixEnd_2503687 1285594839413451046798259 := by
  unfold tailWord_2503687
  simp only [CollatzResearch.WordTrace]
  refine ⟨91316966880577069542077315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60877977920384713028051543 91316966880577069542077315)
  ·
    refine ⟨136975450320865604313115973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91316966880577069542077315 136975450320865604313115973)
    ·
      refine ⟨25682896935162300808709245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136975450320865604313115973 25682896935162300808709245)
      ·
        refine ⟨9631086350685862803265967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25682896935162300808709245 9631086350685862803265967)
        ·
          refine ⟨14446629526028794204898951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631086350685862803265967 14446629526028794204898951)
          ·
            refine ⟨21669944289043191307348427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14446629526028794204898951 21669944289043191307348427)
            ·
              refine ⟨32504916433564786961022641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21669944289043191307348427 32504916433564786961022641)
              ·
                refine ⟨24378687325173590220766981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32504916433564786961022641 24378687325173590220766981)
                ·
                  refine ⟨4571003873470048166393809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24378687325173590220766981 4571003873470048166393809)
                  ·
                    refine ⟨3428252905102536124795357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571003873470048166393809 3428252905102536124795357)
                    ·
                      refine ⟨1285594839413451046798259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428252905102536124795357 1285594839413451046798259)
                      ·
                        rfl

theorem cell23_2503687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2503687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503687 prefixEnd_2503687 := by exact prefixLift 2503687
  have htrace : WordTrace (prefixWord ++ tailWord_2503687) baseStart_2503687 baseEnd_2503687 := by
    simpa [prefixWord, tailWord_2503687, baseEnd_2503687] using wordTrace_append hprefix tailTrace_2503687
  have hstable : (prefixWord ++ tailWord_2503687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503687).length < 2 ^ (prefixWord ++ tailWord_2503687).sum := by decide
  have hdescent : baseEnd_2503687 < baseStart_2503687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503698 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2503698 : Nat := 118140960795 + 2503698 * 2 ^ 59
def prefixEnd_2503698 : Nat := 4983230072969 + 3 ^ 40 * 2503698 * 2
def baseEnd_2503698 : Nat := 428533495900216834586903

theorem tailTrace_2503698 : CollatzResearch.WordTrace tailWord_2503698 prefixEnd_2503698 428533495900216834586903 := by
  unfold tailWord_2503698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22829342020884304605181937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60878245389024812280485165 22829342020884304605181937)
  ·
    refine ⟨17122006515663228453886453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22829342020884304605181937 17122006515663228453886453)
    ·
      refine ⟨1605188110843427667551855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17122006515663228453886453 1605188110843427667551855)
      ·
        refine ⟨2407782166265141501327783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605188110843427667551855 2407782166265141501327783)
        ·
          refine ⟨3611673249397712251991675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407782166265141501327783 3611673249397712251991675)
          ·
            refine ⟨5417509874096568377987513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611673249397712251991675 5417509874096568377987513)
            ·
              refine ⟨4063132405572426283490635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5417509874096568377987513 4063132405572426283490635)
              ·
                refine ⟨6094698608358639425235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063132405572426283490635 6094698608358639425235953)
                ·
                  refine ⟨4571023956268979568926965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6094698608358639425235953 4571023956268979568926965)
                  ·
                    refine ⟨428533495900216834586903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4571023956268979568926965 428533495900216834586903)
                    ·
                      rfl

theorem cell23_2503698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2503698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503698 prefixEnd_2503698 := by exact prefixLift 2503698
  have htrace : WordTrace (prefixWord ++ tailWord_2503698) baseStart_2503698 baseEnd_2503698 := by
    simpa [prefixWord, tailWord_2503698, baseEnd_2503698] using wordTrace_append hprefix tailTrace_2503698
  have hstable : (prefixWord ++ tailWord_2503698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503698).length < 2 ^ (prefixWord ++ tailWord_2503698).sum := by decide
  have hdescent : baseEnd_2503698 < baseStart_2503698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503704 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2503704 : Nat := 118140960795 + 2503704 * 2 ^ 59
def prefixEnd_2503704 : Nat := 4983230072969 + 3 ^ 40 * 2503704 * 2
def baseEnd_2503704 : Nat := 1285603568584577480285681

theorem tailTrace_2503704 : CollatzResearch.WordTrace tailWord_2503704 prefixEnd_2503704 1285603568584577480285681 := by
  unfold tailWord_2503704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658793460757740722723083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60878391281010320963630777 45658793460757740722723083)
  ·
    refine ⟨68488190191136611084084625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45658793460757740722723083 68488190191136611084084625)
    ·
      refine ⟨51366142643352458313063469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68488190191136611084084625 51366142643352458313063469)
      ·
        refine ⟨19262303491257171867398801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51366142643352458313063469 19262303491257171867398801)
        ·
          refine ⟨14446727618442878900549101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19262303491257171867398801 14446727618442878900549101)
          ·
            refine ⟨5417522856916079587705913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14446727618442878900549101 5417522856916079587705913)
            ·
              refine ⟨4063142142687059690779435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5417522856916079587705913 4063142142687059690779435)
              ·
                refine ⟨6094713214030589536169153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063142142687059690779435 6094713214030589536169153)
                ·
                  refine ⟨4571034910522942152126865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6094713214030589536169153 4571034910522942152126865)
                  ·
                    refine ⟨3428276182892206614095149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571034910522942152126865 3428276182892206614095149)
                    ·
                      refine ⟨1285603568584577480285681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428276182892206614095149 1285603568584577480285681)
                      ·
                        rfl

theorem cell23_2503704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2503704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503704 prefixEnd_2503704 := by exact prefixLift 2503704
  have htrace : WordTrace (prefixWord ++ tailWord_2503704) baseStart_2503704 baseEnd_2503704 := by
    simpa [prefixWord, tailWord_2503704, baseEnd_2503704] using wordTrace_append hprefix tailTrace_2503704
  have hstable : (prefixWord ++ tailWord_2503704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503704).length < 2 ^ (prefixWord ++ tailWord_2503704).sum := by decide
  have hdescent : baseEnd_2503704 < baseStart_2503704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503737 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_2503737 : Nat := 118140960795 + 2503737 * 2 ^ 59
def prefixEnd_2503737 : Nat := 4983230072969 + 3 ^ 40 * 2503737 * 2
def baseEnd_2503737 : Nat := 428540171148725283724343

theorem tailTrace_2503737 : CollatzResearch.WordTrace tailWord_2503737 prefixEnd_2503737 428540171148725283724343 := by
  unfold tailWord_2503737
  simp only [CollatzResearch.WordTrace]
  refine ⟨91318790530395928081397465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60879193686930618720931643 91318790530395928081397465)
  ·
    refine ⟨68489092897796946061048099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91318790530395928081397465 68489092897796946061048099)
    ·
      refine ⟨102733639346695419091572149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68489092897796946061048099 102733639346695419091572149)
      ·
        refine ⟨9631278688752695539834889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102733639346695419091572149 9631278688752695539834889)
        ·
          refine ⟨7223459016564521654876167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9631278688752695539834889 7223459016564521654876167)
          ·
            refine ⟨10835188524846782482314251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223459016564521654876167 10835188524846782482314251)
            ·
              refine ⟨16252782787270173723471377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10835188524846782482314251 16252782787270173723471377)
              ·
                refine ⟨12189587090452630292603533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16252782787270173723471377 12189587090452630292603533)
                ·
                  refine ⟨4571095158919736359726325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12189587090452630292603533 4571095158919736359726325)
                  ·
                    refine ⟨428540171148725283724343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4571095158919736359726325 428540171148725283724343)
                    ·
                      rfl

theorem cell23_2503737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_2503737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503737 prefixEnd_2503737 := by exact prefixLift 2503737
  have htrace : WordTrace (prefixWord ++ tailWord_2503737) baseStart_2503737 baseEnd_2503737 := by
    simpa [prefixWord, tailWord_2503737, baseEnd_2503737] using wordTrace_append hprefix tailTrace_2503737
  have hstable : (prefixWord ++ tailWord_2503737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503737).length < 2 ^ (prefixWord ++ tailWord_2503737).sum := by decide
  have hdescent : baseEnd_2503737 < baseStart_2503737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503767 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 4, 4]
def baseStart_2503767 : Nat := 118140960795 + 2503767 * 2 ^ 59
def prefixEnd_2503767 : Nat := 4983230072969 + 3 ^ 40 * 2503767 * 2
def baseEnd_2503767 : Nat := 428545305955270244599297

theorem tailTrace_2503767 : CollatzResearch.WordTrace tailWord_2503767 prefixEnd_2503767 428545305955270244599297 := by
  unfold tailWord_2503767
  simp only [CollatzResearch.WordTrace]
  refine ⟨91319884720287243204989555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60879923146858162136659703 91319884720287243204989555)
  ·
    refine ⟨136979827080430864807484333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91319884720287243204989555 136979827080430864807484333)
    ·
      refine ⟨51367435155161574302806625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136979827080430864807484333 51367435155161574302806625)
      ·
        refine ⟨38525576366371180727104969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51367435155161574302806625 38525576366371180727104969)
        ·
          refine ⟨28894182274778385545328727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38525576366371180727104969 28894182274778385545328727)
          ·
            refine ⟨43341273412167578317993091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28894182274778385545328727 43341273412167578317993091)
            ·
              refine ⟨65011910118251367476989637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43341273412167578317993091 65011910118251367476989637)
              ·
                refine ⟨12189733147172131401935557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65011910118251367476989637 12189733147172131401935557)
                ·
                  refine ⟨2285574965094774637862917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12189733147172131401935557 2285574965094774637862917)
                  ·
                    refine ⟨428545305955270244599297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285574965094774637862917 428545305955270244599297)
                    ·
                      rfl

theorem cell23_2503767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_2503767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503767 prefixEnd_2503767 := by exact prefixLift 2503767
  have htrace : WordTrace (prefixWord ++ tailWord_2503767) baseStart_2503767 baseEnd_2503767 := by
    simpa [prefixWord, tailWord_2503767, baseEnd_2503767] using wordTrace_append hprefix tailTrace_2503767
  have hstable : (prefixWord ++ tailWord_2503767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503767).length < 2 ^ (prefixWord ++ tailWord_2503767).sum := by decide
  have hdescent : baseEnd_2503767 < baseStart_2503767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503791 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 3, 2, 2]
def baseStart_2503791 : Nat := 118140960795 + 2503791 * 2 ^ 59
def prefixEnd_2503791 : Nat := 4983230072969 + 3 ^ 40 * 2503791 * 2
def baseEnd_2503791 : Nat := 1285648241401518639897781

theorem tailTrace_2503791 : CollatzResearch.WordTrace tailWord_2503791 prefixEnd_2503791 1285648241401518639897781 := by
  unfold tailWord_2503791
  simp only [CollatzResearch.WordTrace]
  refine ⟨91320760072200295303863227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60880506714800196869242151 91320760072200295303863227)
  ·
    refine ⟨136981140108300442955794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91320760072200295303863227 136981140108300442955794841)
    ·
      refine ⟨102735855081225332216846131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136981140108300442955794841 102735855081225332216846131)
      ·
        refine ⟨154103782621837998325269197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102735855081225332216846131 154103782621837998325269197)
        ·
          refine ⟨57788918483189249371975949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154103782621837998325269197 57788918483189249371975949)
          ·
            refine ⟨21670844431195968514490981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57788918483189249371975949 21670844431195968514490981)
            ·
              refine ⟨4063283330849244096467059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21670844431195968514490981 4063283330849244096467059)
              ·
                refine ⟨6094924996273866144700589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063283330849244096467059 6094924996273866144700589)
                ·
                  refine ⟨2285596873602699804262721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6094924996273866144700589 2285596873602699804262721)
                  ·
                    refine ⟨1714197655202024853197041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285596873602699804262721 1714197655202024853197041)
                    ·
                      refine ⟨1285648241401518639897781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714197655202024853197041 1285648241401518639897781)
                      ·
                        rfl

theorem cell23_2503791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2, 2].length) (baseStart_2503791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503791 prefixEnd_2503791 := by exact prefixLift 2503791
  have htrace : WordTrace (prefixWord ++ tailWord_2503791) baseStart_2503791 baseEnd_2503791 := by
    simpa [prefixWord, tailWord_2503791, baseEnd_2503791] using wordTrace_append hprefix tailTrace_2503791
  have hstable : (prefixWord ++ tailWord_2503791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503791).length < 2 ^ (prefixWord ++ tailWord_2503791).sum := by decide
  have hdescent : baseEnd_2503791 < baseStart_2503791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503801 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_2503801 : Nat := 118140960795 + 2503801 * 2 ^ 59
def prefixEnd_2503801 : Nat := 4983230072969 + 3 ^ 40 * 2503801 * 2
def baseEnd_2503801 : Nat := 428551125402687866924245

theorem tailTrace_2503801 : CollatzResearch.WordTrace tailWord_2503801 prefixEnd_2503801 428551125402687866924245 := by
  unfold tailWord_2503801
  simp only [CollatzResearch.WordTrace]
  refine ⟨91321124802164067011727257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60880749868109378007818171 91321124802164067011727257)
  ·
    refine ⟨68490843601623050258795443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91321124802164067011727257 68490843601623050258795443)
    ·
      refine ⟨102736265402434575388193165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68490843601623050258795443 102736265402434575388193165)
      ·
        refine ⟨38526099525912965770572437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102736265402434575388193165 38526099525912965770572437)
        ·
          refine ⟨1805910915277170270495583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38526099525912965770572437 1805910915277170270495583)
          ·
            refine ⟨2708866372915755405743375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805910915277170270495583 2708866372915755405743375)
            ·
              refine ⟨4063299559373633108615063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708866372915755405743375 4063299559373633108615063)
              ·
                refine ⟨6094949339060449662922595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063299559373633108615063 6094949339060449662922595)
                ·
                  refine ⟨9142424008590674494383893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094949339060449662922595 9142424008590674494383893)
                  ·
                    refine ⟨428551125402687866924245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9142424008590674494383893 428551125402687866924245)
                    ·
                      rfl

theorem cell23_2503801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_2503801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503801 prefixEnd_2503801 := by exact prefixLift 2503801
  have htrace : WordTrace (prefixWord ++ tailWord_2503801) baseStart_2503801 baseEnd_2503801 := by
    simpa [prefixWord, tailWord_2503801, baseEnd_2503801] using wordTrace_append hprefix tailTrace_2503801
  have hstable : (prefixWord ++ tailWord_2503801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503801).length < 2 ^ (prefixWord ++ tailWord_2503801).sum := by decide
  have hdescent : baseEnd_2503801 < baseStart_2503801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503837 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2503837 : Nat := 118140960795 + 2503837 * 2 ^ 59
def prefixEnd_2503837 : Nat := 4983230072969 + 3 ^ 40 * 2503837 * 2
def baseEnd_2503837 : Nat := 1285671861511625459922569

theorem tailTrace_2503837 : CollatzResearch.WordTrace tailWord_2503837 prefixEnd_2503837 1285671861511625459922569 := by
  unfold tailWord_2503837
  simp only [CollatzResearch.WordTrace]
  refine ⟨91322437830033645160037765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60881625220022430106691843 91322437830033645160037765)
  ·
    refine ⟨17122957093131308467507081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91322437830033645160037765 17122957093131308467507081)
    ·
      refine ⟨12842217819848481350630311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17122957093131308467507081 12842217819848481350630311)
      ·
        refine ⟨19263326729772722025945467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842217819848481350630311 19263326729772722025945467)
        ·
          refine ⟨28894990094659083038918201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19263326729772722025945467 28894990094659083038918201)
          ·
            refine ⟨21671242570994312279188651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28894990094659083038918201 21671242570994312279188651)
            ·
              refine ⟨32506863856491468418782977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21671242570994312279188651 32506863856491468418782977)
              ·
                refine ⟨24380147892368601314087233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32506863856491468418782977 24380147892368601314087233)
                ·
                  refine ⟨18285110919276450985565425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24380147892368601314087233 18285110919276450985565425)
                  ·
                    refine ⟨13713833189457338239174069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18285110919276450985565425 13713833189457338239174069)
                    ·
                      refine ⟨1285671861511625459922569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13713833189457338239174069 1285671861511625459922569)
                      ·
                        rfl

theorem cell23_2503837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2503837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503837 prefixEnd_2503837 := by exact prefixLift 2503837
  have htrace : WordTrace (prefixWord ++ tailWord_2503837) baseStart_2503837 baseEnd_2503837 := by
    simpa [prefixWord, tailWord_2503837, baseEnd_2503837] using wordTrace_append hprefix tailTrace_2503837
  have hstable : (prefixWord ++ tailWord_2503837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503837).length < 2 ^ (prefixWord ++ tailWord_2503837).sum := by decide
  have hdescent : baseEnd_2503837 < baseStart_2503837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503841 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2503841 : Nat := 118140960795 + 2503841 * 2 ^ 59
def prefixEnd_2503841 : Nat := 4983230072969 + 3 ^ 40 * 2503841 * 2
def baseEnd_2503841 : Nat := 1285673915434243444272551

theorem tailTrace_2503841 : CollatzResearch.WordTrace tailWord_2503841 prefixEnd_2503841 1285673915434243444272551 := by
  unfold tailWord_2503841
  simp only [CollatzResearch.WordTrace]
  refine ⟨91322583722019153843183377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60881722481346102562122251 91322583722019153843183377)
  ·
    refine ⟨68491937791514365382387533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91322583722019153843183377 68491937791514365382387533)
    ·
      refine ⟨25684476671817887018395325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68491937791514365382387533 25684476671817887018395325)
      ·
        refine ⟨9631678751931707631898247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25684476671817887018395325 9631678751931707631898247)
        ·
          refine ⟨14447518127897561447847371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631678751931707631898247 14447518127897561447847371)
          ·
            refine ⟨21671277191846342171771057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447518127897561447847371 21671277191846342171771057)
            ·
              refine ⟨16253457893884756628828293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21671277191846342171771057 16253457893884756628828293)
              ·
                refine ⟨3047523355103391867905305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16253457893884756628828293 3047523355103391867905305)
                ·
                  refine ⟨2285642516327543900928979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047523355103391867905305 2285642516327543900928979)
                  ·
                    refine ⟨3428463774491315851393469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285642516327543900928979 3428463774491315851393469)
                    ·
                      refine ⟨1285673915434243444272551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428463774491315851393469 1285673915434243444272551)
                      ·
                        rfl

theorem cell23_2503841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2503841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503841 prefixEnd_2503841 := by exact prefixLift 2503841
  have htrace : WordTrace (prefixWord ++ tailWord_2503841) baseStart_2503841 baseEnd_2503841 := by
    simpa [prefixWord, tailWord_2503841, baseEnd_2503841] using wordTrace_append hprefix tailTrace_2503841
  have hstable : (prefixWord ++ tailWord_2503841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503841).length < 2 ^ (prefixWord ++ tailWord_2503841).sum := by decide
  have hdescent : baseEnd_2503841 < baseStart_2503841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503842 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2503842 : Nat := 118140960795 + 2503842 * 2 ^ 59
def prefixEnd_2503842 : Nat := 4983230072969 + 3 ^ 40 * 2503842 * 2
def baseEnd_2503842 : Nat := 1285674428914897940360047

theorem tailTrace_2503842 : CollatzResearch.WordTrace tailWord_2503842 prefixEnd_2503842 1285674428914897940360047 := by
  unfold tailWord_2503842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830655048753882753492445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60881746796677020675979853 22830655048753882753492445)
  ·
    refine ⟨8561495643282706032559667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22830655048753882753492445 8561495643282706032559667)
    ·
      refine ⟨12842243464924059048839501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561495643282706032559667 12842243464924059048839501)
      ·
        refine ⟨4815841299346522143314813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12842243464924059048839501 4815841299346522143314813)
        ·
          refine ⟨1805940487254945803743055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4815841299346522143314813 1805940487254945803743055)
          ·
            refine ⟨2708910730882418705614583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805940487254945803743055 2708910730882418705614583)
            ·
              refine ⟨4063366096323628058421875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708910730882418705614583 4063366096323628058421875)
              ·
                refine ⟨6095049144485442087632813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063366096323628058421875 6095049144485442087632813)
                ·
                  refine ⟨2285643429182040782862305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095049144485442087632813 2285643429182040782862305)
                  ·
                    refine ⟨1714232571886530587146729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285643429182040782862305 1714232571886530587146729)
                    ·
                      refine ⟨1285674428914897940360047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714232571886530587146729 1285674428914897940360047)
                      ·
                        rfl

theorem cell23_2503842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2503842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503842 prefixEnd_2503842 := by exact prefixLift 2503842
  have htrace : WordTrace (prefixWord ++ tailWord_2503842) baseStart_2503842 baseEnd_2503842 := by
    simpa [prefixWord, tailWord_2503842, baseEnd_2503842] using wordTrace_append hprefix tailTrace_2503842
  have hstable : (prefixWord ++ tailWord_2503842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503842).length < 2 ^ (prefixWord ++ tailWord_2503842).sum := by decide
  have hdescent : baseEnd_2503842 < baseStart_2503842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503858 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_2503858 : Nat := 118140960795 + 2503858 * 2 ^ 59
def prefixEnd_2503858 : Nat := 4983230072969 + 3 ^ 40 * 2503858 * 2
def baseEnd_2503858 : Nat := 1285682644605369877759973

theorem tailTrace_2503858 : CollatzResearch.WordTrace tailWord_2503858 prefixEnd_2503858 1285682644605369877759973 := by
  unfold tailWord_2503858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830800940739391436638057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60882135841971710497701485 22830800940739391436638057)
  ·
    refine ⟨17123100705554543577478543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22830800940739391436638057 17123100705554543577478543)
    ·
      refine ⟨25684651058331815366217815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17123100705554543577478543 25684651058331815366217815)
      ·
        refine ⟨38526976587497723049326723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25684651058331815366217815 38526976587497723049326723)
        ·
          refine ⟨57790464881246584573990085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38526976587497723049326723 57790464881246584573990085)
          ·
            refine ⟨10835712165233734607623141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57790464881246584573990085 10835712165233734607623141)
            ·
              refine ⟨2031696030981325238929339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10835712165233734607623141 2031696030981325238929339)
              ·
                refine ⟨3047544046471987858394009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031696030981325238929339 3047544046471987858394009)
                ·
                  refine ⟨2285658034853990893795507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047544046471987858394009 2285658034853990893795507)
                  ·
                    refine ⟨3428487052280986340693261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285658034853990893795507 3428487052280986340693261)
                    ·
                      refine ⟨1285682644605369877759973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428487052280986340693261 1285682644605369877759973)
                      ·
                        rfl

theorem cell23_2503858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_2503858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503858 prefixEnd_2503858 := by exact prefixLift 2503858
  have htrace : WordTrace (prefixWord ++ tailWord_2503858) baseStart_2503858 baseEnd_2503858 := by
    simpa [prefixWord, tailWord_2503858, baseEnd_2503858] using wordTrace_append hprefix tailTrace_2503858
  have hstable : (prefixWord ++ tailWord_2503858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503858).length < 2 ^ (prefixWord ++ tailWord_2503858).sum := by decide
  have hdescent : baseEnd_2503858 < baseStart_2503858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503862 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2503862 : Nat := 118140960795 + 2503862 * 2 ^ 59
def prefixEnd_2503862 : Nat := 4983230072969 + 3 ^ 40 * 2503862 * 2
def baseEnd_2503862 : Nat := 1285684698527987862109955

theorem tailTrace_2503862 : CollatzResearch.WordTrace tailWord_2503862 prefixEnd_2503862 1285684698527987862109955 := by
  unfold tailWord_2503862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707709353433942151856115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60882233103295382953131893 5707709353433942151856115)
  ·
    refine ⟨8561564030150913227784173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5707709353433942151856115 8561564030150913227784173)
    ·
      refine ⟨3210586511306592460419065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8561564030150913227784173 3210586511306592460419065)
      ·
        refine ⟨2407939883479944345314299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210586511306592460419065 2407939883479944345314299)
        ·
          refine ⟨3611909825219916517971449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407939883479944345314299 3611909825219916517971449)
          ·
            refine ⟨2708932368914937388478587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3611909825219916517971449 2708932368914937388478587)
            ·
              refine ⟨4063398553372406082717881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708932368914937388478587 4063398553372406082717881)
              ·
                refine ⟨3047548915029304562038411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063398553372406082717881 3047548915029304562038411)
                ·
                  refine ⟨4571323372543956843057617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047548915029304562038411 4571323372543956843057617)
                  ·
                    refine ⟨3428492529407967632293213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571323372543956843057617 3428492529407967632293213)
                    ·
                      refine ⟨1285684698527987862109955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428492529407967632293213 1285684698527987862109955)
                      ·
                        rfl

theorem cell23_2503862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2503862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503862 prefixEnd_2503862 := by exact prefixLift 2503862
  have htrace : WordTrace (prefixWord ++ tailWord_2503862) baseStart_2503862 baseEnd_2503862 := by
    simpa [prefixWord, tailWord_2503862, baseEnd_2503862] using wordTrace_append hprefix tailTrace_2503862
  have hstable : (prefixWord ++ tailWord_2503862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503862).length < 2 ^ (prefixWord ++ tailWord_2503862).sum := by decide
  have hdescent : baseEnd_2503862 < baseStart_2503862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3]
def baseStart_2503867 : Nat := 118140960795 + 2503867 * 2 ^ 59
def prefixEnd_2503867 : Nat := 4983230072969 + 3 ^ 40 * 2503867 * 2
def baseEnd_2503867 : Nat := 1285687265931260342547431

theorem tailTrace_2503867 : CollatzResearch.WordTrace tailWord_2503867 prefixEnd_2503867 1285687265931260342547431 := by
  unfold tailWord_2503867
  simp only [CollatzResearch.WordTrace]
  refine ⟨91323532019924960283629855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60882354679949973522419903 91323532019924960283629855)
  ·
    refine ⟨136985298029887440425444783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91323532019924960283629855 136985298029887440425444783)
    ·
      refine ⟨205477947044831160638167175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136985298029887440425444783 205477947044831160638167175)
      ·
        refine ⟨308216920567246740957250763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205477947044831160638167175 308216920567246740957250763)
        ·
          refine ⟨462325380850870111435876145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308216920567246740957250763 462325380850870111435876145)
          ·
            refine ⟨346744035638152583576907109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462325380850870111435876145 346744035638152583576907109)
            ·
              refine ⟨65014506682153609420670083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346744035638152583576907109 65014506682153609420670083)
              ·
                refine ⟨97521760023230414131005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65014506682153609420670083 97521760023230414131005125)
                ·
                  refine ⟨18285330004355702649563461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97521760023230414131005125 18285330004355702649563461)
                  ·
                    refine ⟨3428499375816694246793149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18285330004355702649563461 3428499375816694246793149)
                    ·
                      refine ⟨1285687265931260342547431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428499375816694246793149 1285687265931260342547431)
                      ·
                        rfl

theorem cell23_2503867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].length) (baseStart_2503867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503867 prefixEnd_2503867 := by exact prefixLift 2503867
  have htrace : WordTrace (prefixWord ++ tailWord_2503867) baseStart_2503867 baseEnd_2503867 := by
    simpa [prefixWord, tailWord_2503867, baseEnd_2503867] using wordTrace_append hprefix tailTrace_2503867
  have hstable : (prefixWord ++ tailWord_2503867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503867).length < 2 ^ (prefixWord ++ tailWord_2503867).sum := by decide
  have hdescent : baseEnd_2503867 < baseStart_2503867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503868 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_2503868 : Nat := 118140960795 + 2503868 * 2 ^ 59
def prefixEnd_2503868 : Nat := 4983230072969 + 3 ^ 40 * 2503868 * 2
def baseEnd_2503868 : Nat := 1285687779411914838634927

theorem tailTrace_2503868 : CollatzResearch.WordTrace tailWord_2503868 prefixEnd_2503868 1285687779411914838634927 := by
  unfold tailWord_2503868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45661784246460668727208129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60882378995280891636277505 45661784246460668727208129)
  ·
    refine ⟨34246338184845501545406097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45661784246460668727208129 34246338184845501545406097)
    ·
      refine ⟨25684753638634126159054573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34246338184845501545406097 25684753638634126159054573)
      ·
        refine ⟨9631782614487797309645465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25684753638634126159054573 9631782614487797309645465)
        ·
          refine ⟨7223836960865847982234099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9631782614487797309645465 7223836960865847982234099)
          ·
            refine ⟨10835755441298771973351149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223836960865847982234099 10835755441298771973351149)
            ·
              refine ⟨4063408290487039490006681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10835755441298771973351149 4063408290487039490006681)
              ·
                refine ⟨3047556217865279617505011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063408290487039490006681 3047556217865279617505011)
                ·
                  refine ⟨4571334326797919426257517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047556217865279617505011 4571334326797919426257517)
                  ·
                    refine ⟨1714250372549219784846569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4571334326797919426257517 1714250372549219784846569)
                    ·
                      refine ⟨1285687779411914838634927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714250372549219784846569 1285687779411914838634927)
                      ·
                        rfl

theorem cell23_2503868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_2503868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503868 prefixEnd_2503868 := by exact prefixLift 2503868
  have htrace : WordTrace (prefixWord ++ tailWord_2503868) baseStart_2503868 baseEnd_2503868 := by
    simpa [prefixWord, tailWord_2503868, baseEnd_2503868] using wordTrace_append hprefix tailTrace_2503868
  have hstable : (prefixWord ++ tailWord_2503868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503868).length < 2 ^ (prefixWord ++ tailWord_2503868).sum := by decide
  have hdescent : baseEnd_2503868 < baseStart_2503868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503877 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2503877 : Nat := 118140960795 + 2503877 * 2 ^ 59
def prefixEnd_2503877 : Nat := 4983230072969 + 3 ^ 40 * 2503877 * 2
def baseEnd_2503877 : Nat := 1285692400737805303422385

theorem tailTrace_2503877 : CollatzResearch.WordTrace tailWord_2503877 prefixEnd_2503877 1285692400737805303422385 := by
  unfold tailWord_2503877
  simp only [CollatzResearch.WordTrace]
  refine ⟨91323896749888731991493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60882597833259154660995923 91323896749888731991493885)
  ·
    refine ⟨34246461281208274496810207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91323896749888731991493885 34246461281208274496810207)
    ·
      refine ⟨51369691921812411745215311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34246461281208274496810207 51369691921812411745215311)
      ·
        refine ⟨77054537882718617617822967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51369691921812411745215311 77054537882718617617822967)
        ·
          refine ⟨115581806824077926426734451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77054537882718617617822967 115581806824077926426734451)
          ·
            refine ⟨173372710236116889640101677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115581806824077926426734451 173372710236116889640101677)
            ·
              refine ⟨65014766338543833615038129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173372710236116889640101677 65014766338543833615038129)
              ·
                refine ⟨48761074753907875211278597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65014766338543833615038129 48761074753907875211278597)
                ·
                  refine ⟨9142701516357726602114737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48761074753907875211278597 9142701516357726602114737)
                  ·
                    refine ⟨6857026137268294951586053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9142701516357726602114737 6857026137268294951586053)
                    ·
                      refine ⟨1285692400737805303422385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6857026137268294951586053 1285692400737805303422385)
                      ·
                        rfl

theorem cell23_2503877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2503877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503877 prefixEnd_2503877 := by exact prefixLift 2503877
  have htrace : WordTrace (prefixWord ++ tailWord_2503877) baseStart_2503877 baseEnd_2503877 := by
    simpa [prefixWord, tailWord_2503877, baseEnd_2503877] using wordTrace_append hprefix tailTrace_2503877
  have hstable : (prefixWord ++ tailWord_2503877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503877).length < 2 ^ (prefixWord ++ tailWord_2503877).sum := by decide
  have hdescent : baseEnd_2503877 < baseStart_2503877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503911 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2503911 : Nat := 118140960795 + 2503911 * 2 ^ 59
def prefixEnd_2503911 : Nat := 4983230072969 + 3 ^ 40 * 2503911 * 2
def baseEnd_2503911 : Nat := 1285709859080058170397229

theorem tailTrace_2503911 : CollatzResearch.WordTrace tailWord_2503911 prefixEnd_2503911 1285709859080058170397229 := by
  unfold tailWord_2503911
  simp only [CollatzResearch.WordTrace]
  refine ⟨91325136831765555798231587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60883424554510370532154391 91325136831765555798231587)
  ·
    refine ⟨136987705247648333697347381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91325136831765555798231587 136987705247648333697347381)
    ·
      refine ⟨12842597366967031284126317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136987705247648333697347381 12842597366967031284126317)
      ·
        refine ⟨4815974012612636731547369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12842597366967031284126317 4815974012612636731547369)
        ·
          refine ⟨3611980509459477548660527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4815974012612636731547369 3611980509459477548660527)
          ·
            refine ⟨5417970764189216322990791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611980509459477548660527 5417970764189216322990791)
            ·
              refine ⟨8126956146283824484486187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417970764189216322990791 8126956146283824484486187)
              ·
                refine ⟨12190434219425736726729281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126956146283824484486187 12190434219425736726729281)
                ·
                  refine ⟨9142825664569302545046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12190434219425736726729281 9142825664569302545046961)
                  ·
                    refine ⟨6857119248426976908785221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9142825664569302545046961 6857119248426976908785221)
                    ·
                      refine ⟨1285709859080058170397229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6857119248426976908785221 1285709859080058170397229)
                      ·
                        rfl

theorem cell23_2503911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2503911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503911 prefixEnd_2503911 := by exact prefixLift 2503911
  have htrace : WordTrace (prefixWord ++ tailWord_2503911) baseStart_2503911 baseEnd_2503911 := by
    simpa [prefixWord, tailWord_2503911, baseEnd_2503911] using wordTrace_append hprefix tailTrace_2503911
  have hstable : (prefixWord ++ tailWord_2503911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503911).length < 2 ^ (prefixWord ++ tailWord_2503911).sum := by decide
  have hdescent : baseEnd_2503911 < baseStart_2503911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503914 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2503914 : Nat := 118140960795 + 2503914 * 2 ^ 59
def prefixEnd_2503914 : Nat := 4983230072969 + 3 ^ 40 * 2503914 * 2
def baseEnd_2503914 : Nat := 1285711399522021658659715

theorem tailTrace_2503914 : CollatzResearch.WordTrace tailWord_2503914 prefixEnd_2503914 1285711399522021658659715 := by
  unfold tailWord_2503914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831311562688671827647699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60883497500503124873727197 22831311562688671827647699)
  ·
    refine ⟨34246967344033007741471549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22831311562688671827647699 34246967344033007741471549)
    ·
      refine ⟨12842612754012377903051831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34246967344033007741471549 12842612754012377903051831)
      ·
        refine ⟨19263919131018566854577747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842612754012377903051831 19263919131018566854577747)
        ·
          refine ⟨28895878696527850281866621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19263919131018566854577747 28895878696527850281866621)
          ·
            refine ⟨10835954511197943855699983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28895878696527850281866621 10835954511197943855699983)
            ·
              refine ⟨16253931766796915783549975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10835954511197943855699983 16253931766796915783549975)
              ·
                refine ⟨24380897650195373675324963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16253931766796915783549975 24380897650195373675324963)
                ·
                  refine ⟨36571346475293060512987445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24380897650195373675324963 36571346475293060512987445)
                  ·
                    refine ⟨3428563732058724423092573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36571346475293060512987445 3428563732058724423092573)
                    ·
                      refine ⟨1285711399522021658659715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428563732058724423092573 1285711399522021658659715)
                      ·
                        rfl

theorem cell23_2503914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2503914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503914 prefixEnd_2503914 := by exact prefixLift 2503914
  have htrace : WordTrace (prefixWord ++ tailWord_2503914) baseStart_2503914 baseEnd_2503914 := by
    simpa [prefixWord, tailWord_2503914, baseEnd_2503914] using wordTrace_append hprefix tailTrace_2503914
  have hstable : (prefixWord ++ tailWord_2503914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503914).length < 2 ^ (prefixWord ++ tailWord_2503914).sum := by decide
  have hdescent : baseEnd_2503914 < baseStart_2503914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503971 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 4, 2]
def baseStart_2503971 : Nat := 118140960795 + 2503971 * 2 ^ 59
def prefixEnd_2503971 : Nat := 4983230072969 + 3 ^ 40 * 2503971 * 2
def baseEnd_2503971 : Nat := 1285740667919327935646953

theorem tailTrace_2503971 : CollatzResearch.WordTrace tailWord_2503971 prefixEnd_2503971 1285740667919327935646953 := by
  unfold tailWord_2503971
  simp only [CollatzResearch.WordTrace]
  refine ⟨91327325211548186045415767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60884883474365457363610511 91327325211548186045415767)
  ·
    refine ⟨136990987817322279068123651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91327325211548186045415767 136990987817322279068123651)
    ·
      refine ⟨205486481725983418602185477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136990987817322279068123651 205486481725983418602185477)
      ·
        refine ⟨38528715323621890987909777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205486481725983418602185477 38528715323621890987909777)
        ·
          refine ⟨28896536492716418240932333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38528715323621890987909777 28896536492716418240932333)
          ·
            refine ⟨10836201184768656840349625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28896536492716418240932333 10836201184768656840349625)
            ·
              refine ⟨8127150888576492630262219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10836201184768656840349625 8127150888576492630262219)
              ·
                refine ⟨12190726332864738945393329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8127150888576492630262219 12190726332864738945393329)
                ·
                  refine ⟨9143044749648554209044997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12190726332864738945393329 9143044749648554209044997)
                  ·
                    refine ⟨1714320890559103914195937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9143044749648554209044997 1714320890559103914195937)
                    ·
                      refine ⟨1285740667919327935646953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714320890559103914195937 1285740667919327935646953)
                      ·
                        rfl

theorem cell23_2503971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_2503971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2503971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2503971 prefixEnd_2503971 := by exact prefixLift 2503971
  have htrace : WordTrace (prefixWord ++ tailWord_2503971) baseStart_2503971 baseEnd_2503971 := by
    simpa [prefixWord, tailWord_2503971, baseEnd_2503971] using wordTrace_append hprefix tailTrace_2503971
  have hstable : (prefixWord ++ tailWord_2503971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503971).length < 2 ^ (prefixWord ++ tailWord_2503971).sum := by decide
  have hdescent : baseEnd_2503971 < baseStart_2503971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504024 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_2504024 : Nat := 118140960795 + 2504024 * 2 ^ 59
def prefixEnd_2504024 : Nat := 4983230072969 + 3 ^ 40 * 2504024 * 2
def baseEnd_2504024 : Nat := 428589294131338742761403

theorem tailTrace_2504024 : CollatzResearch.WordTrace tailWord_2504024 prefixEnd_2504024 428589294131338742761403 := by
  unfold tailWord_2504024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45664629140178088048547563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60886172186904117398063417 45664629140178088048547563)
  ·
    refine ⟨68496943710267132072821345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45664629140178088048547563 68496943710267132072821345)
    ·
      refine ⟨51372707782700349054616009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68496943710267132072821345 51372707782700349054616009)
      ·
        refine ⟨38529530837025261790962007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51372707782700349054616009 38529530837025261790962007)
        ·
          refine ⟨57794296255537892686443011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38529530837025261790962007 57794296255537892686443011)
          ·
            refine ⟨86691444383306839029664517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57794296255537892686443011 86691444383306839029664517)
            ·
              refine ⟨16254645821870032318062097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86691444383306839029664517 16254645821870032318062097)
              ·
                refine ⟨12190984366402524238546573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16254645821870032318062097 12190984366402524238546573)
                ·
                  refine ⟨4571619137400946589454965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12190984366402524238546573 4571619137400946589454965)
                  ·
                    refine ⟨428589294131338742761403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4571619137400946589454965 428589294131338742761403)
                    ·
                      rfl

theorem cell23_2504024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_2504024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504024 prefixEnd_2504024 := by exact prefixLift 2504024
  have htrace : WordTrace (prefixWord ++ tailWord_2504024) baseStart_2504024 baseEnd_2504024 := by
    simpa [prefixWord, tailWord_2504024, baseEnd_2504024] using wordTrace_append hprefix tailTrace_2504024
  have hstable : (prefixWord ++ tailWord_2504024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504024).length < 2 ^ (prefixWord ++ tailWord_2504024).sum := by decide
  have hdescent : baseEnd_2504024 < baseStart_2504024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504031 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 6, 3, 2]
def baseStart_2504031 : Nat := 118140960795 + 2504031 * 2 ^ 59
def prefixEnd_2504031 : Nat := 4983230072969 + 3 ^ 40 * 2504031 * 2
def baseEnd_2504031 : Nat := 1285771476758597700896677

theorem tailTrace_2504031 : CollatzResearch.WordTrace tailWord_2504031 prefixEnd_2504031 1285771476758597700896677 := by
  unfold tailWord_2504031
  simp only [CollatzResearch.WordTrace]
  refine ⟨91329513591330816292599947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60886342394220544195066631 91329513591330816292599947)
  ·
    refine ⟨136994270386996224438899921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91329513591330816292599947 136994270386996224438899921)
    ·
      refine ⟨102745702790247168329174941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136994270386996224438899921 102745702790247168329174941)
      ·
        refine ⟨38529638546342688123440603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102745702790247168329174941 38529638546342688123440603)
        ·
          refine ⟨57794457819514032185160905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38529638546342688123440603 57794457819514032185160905)
          ·
            refine ⟨43345843364635524138870679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57794457819514032185160905 43345843364635524138870679)
            ·
              refine ⟨65018765046953286208306019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43345843364635524138870679 65018765046953286208306019)
              ·
                refine ⟨97528147570429929312459029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65018765046953286208306019 97528147570429929312459029)
                ·
                  refine ⟨4571631917363902936521517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97528147570429929312459029 4571631917363902936521517)
                  ·
                    refine ⟨1714361969011463601195569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4571631917363902936521517 1714361969011463601195569)
                    ·
                      refine ⟨1285771476758597700896677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714361969011463601195569 1285771476758597700896677)
                      ·
                        rfl

theorem cell23_2504031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_2504031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504031 prefixEnd_2504031 := by exact prefixLift 2504031
  have htrace : WordTrace (prefixWord ++ tailWord_2504031) baseStart_2504031 baseEnd_2504031 := by
    simpa [prefixWord, tailWord_2504031, baseEnd_2504031] using wordTrace_append hprefix tailTrace_2504031
  have hstable : (prefixWord ++ tailWord_2504031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504031).length < 2 ^ (prefixWord ++ tailWord_2504031).sum := by decide
  have hdescent : baseEnd_2504031 < baseStart_2504031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504048 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2]
def baseStart_2504048 : Nat := 118140960795 + 2504048 * 2 ^ 59
def prefixEnd_2504048 : Nat := 4983230072969 + 3 ^ 40 * 2504048 * 2
def baseEnd_2504048 : Nat := 1285780205929724134384099

theorem tailTrace_2504048 : CollatzResearch.WordTrace tailWord_2504048 prefixEnd_2504048 1285780205929724134384099 := by
  unfold tailWord_2504048
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665066816134614097984399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60886755754846152130645865 45665066816134614097984399)
  ·
    refine ⟨68497600224201921146976599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45665066816134614097984399 68497600224201921146976599)
    ·
      refine ⟨102746400336302881720464899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68497600224201921146976599 102746400336302881720464899)
      ·
        refine ⟨154119600504454322580697349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102746400336302881720464899 154119600504454322580697349)
        ·
          refine ⟨28897425094585185483880753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154119600504454322580697349 28897425094585185483880753)
          ·
            refine ⟨21673068820938889112910565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28897425094585185483880753 21673068820938889112910565)
            ·
              refine ⟨4063700403926041708670731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21673068820938889112910565 4063700403926041708670731)
              ·
                refine ⟨6095550605889062563006097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063700403926041708670731 6095550605889062563006097)
                ·
                  refine ⟨4571662954416796922254573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6095550605889062563006097 4571662954416796922254573)
                  ·
                    refine ⟨1714373607906298845845465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4571662954416796922254573 1714373607906298845845465)
                    ·
                      refine ⟨1285780205929724134384099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714373607906298845845465 1285780205929724134384099)
                      ·
                        rfl

theorem cell23_2504048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2].length) (baseStart_2504048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504048 prefixEnd_2504048 := by exact prefixLift 2504048
  have htrace : WordTrace (prefixWord ++ tailWord_2504048) baseStart_2504048 baseEnd_2504048 := by
    simpa [prefixWord, tailWord_2504048, baseEnd_2504048] using wordTrace_append hprefix tailTrace_2504048
  have hstable : (prefixWord ++ tailWord_2504048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504048).length < 2 ^ (prefixWord ++ tailWord_2504048).sum := by decide
  have hdescent : baseEnd_2504048 < baseStart_2504048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504072 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2504072 : Nat := 118140960795 + 2504072 * 2 ^ 59
def prefixEnd_2504072 : Nat := 4983230072969 + 3 ^ 40 * 2504072 * 2
def baseEnd_2504072 : Nat := 1285792529465432040483989

theorem tailTrace_2504072 : CollatzResearch.WordTrace tailWord_2504072 prefixEnd_2504072 1285792529465432040483989 := by
  unfold tailWord_2504072
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665504492091140147421235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60887339322788186863228313 45665504492091140147421235)
  ·
    refine ⟨68498256738136710221131853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45665504492091140147421235 68498256738136710221131853)
    ·
      refine ⟨25686846276801266332924445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68498256738136710221131853 25686846276801266332924445)
      ·
        refine ⟨9632567353800474874846667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25686846276801266332924445 9632567353800474874846667)
        ·
          refine ⟨14448851030700712312270001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632567353800474874846667 14448851030700712312270001)
          ·
            refine ⟨10836638273025534234202501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14448851030700712312270001 10836638273025534234202501)
            ·
              refine ⟨2031869676192287668912969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10836638273025534234202501 2031869676192287668912969)
              ·
                refine ⟨1523902257144215751684727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031869676192287668912969 1523902257144215751684727)
                ·
                  refine ⟨2285853385716323627527091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523902257144215751684727 2285853385716323627527091)
                  ·
                    refine ⟨3428780078574485441290637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285853385716323627527091 3428780078574485441290637)
                    ·
                      refine ⟨1285792529465432040483989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428780078574485441290637 1285792529465432040483989)
                      ·
                        rfl

theorem cell23_2504072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2504072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504072 prefixEnd_2504072 := by exact prefixLift 2504072
  have htrace : WordTrace (prefixWord ++ tailWord_2504072) baseStart_2504072 baseEnd_2504072 := by
    simpa [prefixWord, tailWord_2504072, baseEnd_2504072] using wordTrace_append hprefix tailTrace_2504072
  have hstable : (prefixWord ++ tailWord_2504072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504072).length < 2 ^ (prefixWord ++ tailWord_2504072).sum := by decide
  have hdescent : baseEnd_2504072 < baseStart_2504072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504088 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_2504088 : Nat := 118140960795 + 2504088 * 2 ^ 59
def prefixEnd_2504088 : Nat := 4983230072969 + 3 ^ 40 * 2504088 * 2
def baseEnd_2504088 : Nat := 428600248385301325961305

theorem tailTrace_2504088 : CollatzResearch.WordTrace tailWord_2504088 prefixEnd_2504088 428600248385301325961305 := by
  unfold tailWord_2504088
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665796276062157513712459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60887728368082876684949945 45665796276062157513712459)
  ·
    refine ⟨68498694414093236270568689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45665796276062157513712459 68498694414093236270568689)
    ·
      refine ⟨51374020810569927202926517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68498694414093236270568689 51374020810569927202926517)
      ·
        refine ⟨4816314450990930675274361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51374020810569927202926517 4816314450990930675274361)
        ·
          refine ⟨3612235838243198006455771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4816314450990930675274361 3612235838243198006455771)
          ·
            refine ⟨5418353757364797009683657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612235838243198006455771 5418353757364797009683657)
            ·
              refine ⟨4063765318023597757262743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418353757364797009683657 4063765318023597757262743)
              ·
                refine ⟨6095647977035396635894115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063765318023597757262743 6095647977035396635894115)
                ·
                  refine ⟨9143471965553094953841173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095647977035396635894115 9143471965553094953841173)
                  ·
                    refine ⟨428600248385301325961305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9143471965553094953841173 428600248385301325961305)
                    ·
                      rfl

theorem cell23_2504088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_2504088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504088 prefixEnd_2504088 := by exact prefixLift 2504088
  have htrace : WordTrace (prefixWord ++ tailWord_2504088) baseStart_2504088 baseEnd_2504088 := by
    simpa [prefixWord, tailWord_2504088, baseEnd_2504088] using wordTrace_append hprefix tailTrace_2504088
  have hstable : (prefixWord ++ tailWord_2504088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504088).length < 2 ^ (prefixWord ++ tailWord_2504088).sum := by decide
  have hdescent : baseEnd_2504088 < baseStart_2504088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504095 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2504095 : Nat := 118140960795 + 2504095 * 2 ^ 59
def prefixEnd_2504095 : Nat := 4983230072969 + 3 ^ 40 * 2504095 * 2
def baseEnd_2504095 : Nat := 1285804339520485450496383

theorem tailTrace_2504095 : CollatzResearch.WordTrace tailWord_2504095 prefixEnd_2504095 1285804339520485450496383 := by
  unfold tailWord_2504095
  simp only [CollatzResearch.WordTrace]
  refine ⟨91331847863098955222929739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60887898575399303481953159 91331847863098955222929739)
  ·
    refine ⟨136997771794648432834394609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91331847863098955222929739 136997771794648432834394609)
    ·
      refine ⟨102748328845986324625795957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136997771794648432834394609 102748328845986324625795957)
      ·
        refine ⟨9632655829311217933668371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102748328845986324625795957 9632655829311217933668371)
        ·
          refine ⟨14448983743966826900502557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632655829311217933668371 14448983743966826900502557)
          ·
            refine ⟨5418368903987560087688459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14448983743966826900502557 5418368903987560087688459)
            ·
              refine ⟨8127553355981340131532689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418368903987560087688459 8127553355981340131532689)
              ·
                refine ⟨6095665016986005098649517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8127553355981340131532689 6095665016986005098649517)
                ·
                  refine ⟨2285874381369751911993569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095665016986005098649517 2285874381369751911993569)
                  ·
                    refine ⟨1714405786027313933995177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285874381369751911993569 1714405786027313933995177)
                    ·
                      refine ⟨1285804339520485450496383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714405786027313933995177 1285804339520485450496383)
                      ·
                        rfl

theorem cell23_2504095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2504095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504095 prefixEnd_2504095 := by exact prefixLift 2504095
  have htrace : WordTrace (prefixWord ++ tailWord_2504095) baseStart_2504095 baseEnd_2504095 := by
    simpa [prefixWord, tailWord_2504095, baseEnd_2504095] using wordTrace_append hprefix tailTrace_2504095
  have hstable : (prefixWord ++ tailWord_2504095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504095).length < 2 ^ (prefixWord ++ tailWord_2504095).sum := by decide
  have hdescent : baseEnd_2504095 < baseStart_2504095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504098 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2504098 : Nat := 118140960795 + 2504098 * 2 ^ 59
def prefixEnd_2504098 : Nat := 4983230072969 + 3 ^ 40 * 2504098 * 2
def baseEnd_2504098 : Nat := 1285805879962448938758869

theorem tailTrace_2504098 : CollatzResearch.WordTrace tailWord_2504098 prefixEnd_2504098 1285805879962448938758869 := by
  unfold tailWord_2504098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22832989320522021683822237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60887971521392057823525965 22832989320522021683822237)
  ·
    refine ⟨8562370995195758131433339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22832989320522021683822237 8562370995195758131433339)
    ·
      refine ⟨12843556492793637197150009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562370995195758131433339 12843556492793637197150009)
      ·
        refine ⟨9632667369595227897862507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12843556492793637197150009 9632667369595227897862507)
        ·
          refine ⟨14449001054392841846793761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632667369595227897862507 14449001054392841846793761)
          ·
            refine ⟨10836750790794631385095321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14449001054392841846793761 10836750790794631385095321)
            ·
              refine ⟨8127563093095973538821491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10836750790794631385095321 8127563093095973538821491)
              ·
                refine ⟨12191344639643960308232237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8127563093095973538821491 12191344639643960308232237)
                ·
                  refine ⟨4571754239866485115587089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12191344639643960308232237 4571754239866485115587089)
                  ·
                    refine ⟨3428815679899863836690317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571754239866485115587089 3428815679899863836690317)
                    ·
                      refine ⟨1285805879962448938758869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428815679899863836690317 1285805879962448938758869)
                      ·
                        rfl

theorem cell23_2504098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2504098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504098 prefixEnd_2504098 := by exact prefixLift 2504098
  have htrace : WordTrace (prefixWord ++ tailWord_2504098) baseStart_2504098 baseEnd_2504098 := by
    simpa [prefixWord, tailWord_2504098, baseEnd_2504098] using wordTrace_append hprefix tailTrace_2504098
  have hstable : (prefixWord ++ tailWord_2504098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504098).length < 2 ^ (prefixWord ++ tailWord_2504098).sum := by decide
  have hdescent : baseEnd_2504098 < baseStart_2504098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504114 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_2504114 : Nat := 118140960795 + 2504114 * 2 ^ 59
def prefixEnd_2504114 : Nat := 4983230072969 + 3 ^ 40 * 2504114 * 2
def baseEnd_2504114 : Nat := 428604698550973625386265

theorem tailTrace_2504114 : CollatzResearch.WordTrace tailWord_2504114 prefixEnd_2504114 428604698550973625386265 := by
  unfold tailWord_2504114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833135212507530366967849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60888360566686747645247597 22833135212507530366967849)
  ·
    refine ⟨17124851409380647775225887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22833135212507530366967849 17124851409380647775225887)
    ·
      refine ⟨25687277114070971662838831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124851409380647775225887 25687277114070971662838831)
      ·
        refine ⟨38530915671106457494258247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25687277114070971662838831 38530915671106457494258247)
        ·
          refine ⟨57796373506659686241387371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38530915671106457494258247 57796373506659686241387371)
          ·
            refine ⟨86694560259989529362081057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57796373506659686241387371 86694560259989529362081057)
            ·
              refine ⟨65020920194992147021560793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86694560259989529362081057 65020920194992147021560793)
              ·
                refine ⟨48765690146244110266170595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65020920194992147021560793 48765690146244110266170595)
                ·
                  refine ⟨73148535219366165399255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48765690146244110266170595 73148535219366165399255893)
                  ·
                    refine ⟨428604698550973625386265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73148535219366165399255893 428604698550973625386265)
                    ·
                      rfl

theorem cell23_2504114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_2504114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504114 prefixEnd_2504114 := by exact prefixLift 2504114
  have htrace : WordTrace (prefixWord ++ tailWord_2504114) baseStart_2504114 baseEnd_2504114 := by
    simpa [prefixWord, tailWord_2504114, baseEnd_2504114] using wordTrace_append hprefix tailTrace_2504114
  have hstable : (prefixWord ++ tailWord_2504114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504114).length < 2 ^ (prefixWord ++ tailWord_2504114).sum := by decide
  have hdescent : baseEnd_2504114 < baseStart_2504114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504168 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2504168 : Nat := 118140960795 + 2504168 * 2 ^ 59
def prefixEnd_2504168 : Nat := 4983230072969 + 3 ^ 40 * 2504168 * 2
def baseEnd_2504168 : Nat := 1285841823608263664883547

theorem tailTrace_2504168 : CollatzResearch.WordTrace tailWord_2504168 prefixEnd_2504168 1285841823608263664883547 := by
  unfold tailWord_2504168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45667255195917244345168579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60889673594556325793558105 45667255195917244345168579)
  ·
    refine ⟨68500882793875866517752869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45667255195917244345168579 68500882793875866517752869)
    ·
      refine ⟨12843915523851724972078663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68500882793875866517752869 12843915523851724972078663)
      ·
        refine ⟨19265873285777587458117995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843915523851724972078663 19265873285777587458117995)
        ·
          refine ⟨28898809928666381187176993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19265873285777587458117995 28898809928666381187176993)
          ·
            refine ⟨21674107446499785890382745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28898809928666381187176993 21674107446499785890382745)
            ·
              refine ⟨16255580584874839417787059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21674107446499785890382745 16255580584874839417787059)
              ·
                refine ⟨24383370877312259126680589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16255580584874839417787059 24383370877312259126680589)
                ·
                  refine ⟨9143764078992097172505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24383370877312259126680589 9143764078992097172505221)
                  ·
                    refine ⟨1714455764811018219844729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9143764078992097172505221 1714455764811018219844729)
                    ·
                      refine ⟨1285841823608263664883547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714455764811018219844729 1285841823608263664883547)
                      ·
                        rfl

theorem cell23_2504168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2504168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504168 prefixEnd_2504168 := by exact prefixLift 2504168
  have htrace : WordTrace (prefixWord ++ tailWord_2504168) baseStart_2504168 baseEnd_2504168 := by
    simpa [prefixWord, tailWord_2504168, baseEnd_2504168] using wordTrace_append hprefix tailTrace_2504168
  have hstable : (prefixWord ++ tailWord_2504168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504168).length < 2 ^ (prefixWord ++ tailWord_2504168).sum := by decide
  have hdescent : baseEnd_2504168 < baseStart_2504168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504185 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 2, 2, 2]
def baseStart_2504185 : Nat := 118140960795 + 2504185 * 2 ^ 59
def prefixEnd_2504185 : Nat := 4983230072969 + 3 ^ 40 * 2504185 * 2
def baseEnd_2504185 : Nat := 1285850552779390098370969

theorem tailTrace_2504185 : CollatzResearch.WordTrace tailWord_2504185 prefixEnd_2504185 1285850552779390098370969 := by
  unfold tailWord_2504185
  simp only [CollatzResearch.WordTrace]
  refine ⟨91335130432772900593706009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60890086955181933729137339 91335130432772900593706009)
  ·
    refine ⟨68501347824579675445279507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91335130432772900593706009 68501347824579675445279507)
    ·
      refine ⟨102752021736869513167919261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68501347824579675445279507 102752021736869513167919261)
      ·
        refine ⟨38532008151326067437969723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102752021736869513167919261 38532008151326067437969723)
        ·
          refine ⟨57798012226989101156954585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38532008151326067437969723 57798012226989101156954585)
          ·
            refine ⟨43348509170241825867715939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57798012226989101156954585 43348509170241825867715939)
            ·
              refine ⟨65022763755362738801573909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43348509170241825867715939 65022763755362738801573909)
              ·
                refine ⟨3047942051032628381323777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65022763755362738801573909 3047942051032628381323777)
                ·
                  refine ⟨2285956538274471285992833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047942051032628381323777 2285956538274471285992833)
                  ·
                    refine ⟨1714467403705853464494625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285956538274471285992833 1714467403705853464494625)
                    ·
                      refine ⟨1285850552779390098370969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714467403705853464494625 1285850552779390098370969)
                      ·
                        rfl

theorem cell23_2504185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_2504185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504185 prefixEnd_2504185 := by exact prefixLift 2504185
  have htrace : WordTrace (prefixWord ++ tailWord_2504185) baseStart_2504185 baseEnd_2504185 := by
    simpa [prefixWord, tailWord_2504185, baseEnd_2504185] using wordTrace_append hprefix tailTrace_2504185
  have hstable : (prefixWord ++ tailWord_2504185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504185).length < 2 ^ (prefixWord ++ tailWord_2504185).sum := by decide
  have hdescent : baseEnd_2504185 < baseStart_2504185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504196 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2504196 : Nat := 118140960795 + 2504196 * 2 ^ 59
def prefixEnd_2504196 : Nat := 4983230072969 + 3 ^ 40 * 2504196 * 2
def baseEnd_2504196 : Nat := 1285856201066589555333419

theorem tailTrace_2504196 : CollatzResearch.WordTrace tailWord_2504196 prefixEnd_2504196 1285856201066589555333419 := by
  unfold tailWord_2504196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45667765817866524736178221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60890354423822032981570961 45667765817866524736178221)
  ·
    refine ⟨17125412181699946776066833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45667765817866524736178221 17125412181699946776066833)
    ·
      refine ⟨12844059136274960082050125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17125412181699946776066833 12844059136274960082050125)
      ·
        refine ⟨4816522176103110030768797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12844059136274960082050125 4816522176103110030768797)
        ·
          refine ⟨1806195816038666261538299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4816522176103110030768797 1806195816038666261538299)
          ·
            refine ⟨2709293724057999392307449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806195816038666261538299 2709293724057999392307449)
            ·
              refine ⟨2031970293043499544230587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709293724057999392307449 2031970293043499544230587)
              ·
                refine ⟨3047955439565249316345881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031970293043499544230587 3047955439565249316345881)
                ·
                  refine ⟨2285966579673936987259411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047955439565249316345881 2285966579673936987259411)
                  ·
                    refine ⟨3428949869510905480889117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285966579673936987259411 3428949869510905480889117)
                    ·
                      refine ⟨1285856201066589555333419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428949869510905480889117 1285856201066589555333419)
                      ·
                        rfl

theorem cell23_2504196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2504196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504196 prefixEnd_2504196 := by exact prefixLift 2504196
  have htrace : WordTrace (prefixWord ++ tailWord_2504196) baseStart_2504196 baseEnd_2504196 := by
    simpa [prefixWord, tailWord_2504196, baseEnd_2504196] using wordTrace_append hprefix tailTrace_2504196
  have hstable : (prefixWord ++ tailWord_2504196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504196).length < 2 ^ (prefixWord ++ tailWord_2504196).sum := by decide
  have hdescent : baseEnd_2504196 < baseStart_2504196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504201 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_2504201 : Nat := 118140960795 + 2504201 * 2 ^ 59
def prefixEnd_2504201 : Nat := 4983230072969 + 3 ^ 40 * 2504201 * 2
def baseEnd_2504201 : Nat := 1285858768469862035770895

theorem tailTrace_2504201 : CollatzResearch.WordTrace tailWord_2504201 prefixEnd_2504201 1285858768469862035770895 := by
  unfold tailWord_2504201
  simp only [CollatzResearch.WordTrace]
  refine ⟨91335714000714935326288457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60890476000476623550858971 91335714000714935326288457)
  ·
    refine ⟨68501785500536201494716343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91335714000714935326288457 68501785500536201494716343)
    ·
      refine ⟨102752678250804302242074515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68501785500536201494716343 102752678250804302242074515)
      ·
        refine ⟨154129017376206453363111773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102752678250804302242074515 154129017376206453363111773)
        ·
          refine ⟨57798381516077420011166915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154129017376206453363111773 57798381516077420011166915)
          ·
            refine ⟨86697572274116130016750373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57798381516077420011166915 86697572274116130016750373)
            ·
              refine ⟨16255794801396774378140695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86697572274116130016750373 16255794801396774378140695)
              ·
                refine ⟨24383692202095161567211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16255794801396774378140695 24383692202095161567211043)
                ·
                  refine ⟨36575538303142742350816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24383692202095161567211043 36575538303142742350816565)
                  ·
                    refine ⟨3428956715919632095389053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36575538303142742350816565 3428956715919632095389053)
                    ·
                      refine ⟨1285858768469862035770895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3428956715919632095389053 1285858768469862035770895)
                      ·
                        rfl

theorem cell23_2504201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_2504201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504201 prefixEnd_2504201 := by exact prefixLift 2504201
  have htrace : WordTrace (prefixWord ++ tailWord_2504201) baseStart_2504201 baseEnd_2504201 := by
    simpa [prefixWord, tailWord_2504201, baseEnd_2504201] using wordTrace_append hprefix tailTrace_2504201
  have hstable : (prefixWord ++ tailWord_2504201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504201).length < 2 ^ (prefixWord ++ tailWord_2504201).sum := by decide
  have hdescent : baseEnd_2504201 < baseStart_2504201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504202 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_2504202 : Nat := 118140960795 + 2504202 * 2 ^ 59
def prefixEnd_2504202 : Nat := 4983230072969 + 3 ^ 40 * 2504202 * 2
def baseEnd_2504202 : Nat := 1285859281950516531858391

theorem tailTrace_2504202 : CollatzResearch.WordTrace tailWord_2504202 prefixEnd_2504202 1285859281950516531858391 := by
  unfold tailWord_2504202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833937618427828124268715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60890500315807541664716573 22833937618427828124268715)
  ·
    refine ⟨34250906427641742186403073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22833937618427828124268715 34250906427641742186403073)
    ·
      refine ⟨25688179820731306639802305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34250906427641742186403073 25688179820731306639802305)
      ·
        refine ⟨19266134865548479979851729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25688179820731306639802305 19266134865548479979851729)
        ·
          refine ⟨14449601149161359984888797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19266134865548479979851729 14449601149161359984888797)
          ·
            refine ⟨5418600430935509994333299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14449601149161359984888797 5418600430935509994333299)
            ·
              refine ⟨8127900646403264991499949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418600430935509994333299 8127900646403264991499949)
              ·
                refine ⟨3047962742401224371812481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8127900646403264991499949 3047962742401224371812481)
                ·
                  refine ⟨2285972056800918278859361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047962742401224371812481 2285972056800918278859361)
                  ·
                    refine ⟨1714479042600688709144521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285972056800918278859361 1714479042600688709144521)
                    ·
                      refine ⟨1285859281950516531858391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714479042600688709144521 1285859281950516531858391)
                      ·
                        rfl

theorem cell23_2504202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_2504202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504202 prefixEnd_2504202 := by exact prefixLift 2504202
  have htrace : WordTrace (prefixWord ++ tailWord_2504202) baseStart_2504202 baseEnd_2504202 := by
    simpa [prefixWord, tailWord_2504202, baseEnd_2504202] using wordTrace_append hprefix tailTrace_2504202
  have hstable : (prefixWord ++ tailWord_2504202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504202).length < 2 ^ (prefixWord ++ tailWord_2504202).sum := by decide
  have hdescent : baseEnd_2504202 < baseStart_2504202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504241 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2504241 : Nat := 118140960795 + 2504241 * 2 ^ 59
def prefixEnd_2504241 : Nat := 4983230072969 + 3 ^ 40 * 2504241 * 2
def baseEnd_2504241 : Nat := 1285879307696041879270711

theorem tailTrace_2504241 : CollatzResearch.WordTrace tailWord_2504241 prefixEnd_2504241 1285879307696041879270711 := by
  unfold tailWord_2504241
  simp only [CollatzResearch.WordTrace]
  refine ⟨91337172920570022157744577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60891448613713348105163051 91337172920570022157744577)
  ·
    refine ⟨68502879690427516618308433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91337172920570022157744577 68502879690427516618308433)
    ·
      refine ⟨51377159767820637463731325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68502879690427516618308433 51377159767820637463731325)
      ·
        refine ⟨19266434912932739048899247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51377159767820637463731325 19266434912932739048899247)
        ·
          refine ⟨28899652369399108573348871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19266434912932739048899247 28899652369399108573348871)
          ·
            refine ⟨43349478554098662860023307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28899652369399108573348871 43349478554098662860023307)
            ·
              refine ⟨65024217831147994290034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43349478554098662860023307 65024217831147994290034961)
              ·
                refine ⟨48768163373360995717526221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65024217831147994290034961 48768163373360995717526221)
                ·
                  refine ⟨18288061265010373394072333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48768163373360995717526221 18288061265010373394072333)
                  ·
                    refine ⟨6858022974378890022777125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18288061265010373394072333 6858022974378890022777125)
                    ·
                      refine ⟨1285879307696041879270711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6858022974378890022777125 1285879307696041879270711)
                      ·
                        rfl

theorem cell23_2504241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2504241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504241 prefixEnd_2504241 := by exact prefixLift 2504241
  have htrace : WordTrace (prefixWord ++ tailWord_2504241) baseStart_2504241 baseEnd_2504241 := by
    simpa [prefixWord, tailWord_2504241, baseEnd_2504241] using wordTrace_append hprefix tailTrace_2504241
  have hstable : (prefixWord ++ tailWord_2504241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504241).length < 2 ^ (prefixWord ++ tailWord_2504241).sum := by decide
  have hdescent : baseEnd_2504241 < baseStart_2504241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504268 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_2504268 : Nat := 118140960795 + 2504268 * 2 ^ 59
def prefixEnd_2504268 : Nat := 4983230072969 + 3 ^ 40 * 2504268 * 2
def baseEnd_2504268 : Nat := 428631057224571091211029

theorem tailTrace_2504268 : CollatzResearch.WordTrace tailWord_2504268 prefixEnd_2504268 428631057224571091211029 := by
  unfold tailWord_2504268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45669078845736102884488729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60892105127648137179318305 45669078845736102884488729)
  ·
    refine ⟨34251809134302077163366547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45669078845736102884488729 34251809134302077163366547)
    ·
      refine ⟨51377713701453115745049821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34251809134302077163366547 51377713701453115745049821)
      ·
        refine ⟨19266642638044918404393683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51377713701453115745049821 19266642638044918404393683)
        ·
          refine ⟨28899963957067377606590525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19266642638044918404393683 28899963957067377606590525)
          ·
            refine ⟨10837486483900266602471447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28899963957067377606590525 10837486483900266602471447)
            ·
              refine ⟨16256229725850399903707171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837486483900266602471447 16256229725850399903707171)
              ·
                refine ⟨24384344588775599855560757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16256229725850399903707171 24384344588775599855560757)
                ·
                  refine ⟨2286032305197712486458821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24384344588775599855560757 2286032305197712486458821)
                  ·
                    refine ⟨428631057224571091211029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286032305197712486458821 428631057224571091211029)
                    ·
                      rfl

theorem cell23_2504268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_2504268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504268 prefixEnd_2504268 := by exact prefixLift 2504268
  have htrace : WordTrace (prefixWord ++ tailWord_2504268) baseStart_2504268 baseEnd_2504268 := by
    simpa [prefixWord, tailWord_2504268, baseEnd_2504268] using wordTrace_append hprefix tailTrace_2504268
  have hstable : (prefixWord ++ tailWord_2504268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504268).length < 2 ^ (prefixWord ++ tailWord_2504268).sum := by decide
  have hdescent : baseEnd_2504268 < baseStart_2504268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504298 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_2504298 : Nat := 118140960795 + 2504298 * 2 ^ 59
def prefixEnd_2504298 : Nat := 4983230072969 + 3 ^ 40 * 2504298 * 2
def baseEnd_2504298 : Nat := 142878730677038684028661

theorem tailTrace_2504298 : CollatzResearch.WordTrace tailWord_2504298 prefixEnd_2504298 142878730677038684028661 := by
  unfold tailWord_2504298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22834812970340880223142387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60892834587575680595046365 22834812970340880223142387)
  ·
    refine ⟨34252219455511320334713581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22834812970340880223142387 34252219455511320334713581)
    ·
      refine ⟨12844582295816745125517593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34252219455511320334713581 12844582295816745125517593)
      ·
        refine ⟨9633436721862558844138195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12844582295816745125517593 9633436721862558844138195)
        ·
          refine ⟨14450155082793838266207293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633436721862558844138195 14450155082793838266207293)
          ·
            refine ⟨5418808156047689349827735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14450155082793838266207293 5418808156047689349827735)
            ·
              refine ⟨8128212234071534024741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418808156047689349827735 8128212234071534024741603)
              ·
                refine ⟨12192318351107301037112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128212234071534024741603 12192318351107301037112405)
                ·
                  refine ⟨142878730677038684028661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12192318351107301037112405 142878730677038684028661)
                  ·
                    rfl

theorem cell23_2504298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_2504298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504298 prefixEnd_2504298 := by exact prefixLift 2504298
  have htrace : WordTrace (prefixWord ++ tailWord_2504298) baseStart_2504298 baseEnd_2504298 := by
    simpa [prefixWord, tailWord_2504298, baseEnd_2504298] using wordTrace_append hprefix tailTrace_2504298
  have hstable : (prefixWord ++ tailWord_2504298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504298).length < 2 ^ (prefixWord ++ tailWord_2504298).sum := by decide
  have hdescent : baseEnd_2504298 < baseStart_2504298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504302 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2504302 : Nat := 118140960795 + 2504302 * 2 ^ 59
def prefixEnd_2504302 : Nat := 4983230072969 + 3 ^ 40 * 2504302 * 2
def baseEnd_2504302 : Nat := 428636876671988713535977

theorem tailTrace_2504302 : CollatzResearch.WordTrace tailWord_2504302 prefixEnd_2504302 428636876671988713535977 := by
  unfold tailWord_2504302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417424721668628696964395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60892931848899353050476773 11417424721668628696964395)
  ·
    refine ⟨17126137082502943045446593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11417424721668628696964395 17126137082502943045446593)
    ·
      refine ⟨12844602811877207284084945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17126137082502943045446593 12844602811877207284084945)
      ·
        refine ⟨9633452108907905463063709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12844602811877207284084945 9633452108907905463063709)
        ·
          refine ⟨3612544540840464548648891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9633452108907905463063709 3612544540840464548648891)
          ·
            refine ⟨5418816811260696822973337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612544540840464548648891 5418816811260696822973337)
            ·
              refine ⟨4064112608445522617230003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418816811260696822973337 4064112608445522617230003)
              ·
                refine ⟨6096168912668283925845005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064112608445522617230003 6096168912668283925845005)
                ·
                  refine ⟨2286063342250606472191877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6096168912668283925845005 2286063342250606472191877)
                  ·
                    refine ⟨428636876671988713535977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286063342250606472191877 428636876671988713535977)
                    ·
                      rfl

theorem cell23_2504302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2504302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504302 prefixEnd_2504302 := by exact prefixLift 2504302
  have htrace : WordTrace (prefixWord ++ tailWord_2504302) baseStart_2504302 baseEnd_2504302 := by
    simpa [prefixWord, tailWord_2504302, baseEnd_2504302] using wordTrace_append hprefix tailTrace_2504302
  have hstable : (prefixWord ++ tailWord_2504302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504302).length < 2 ^ (prefixWord ++ tailWord_2504302).sum := by decide
  have hdescent : baseEnd_2504302 < baseStart_2504302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504325 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_2504325 : Nat := 118140960795 + 2504325 * 2 ^ 59
def prefixEnd_2504325 : Nat := 4983230072969 + 3 ^ 40 * 2504325 * 2
def baseEnd_2504325 : Nat := 1285922440071019550620325

theorem tailTrace_2504325 : CollatzResearch.WordTrace tailWord_2504325 prefixEnd_2504325 1285922440071019550620325 := by
  unfold tailWord_2504325
  simp only [CollatzResearch.WordTrace]
  refine ⟨91340236652265704503802429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60893491101510469669201619 91340236652265704503802429)
  ·
    refine ⟨34252588744599639188925911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91340236652265704503802429 34252588744599639188925911)
    ·
      refine ⟨51378883116899458783388867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34252588744599639188925911 51378883116899458783388867)
      ·
        refine ⟨77068324675349188175083301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51378883116899458783388867 77068324675349188175083301)
        ·
          refine ⟨14450310876627972782828119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77068324675349188175083301 14450310876627972782828119)
          ·
            refine ⟨21675466314941959174242179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14450310876627972782828119 21675466314941959174242179)
            ·
              refine ⟨32513199472412938761363269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21675466314941959174242179 32513199472412938761363269)
              ·
                refine ⟨6096224901077426017755613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32513199472412938761363269 6096224901077426017755613)
                ·
                  refine ⟨2286084337904034756658355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6096224901077426017755613 2286084337904034756658355)
                  ·
                    refine ⟨3429126506856052134987533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2286084337904034756658355 3429126506856052134987533)
                    ·
                      refine ⟨1285922440071019550620325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3429126506856052134987533 1285922440071019550620325)
                      ·
                        rfl

theorem cell23_2504325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_2504325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504325 prefixEnd_2504325 := by exact prefixLift 2504325
  have htrace : WordTrace (prefixWord ++ tailWord_2504325) baseStart_2504325 baseEnd_2504325 := by
    simpa [prefixWord, tailWord_2504325, baseEnd_2504325] using wordTrace_append hprefix tailTrace_2504325
  have hstable : (prefixWord ++ tailWord_2504325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504325).length < 2 ^ (prefixWord ++ tailWord_2504325).sum := by decide
  have hdescent : baseEnd_2504325 < baseStart_2504325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504352 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2]
def baseStart_2504352 : Nat := 118140960795 + 2504352 * 2 ^ 59
def prefixEnd_2504352 : Nat := 4983230072969 + 3 ^ 40 * 2504352 * 2
def baseEnd_2504352 : Nat := 1285936304048690944982701

theorem tailTrace_2504352 : CollatzResearch.WordTrace tailWord_2504352 prefixEnd_2504352 1285936304048690944982701 := by
  unfold tailWord_2504352
  simp only [CollatzResearch.WordTrace]
  refine ⟨45670610711583944057517655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60894147615445258743356873 45670610711583944057517655)
  ·
    refine ⟨68505916067375916086276483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45670610711583944057517655 68505916067375916086276483)
    ·
      refine ⟨102758874101063874129414725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68505916067375916086276483 102758874101063874129414725)
      ·
        refine ⟨19267288893949476399265261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102758874101063874129414725 19267288893949476399265261)
        ·
          refine ⟨7225233335231053649724473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19267288893949476399265261 7225233335231053649724473)
          ·
            refine ⟨5418925001423290237293355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7225233335231053649724473 5418925001423290237293355)
            ·
              refine ⟨8128387502134935355940033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418925001423290237293355 8128387502134935355940033)
              ·
                refine ⟨6096290626601201516955025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8128387502134935355940033 6096290626601201516955025)
                ·
                  refine ⟨4572217969950901137716269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096290626601201516955025 4572217969950901137716269)
                  ·
                    refine ⟨1714581738731587926643601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4572217969950901137716269 1714581738731587926643601)
                    ·
                      refine ⟨1285936304048690944982701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714581738731587926643601 1285936304048690944982701)
                      ·
                        rfl

theorem cell23_2504352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_2504352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504352 prefixEnd_2504352 := by exact prefixLift 2504352
  have htrace : WordTrace (prefixWord ++ tailWord_2504352) baseStart_2504352 baseEnd_2504352 := by
    simpa [prefixWord, tailWord_2504352, baseEnd_2504352] using wordTrace_append hprefix tailTrace_2504352
  have hstable : (prefixWord ++ tailWord_2504352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504352).length < 2 ^ (prefixWord ++ tailWord_2504352).sum := by decide
  have hdescent : baseEnd_2504352 < baseStart_2504352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504365 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2504365 : Nat := 118140960795 + 2504365 * 2 ^ 59
def prefixEnd_2504365 : Nat := 4983230072969 + 3 ^ 40 * 2504365 * 2
def baseEnd_2504365 : Nat := 1285942979297199394120141

theorem tailTrace_2504365 : CollatzResearch.WordTrace tailWord_2504365 prefixEnd_2504365 1285942979297199394120141 := by
  unfold tailWord_2504365
  simp only [CollatzResearch.WordTrace]
  refine ⟨91341695572120791335258549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60894463714747194223505699 91341695572120791335258549)
  ·
    refine ⟨8563283959886324187680489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91341695572120791335258549 8563283959886324187680489)
    ·
      refine ⟨6422462969914743140760367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8563283959886324187680489 6422462969914743140760367)
      ·
        refine ⟨9633694454872114711140551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422462969914743140760367 9633694454872114711140551)
        ·
          refine ⟨14450541682308172066710827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633694454872114711140551 14450541682308172066710827)
          ·
            refine ⟨21675812523462258100066241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14450541682308172066710827 21675812523462258100066241)
            ·
              refine ⟨16256859392596693575049681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21675812523462258100066241 16256859392596693575049681)
              ·
                refine ⟨12192644544447520181287261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16256859392596693575049681 12192644544447520181287261)
                ·
                  refine ⟨4572241704167820067982723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12192644544447520181287261 4572241704167820067982723)
                  ·
                    refine ⟨6858362556251730101974085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4572241704167820067982723 6858362556251730101974085)
                    ·
                      refine ⟨1285942979297199394120141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6858362556251730101974085 1285942979297199394120141)
                      ·
                        rfl

theorem cell23_2504365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2504365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504365 prefixEnd_2504365 := by exact prefixLift 2504365
  have htrace : WordTrace (prefixWord ++ tailWord_2504365) baseStart_2504365 baseEnd_2504365 := by
    simpa [prefixWord, tailWord_2504365, baseEnd_2504365] using wordTrace_append hprefix tailTrace_2504365
  have hstable : (prefixWord ++ tailWord_2504365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504365).length < 2 ^ (prefixWord ++ tailWord_2504365).sum := by decide
  have hdescent : baseEnd_2504365 < baseStart_2504365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504366 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_2504366 : Nat := 118140960795 + 2504366 * 2 ^ 59
def prefixEnd_2504366 : Nat := 4983230072969 + 3 ^ 40 * 2504366 * 2
def baseEnd_2504366 : Nat := 142882610308650432245293

theorem tailTrace_2504366 : CollatzResearch.WordTrace tailWord_2504366 prefixEnd_2504366 142882610308650432245293 := by
  unfold tailWord_2504366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417716505639646063255619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60894488030078112337363301 11417716505639646063255619)
  ·
    refine ⟨17126574758459469094883429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11417716505639646063255619 17126574758459469094883429)
    ·
      refine ⟨3211232767211150455290643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17126574758459469094883429 3211232767211150455290643)
      ·
        refine ⟨4816849150816725682935965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211232767211150455290643 4816849150816725682935965)
        ·
          refine ⟨1806318431556272131100987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4816849150816725682935965 1806318431556272131100987)
          ·
            refine ⟨2709477647334408196651481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806318431556272131100987 2709477647334408196651481)
            ·
              refine ⟨2032108235500806147488611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709477647334408196651481 2032108235500806147488611)
              ·
                refine ⟨3048162353251209221232917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032108235500806147488611 3048162353251209221232917)
                ·
                  refine ⟨142882610308650432245293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048162353251209221232917 142882610308650432245293)
                  ·
                    rfl

theorem cell23_2504366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_2504366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504366 prefixEnd_2504366 := by exact prefixLift 2504366
  have htrace : WordTrace (prefixWord ++ tailWord_2504366) baseStart_2504366 baseEnd_2504366 := by
    simpa [prefixWord, tailWord_2504366, baseEnd_2504366] using wordTrace_append hprefix tailTrace_2504366
  have hstable : (prefixWord ++ tailWord_2504366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504366).length < 2 ^ (prefixWord ++ tailWord_2504366).sum := by decide
  have hdescent : baseEnd_2504366 < baseStart_2504366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504368 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_2504368 : Nat := 118140960795 + 2504368 * 2 ^ 59
def prefixEnd_2504368 : Nat := 4983230072969 + 3 ^ 40 * 2504368 * 2
def baseEnd_2504368 : Nat := 1285944519739162882382627

theorem tailTrace_2504368 : CollatzResearch.WordTrace tailWord_2504368 prefixEnd_2504368 1285944519739162882382627 := by
  unfold tailWord_2504368
  simp only [CollatzResearch.WordTrace]
  refine ⟨45670902495554961423808879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60894536660739948565078505 45670902495554961423808879)
  ·
    refine ⟨68506353743332442135713319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45670902495554961423808879 68506353743332442135713319)
    ·
      refine ⟨102759530614998663203569979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68506353743332442135713319 102759530614998663203569979)
      ·
        refine ⟨154139295922497994805354969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102759530614998663203569979 154139295922497994805354969)
        ·
          refine ⟨115604471941873496104016227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154139295922497994805354969 115604471941873496104016227)
          ·
            refine ⟨173406707912810244156024341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115604471941873496104016227 173406707912810244156024341)
            ·
              refine ⟨8128439433412980194813641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173406707912810244156024341 8128439433412980194813641)
              ·
                refine ⟨6096329575059735146110231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8128439433412980194813641 6096329575059735146110231)
                ·
                  refine ⟨9144494362589602719165347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6096329575059735146110231 9144494362589602719165347)
                  ·
                    refine ⟨13716741543884404078748021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9144494362589602719165347 13716741543884404078748021)
                    ·
                      refine ⟨1285944519739162882382627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13716741543884404078748021 1285944519739162882382627)
                      ·
                        rfl

theorem cell23_2504368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_2504368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504368 prefixEnd_2504368 := by exact prefixLift 2504368
  have htrace : WordTrace (prefixWord ++ tailWord_2504368) baseStart_2504368 baseEnd_2504368 := by
    simpa [prefixWord, tailWord_2504368, baseEnd_2504368] using wordTrace_append hprefix tailTrace_2504368
  have hstable : (prefixWord ++ tailWord_2504368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504368).length < 2 ^ (prefixWord ++ tailWord_2504368).sum := by decide
  have hdescent : baseEnd_2504368 < baseStart_2504368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504378 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_2504378 : Nat := 118140960795 + 2504378 * 2 ^ 59
def prefixEnd_2504378 : Nat := 4983230072969 + 3 ^ 40 * 2504378 * 2
def baseEnd_2504378 : Nat := 1285949654545707843257581

theorem tailTrace_2504378 : CollatzResearch.WordTrace tailWord_2504378 prefixEnd_2504378 1285949654545707843257581 := by
  unfold tailWord_2504378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835542430268423638870447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60894779814049129703654525 22835542430268423638870447)
  ·
    refine ⟨34253313645402635458305671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22835542430268423638870447 34253313645402635458305671)
    ·
      refine ⟨51379970468103953187458507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253313645402635458305671 51379970468103953187458507)
      ·
        refine ⟨77069955702155929781187761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51379970468103953187458507 77069955702155929781187761)
        ·
          refine ⟨57802466776616947335890821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77069955702155929781187761 57802466776616947335890821)
          ·
            refine ⟨10837962520615677625479529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57802466776616947335890821 10837962520615677625479529)
            ·
              refine ⟨8128471890461758219109647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10837962520615677625479529 8128471890461758219109647)
              ·
                refine ⟨12192707835692637328664471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128471890461758219109647 12192707835692637328664471)
                ·
                  refine ⟨18289061753538955992996707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192707835692637328664471 18289061753538955992996707)
                  ·
                    refine ⟨27433592630308433989495061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18289061753538955992996707 27433592630308433989495061)
                    ·
                      refine ⟨1285949654545707843257581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27433592630308433989495061 1285949654545707843257581)
                      ·
                        rfl

theorem cell23_2504378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_2504378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504378 prefixEnd_2504378 := by exact prefixLift 2504378
  have htrace : WordTrace (prefixWord ++ tailWord_2504378) baseStart_2504378 baseEnd_2504378 := by
    simpa [prefixWord, tailWord_2504378, baseEnd_2504378] using wordTrace_append hprefix tailTrace_2504378
  have hstable : (prefixWord ++ tailWord_2504378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504378).length < 2 ^ (prefixWord ++ tailWord_2504378).sum := by decide
  have hdescent : baseEnd_2504378 < baseStart_2504378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504382 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2504382 : Nat := 118140960795 + 2504382 * 2 ^ 59
def prefixEnd_2504382 : Nat := 4983230072969 + 3 ^ 40 * 2504382 * 2
def baseEnd_2504382 : Nat := 1285951708468325827607563

theorem tailTrace_2504382 : CollatzResearch.WordTrace tailWord_2504382 prefixEnd_2504382 1285951708468325827607563 := by
  unfold tailWord_2504382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417789451632400404828425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60894877075372802159084933 11417789451632400404828425)
  ·
    refine ⟨8563342088724300303621319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11417789451632400404828425 8563342088724300303621319)
    ·
      refine ⟨12845013133086450455431979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8563342088724300303621319 12845013133086450455431979)
      ·
        refine ⟨19267519699629675683147969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12845013133086450455431979 19267519699629675683147969)
        ·
          refine ⟨14450639774722256762360977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19267519699629675683147969 14450639774722256762360977)
          ·
            refine ⟨10837979831041692571770733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14450639774722256762360977 10837979831041692571770733)
            ·
              refine ⟨4064242436640634714414025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10837979831041692571770733 4064242436640634714414025)
              ·
                refine ⟨3048181827480476035810519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064242436640634714414025 3048181827480476035810519)
                ·
                  refine ⟨4572272741220714053715779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048181827480476035810519 4572272741220714053715779)
                  ·
                    refine ⟨6858409111831071080573669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4572272741220714053715779 6858409111831071080573669)
                    ·
                      refine ⟨1285951708468325827607563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6858409111831071080573669 1285951708468325827607563)
                      ·
                        rfl

theorem cell23_2504382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2504382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504382 prefixEnd_2504382 := by exact prefixLift 2504382
  have htrace : WordTrace (prefixWord ++ tailWord_2504382) baseStart_2504382 baseEnd_2504382 := by
    simpa [prefixWord, tailWord_2504382, baseEnd_2504382] using wordTrace_append hprefix tailTrace_2504382
  have hstable : (prefixWord ++ tailWord_2504382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504382).length < 2 ^ (prefixWord ++ tailWord_2504382).sum := by decide
  have hdescent : baseEnd_2504382 < baseStart_2504382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504388 : List Nat := [2, 3, 3, 1, 1, 1, 1, 11]
def baseStart_2504388 : Nat := 118140960795 + 2504388 * 2 ^ 59
def prefixEnd_2504388 : Nat := 4983230072969 + 3 ^ 40 * 2504388 * 2
def baseEnd_2504388 : Nat := 47627955161194548301205

theorem tailTrace_2504388 : CollatzResearch.WordTrace tailWord_2504388 prefixEnd_2504388 47627955161194548301205 := by
  unfold tailWord_2504388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45671267225518733131672909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60895022967358310842230545 45671267225518733131672909)
  ·
    refine ⟨17126725209569524924377341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45671267225518733131672909 17126725209569524924377341)
    ·
      refine ⟨6422521953588571846641503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17126725209569524924377341 6422521953588571846641503)
      ·
        refine ⟨9633782930382857769962255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422521953588571846641503 9633782930382857769962255)
        ·
          refine ⟨14450674395574286654943383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633782930382857769962255 14450674395574286654943383)
          ·
            refine ⟨21676011593361429982415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14450674395574286654943383 21676011593361429982415075)
            ·
              refine ⟨32514017390042144973622613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21676011593361429982415075 32514017390042144973622613)
              ·
                refine ⟨47627955161194548301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32514017390042144973622613 47627955161194548301205)
                ·
                  rfl

theorem cell23_2504388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 11].length) (baseStart_2504388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504388 prefixEnd_2504388 := by exact prefixLift 2504388
  have htrace : WordTrace (prefixWord ++ tailWord_2504388) baseStart_2504388 baseEnd_2504388 := by
    simpa [prefixWord, tailWord_2504388, baseEnd_2504388] using wordTrace_append hprefix tailTrace_2504388
  have hstable : (prefixWord ++ tailWord_2504388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504388).length < 2 ^ (prefixWord ++ tailWord_2504388).sum := by decide
  have hdescent : baseEnd_2504388 < baseStart_2504388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504402 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2504402 : Nat := 118140960795 + 2504402 * 2 ^ 59
def prefixEnd_2504402 : Nat := 4983230072969 + 3 ^ 40 * 2504402 * 2
def baseEnd_2504402 : Nat := 1285961978081415749357471

theorem tailTrace_2504402 : CollatzResearch.WordTrace tailWord_2504402 prefixEnd_2504402 1285961978081415749357471 := by
  unfold tailWord_2504402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835761268246686663588865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60895363381991164436236973 22835761268246686663588865)
  ·
    refine ⟨17126820951185014997691649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22835761268246686663588865 17126820951185014997691649)
    ·
      refine ⟨12845115713388761248268737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17126820951185014997691649 12845115713388761248268737)
      ·
        refine ⟨9633836785041570936201553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12845115713388761248268737 9633836785041570936201553)
        ·
          refine ⟨7225377588781178202151165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9633836785041570936201553 7225377588781178202151165)
          ·
            refine ⟨2709516595792941825806687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7225377588781178202151165 2709516595792941825806687)
            ·
              refine ⟨4064274893689412738710031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709516595792941825806687 4064274893689412738710031)
              ·
                refine ⟨6096412340534119108065047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064274893689412738710031 6096412340534119108065047)
                ·
                  refine ⟨9144618510801178662097571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6096412340534119108065047 9144618510801178662097571)
                  ·
                    refine ⟨13716927766201767993146357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9144618510801178662097571 13716927766201767993146357)
                    ·
                      refine ⟨1285961978081415749357471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13716927766201767993146357 1285961978081415749357471)
                      ·
                        rfl

theorem cell23_2504402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2504402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504402 prefixEnd_2504402 := by exact prefixLift 2504402
  have htrace : WordTrace (prefixWord ++ tailWord_2504402) baseStart_2504402 baseEnd_2504402 := by
    simpa [prefixWord, tailWord_2504402, baseEnd_2504402] using wordTrace_append hprefix tailTrace_2504402
  have hstable : (prefixWord ++ tailWord_2504402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504402).length < 2 ^ (prefixWord ++ tailWord_2504402).sum := by decide
  have hdescent : baseEnd_2504402 < baseStart_2504402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504416 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 1, 2, 2]
def baseStart_2504416 : Nat := 118140960795 + 2504416 * 2 ^ 59
def prefixEnd_2504416 : Nat := 4983230072969 + 3 ^ 40 * 2504416 * 2
def baseEnd_2504416 : Nat := 1285969166810578694582407

theorem tailTrace_2504416 : CollatzResearch.WordTrace tailWord_2504416 prefixEnd_2504416 1285969166810578694582407 := by
  unfold tailWord_2504416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45671777847468013522682551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60895703796624018030243401 45671777847468013522682551)
  ·
    refine ⟨68507666771202020284023827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45671777847468013522682551 68507666771202020284023827)
    ·
      refine ⟨102761500156803030426035741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68507666771202020284023827 102761500156803030426035741)
      ·
        refine ⟨38535562558801136409763403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102761500156803030426035741 38535562558801136409763403)
        ·
          refine ⟨57803343838201704614645105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38535562558801136409763403 57803343838201704614645105)
          ·
            refine ⟨43352507878651278460983829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57803343838201704614645105 43352507878651278460983829)
            ·
              refine ⟨2032148806811778677858617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43352507878651278460983829 2032148806811778677858617)
              ·
                refine ⟨1524111605108834008393963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032148806811778677858617 1524111605108834008393963)
                ·
                  refine ⟨2286167407663251012590945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524111605108834008393963 2286167407663251012590945)
                  ·
                    refine ⟨1714625555747438259443209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2286167407663251012590945 1714625555747438259443209)
                    ·
                      refine ⟨1285969166810578694582407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714625555747438259443209 1285969166810578694582407)
                      ·
                        rfl

theorem cell23_2504416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_2504416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504416 prefixEnd_2504416 := by exact prefixLift 2504416
  have htrace : WordTrace (prefixWord ++ tailWord_2504416) baseStart_2504416 baseEnd_2504416 := by
    simpa [prefixWord, tailWord_2504416, baseEnd_2504416] using wordTrace_append hprefix tailTrace_2504416
  have hstable : (prefixWord ++ tailWord_2504416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504416).length < 2 ^ (prefixWord ++ tailWord_2504416).sum := by decide
  have hdescent : baseEnd_2504416 < baseStart_2504416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504442 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_2504442 : Nat := 118140960795 + 2504442 * 2 ^ 59
def prefixEnd_2504442 : Nat := 4983230072969 + 3 ^ 40 * 2504442 * 2
def baseEnd_2504442 : Nat := 1285982517307595592857287

theorem tailTrace_2504442 : CollatzResearch.WordTrace tailWord_2504442 prefixEnd_2504442 1285982517307595592857287 := by
  unfold tailWord_2504442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22836125998210458371452895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60896335995227888990541053 22836125998210458371452895)
  ·
    refine ⟨34254188997315687557179343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22836125998210458371452895 34254188997315687557179343)
    ·
      refine ⟨51381283495973531335769015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34254188997315687557179343 51381283495973531335769015)
      ·
        refine ⟨77071925243960297003653523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51381283495973531335769015 77071925243960297003653523)
        ·
          refine ⟨115607887865940445505480285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77071925243960297003653523 115607887865940445505480285)
          ·
            refine ⟨43352957949727667064555107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115607887865940445505480285 43352957949727667064555107)
            ·
              refine ⟨65029436924591500596832661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43352957949727667064555107 65029436924591500596832661)
              ·
                refine ⟨3048254855840226590476531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65029436924591500596832661 3048254855840226590476531)
                ·
                  refine ⟨4572382283760339885714797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048254855840226590476531 4572382283760339885714797)
                  ·
                    refine ⟨1714643356410127457143049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4572382283760339885714797 1714643356410127457143049)
                    ·
                      refine ⟨1285982517307595592857287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714643356410127457143049 1285982517307595592857287)
                      ·
                        rfl

theorem cell23_2504442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_2504442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504442 prefixEnd_2504442 := by exact prefixLift 2504442
  have htrace : WordTrace (prefixWord ++ tailWord_2504442) baseStart_2504442 baseEnd_2504442 := by
    simpa [prefixWord, tailWord_2504442, baseEnd_2504442] using wordTrace_append hprefix tailTrace_2504442
  have hstable : (prefixWord ++ tailWord_2504442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504442).length < 2 ^ (prefixWord ++ tailWord_2504442).sum := by decide
  have hdescent : baseEnd_2504442 < baseStart_2504442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504459 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 1, 3, 2]
def baseStart_2504459 : Nat := 118140960795 + 2504459 * 2 ^ 59
def prefixEnd_2504459 : Nat := 4983230072969 + 3 ^ 40 * 2504459 * 2
def baseEnd_2504459 : Nat := 1285991246478722026344709

theorem tailTrace_2504459 : CollatzResearch.WordTrace tailWord_2504459 prefixEnd_2504459 1285991246478722026344709 := by
  unfold tailWord_2504459
  simp only [CollatzResearch.WordTrace]
  refine ⟨91345124033780245389180431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60896749355853496926120287 91345124033780245389180431)
  ·
    refine ⟨137017686050670368083770647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91345124033780245389180431 137017686050670368083770647)
    ·
      refine ⟨205526529076005552125655971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137017686050670368083770647 205526529076005552125655971)
      ·
        refine ⟨308289793614008328188483957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205526529076005552125655971 308289793614008328188483957)
        ·
          refine ⟨28902168151313280767670371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308289793614008328188483957 28902168151313280767670371)
          ·
            refine ⟨43353252226969921151505557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28902168151313280767670371 43353252226969921151505557)
            ·
              refine ⟨2032183698139215053976823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43353252226969921151505557 2032183698139215053976823)
              ·
                refine ⟨3048275547208822580965235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032183698139215053976823 3048275547208822580965235)
                ·
                  refine ⟨4572413320813233871447853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048275547208822580965235 4572413320813233871447853)
                  ·
                    refine ⟨1714654995304962701792945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4572413320813233871447853 1714654995304962701792945)
                    ·
                      refine ⟨1285991246478722026344709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714654995304962701792945 1285991246478722026344709)
                      ·
                        rfl

theorem cell23_2504459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 3, 2].length) (baseStart_2504459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504459 prefixEnd_2504459 := by exact prefixLift 2504459
  have htrace : WordTrace (prefixWord ++ tailWord_2504459) baseStart_2504459 baseEnd_2504459 := by
    simpa [prefixWord, tailWord_2504459, baseEnd_2504459] using wordTrace_append hprefix tailTrace_2504459
  have hstable : (prefixWord ++ tailWord_2504459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504459).length < 2 ^ (prefixWord ++ tailWord_2504459).sum := by decide
  have hdescent : baseEnd_2504459 < baseStart_2504459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504466 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2504466 : Nat := 118140960795 + 2504466 * 2 ^ 59
def prefixEnd_2504466 : Nat := 4983230072969 + 3 ^ 40 * 2504466 * 2
def baseEnd_2504466 : Nat := 1285994840843303498957177

theorem tailTrace_2504466 : CollatzResearch.WordTrace tailWord_2504466 prefixEnd_2504466 1285994840843303498957177 := by
  unfold tailWord_2504466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22836344836188721396171313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60896919563169923723123501 22836344836188721396171313)
  ·
    refine ⟨17127258627141541047128485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22836344836188721396171313 17127258627141541047128485)
    ·
      refine ⟨3211360992589038946336591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17127258627141541047128485 3211360992589038946336591)
      ·
        refine ⟨4817041488883558419504887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211360992589038946336591 4817041488883558419504887)
        ·
          refine ⟨7225562233325337629257331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817041488883558419504887 7225562233325337629257331)
          ·
            refine ⟨10838343349988006443885997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225562233325337629257331 10838343349988006443885997)
            ·
              refine ⟨4064378756245502416457249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10838343349988006443885997 4064378756245502416457249)
              ·
                refine ⟨3048284067184126812342937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064378756245502416457249 3048284067184126812342937)
                ·
                  refine ⟨2286213050388095109257203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3048284067184126812342937 2286213050388095109257203)
                  ·
                    refine ⟨3429319575582142663885805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2286213050388095109257203 3429319575582142663885805)
                    ·
                      refine ⟨1285994840843303498957177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3429319575582142663885805 1285994840843303498957177)
                      ·
                        rfl

theorem cell23_2504466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2504466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504466 prefixEnd_2504466 := by exact prefixLift 2504466
  have htrace : WordTrace (prefixWord ++ tailWord_2504466) baseStart_2504466 baseEnd_2504466 := by
    simpa [prefixWord, tailWord_2504466, baseEnd_2504466] using wordTrace_append hprefix tailTrace_2504466
  have hstable : (prefixWord ++ tailWord_2504466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504466).length < 2 ^ (prefixWord ++ tailWord_2504466).sum := by decide
  have hdescent : baseEnd_2504466 < baseStart_2504466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504485 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2504485 : Nat := 118140960795 + 2504485 * 2 ^ 59
def prefixEnd_2504485 : Nat := 4983230072969 + 3 ^ 40 * 2504485 * 2
def baseEnd_2504485 : Nat := 1286004596975738924619589

theorem tailTrace_2504485 : CollatzResearch.WordTrace tailWord_2504485 prefixEnd_2504485 1286004596975738924619589 := by
  unfold tailWord_2504485
  simp only [CollatzResearch.WordTrace]
  refine ⟨91346072331686051829626909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60897381554457367886417939 91346072331686051829626909)
  ·
    refine ⟨34254777124382269436110091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91346072331686051829626909 34254777124382269436110091)
    ·
      refine ⟨51382165686573404154165137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34254777124382269436110091 51382165686573404154165137)
      ·
        refine ⟨38536624264930053115623853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51382165686573404154165137 38536624264930053115623853)
        ·
          refine ⟨14451234099348769918358945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38536624264930053115623853 14451234099348769918358945)
          ·
            refine ⟨10838425574511577438769209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14451234099348769918358945 10838425574511577438769209)
            ·
              refine ⟨8128819180883683079076907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10838425574511577438769209 8128819180883683079076907)
              ·
                refine ⟨12193228771325524618615361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128819180883683079076907 12193228771325524618615361)
                ·
                  refine ⟨9144921578494143463961521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12193228771325524618615361 9144921578494143463961521)
                  ·
                    refine ⟨6858691183870607597971141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9144921578494143463961521 6858691183870607597971141)
                    ·
                      refine ⟨1286004596975738924619589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6858691183870607597971141 1286004596975738924619589)
                      ·
                        rfl

theorem cell23_2504485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2504485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504485 prefixEnd_2504485 := by exact prefixLift 2504485
  have htrace : WordTrace (prefixWord ++ tailWord_2504485) baseStart_2504485 baseEnd_2504485 := by
    simpa [prefixWord, tailWord_2504485, baseEnd_2504485] using wordTrace_append hprefix tailTrace_2504485
  have hstable : (prefixWord ++ tailWord_2504485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504485).length < 2 ^ (prefixWord ++ tailWord_2504485).sum := by decide
  have hdescent : baseEnd_2504485 < baseStart_2504485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504529 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 5]
def baseStart_2504529 : Nat := 118140960795 + 2504529 * 2 ^ 59
def prefixEnd_2504529 : Nat := 4983230072969 + 3 ^ 40 * 2504529 * 2
def baseEnd_2504529 : Nat := 142891910013837416941043

theorem tailTrace_2504529 : CollatzResearch.WordTrace tailWord_2504529 prefixEnd_2504529 142891910013837416941043 := by
  unfold tailWord_2504529
  simp only [CollatzResearch.WordTrace]
  refine ⟨91347677143526647344228641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60898451429017764896152427 91347677143526647344228641)
  ·
    refine ⟨68510757857644985508171481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91347677143526647344228641 68510757857644985508171481)
    ·
      refine ⟨51383068393233739131128611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68510757857644985508171481 51383068393233739131128611)
      ·
        refine ⟨77074602589850608696692917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51383068393233739131128611 77074602589850608696692917)
        ·
          refine ⟨7225743992798494565314961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77074602589850608696692917 7225743992798494565314961)
          ·
            refine ⟨5419307994598870923986221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7225743992798494565314961 5419307994598870923986221)
            ·
              refine ⟨2032240497974576596494833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5419307994598870923986221 2032240497974576596494833)
              ·
                refine ⟨1524180373480932447371125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032240497974576596494833 1524180373480932447371125)
                ·
                  refine ⟨142891910013837416941043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524180373480932447371125 142891910013837416941043)
                  ·
                    rfl

theorem cell23_2504529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 5].length) (baseStart_2504529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504529 prefixEnd_2504529 := by exact prefixLift 2504529
  have htrace : WordTrace (prefixWord ++ tailWord_2504529) baseStart_2504529 baseEnd_2504529 := by
    simpa [prefixWord, tailWord_2504529, baseEnd_2504529] using wordTrace_append hprefix tailTrace_2504529
  have hstable : (prefixWord ++ tailWord_2504529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504529).length < 2 ^ (prefixWord ++ tailWord_2504529).sum := by decide
  have hdescent : baseEnd_2504529 < baseStart_2504529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504540 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2504540 : Nat := 118140960795 + 2504540 * 2 ^ 59
def prefixEnd_2504540 : Nat := 4983230072969 + 3 ^ 40 * 2504540 * 2
def baseEnd_2504540 : Nat := 1286032838411736209431837

theorem tailTrace_2504540 : CollatzResearch.WordTrace tailWord_2504540 prefixEnd_2504540 1286032838411736209431837 := by
  unfold tailWord_2504540
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674039173243398111439537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60898718897657864148586049 45674039173243398111439537)
  ·
    refine ⟨34255529379932548583579653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45674039173243398111439537 34255529379932548583579653)
    ·
      refine ⟨6422911758737352859421185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34255529379932548583579653 6422911758737352859421185)
      ·
        refine ⟨4817183819053014644565889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6422911758737352859421185 4817183819053014644565889)
        ·
          refine ⟨3612887864289760983424417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4817183819053014644565889 3612887864289760983424417)
          ·
            refine ⟨2709665898217320737568313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3612887864289760983424417 2709665898217320737568313)
            ·
              refine ⟨2032249423662990553176235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709665898217320737568313 2032249423662990553176235)
              ·
                refine ⟨3048374135494485829764353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032249423662990553176235 3048374135494485829764353)
                ·
                  refine ⟨2286280601620864372323265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3048374135494485829764353 2286280601620864372323265)
                  ·
                    refine ⟨1714710451215648279242449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2286280601620864372323265 1714710451215648279242449)
                    ·
                      refine ⟨1286032838411736209431837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714710451215648279242449 1286032838411736209431837)
                      ·
                        rfl

theorem cell23_2504540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2504540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504540 prefixEnd_2504540 := by exact prefixLift 2504540
  have htrace : WordTrace (prefixWord ++ tailWord_2504540) baseStart_2504540 baseEnd_2504540 := by
    simpa [prefixWord, tailWord_2504540, baseEnd_2504540] using wordTrace_append hprefix tailTrace_2504540
  have hstable : (prefixWord ++ tailWord_2504540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504540).length < 2 ^ (prefixWord ++ tailWord_2504540).sum := by decide
  have hdescent : baseEnd_2504540 < baseStart_2504540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504545 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2504545 : Nat := 118140960795 + 2504545 * 2 ^ 59
def prefixEnd_2504545 : Nat := 4983230072969 + 3 ^ 40 * 2504545 * 2
def baseEnd_2504545 : Nat := 1286035405815008689869313

theorem tailTrace_2504545 : CollatzResearch.WordTrace tailWord_2504545 prefixEnd_2504545 1286035405815008689869313 := by
  unfold tailWord_2504545
  simp only [CollatzResearch.WordTrace]
  refine ⟨91348260711468682076811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60898840474312454717874059 91348260711468682076811089)
  ·
    refine ⟨68511195533601511557608317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91348260711468682076811089 68511195533601511557608317)
    ·
      refine ⟨25691698325100566834103119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68511195533601511557608317 25691698325100566834103119)
      ·
        refine ⟨38537547487650850251154679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25691698325100566834103119 38537547487650850251154679)
        ·
          refine ⟨57806321231476275376732019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38537547487650850251154679 57806321231476275376732019)
          ·
            refine ⟨86709481847214413065098029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57806321231476275376732019 86709481847214413065098029)
            ·
              refine ⟨32516055692705404899411761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86709481847214413065098029 32516055692705404899411761)
              ·
                refine ⟨24387041769529053674558821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32516055692705404899411761 24387041769529053674558821)
                ·
                  refine ⟨4572570331786697563979779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24387041769529053674558821 4572570331786697563979779)
                  ·
                    refine ⟨6858855497680046345969669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4572570331786697563979779 6858855497680046345969669)
                    ·
                      refine ⟨1286035405815008689869313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6858855497680046345969669 1286035405815008689869313)
                      ·
                        rfl

theorem cell23_2504545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2504545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504545 prefixEnd_2504545 := by exact prefixLift 2504545
  have htrace : WordTrace (prefixWord ++ tailWord_2504545) baseStart_2504545 baseEnd_2504545 := by
    simpa [prefixWord, tailWord_2504545, baseEnd_2504545] using wordTrace_append hprefix tailTrace_2504545
  have hstable : (prefixWord ++ tailWord_2504545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504545).length < 2 ^ (prefixWord ++ tailWord_2504545).sum := by decide
  have hdescent : baseEnd_2504545 < baseStart_2504545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504555 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 5, 4]
def baseStart_2504555 : Nat := 118140960795 + 2504555 * 2 ^ 59
def prefixEnd_2504555 : Nat := 4983230072969 + 3 ^ 40 * 2504555 * 2
def baseEnd_2504555 : Nat := 428680180207184550248089

theorem tailTrace_2504555 : CollatzResearch.WordTrace tailWord_2504555 prefixEnd_2504555 428680180207184550248089 := by
  unfold tailWord_2504555
  simp only [CollatzResearch.WordTrace]
  refine ⟨91348625441432453784675119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60899083627621635856450079 91348625441432453784675119)
  ·
    refine ⟨137022938162148680677012679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91348625441432453784675119 137022938162148680677012679)
    ·
      refine ⟨205534407243223021015519019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137022938162148680677012679 205534407243223021015519019)
      ·
        refine ⟨308301610864834531523278529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205534407243223021015519019 308301610864834531523278529)
        ·
          refine ⟨231226208148625898642458897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308301610864834531523278529 231226208148625898642458897)
          ·
            refine ⟨173419656111469423981844173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231226208148625898642458897 173419656111469423981844173)
            ·
              refine ⟨65032371041801033993191565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173419656111469423981844173 65032371041801033993191565)
              ·
                refine ⟨24387139140675387747446837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65032371041801033993191565 24387139140675387747446837)
                ·
                  refine ⟨2286294294438317601323141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24387139140675387747446837 2286294294438317601323141)
                  ·
                    refine ⟨428680180207184550248089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286294294438317601323141 428680180207184550248089)
                    ·
                      rfl

theorem cell23_2504555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 4].length) (baseStart_2504555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504555 prefixEnd_2504555 := by exact prefixLift 2504555
  have htrace : WordTrace (prefixWord ++ tailWord_2504555) baseStart_2504555 baseEnd_2504555 := by
    simpa [prefixWord, tailWord_2504555, baseEnd_2504555] using wordTrace_append hprefix tailTrace_2504555
  have hstable : (prefixWord ++ tailWord_2504555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504555).length < 2 ^ (prefixWord ++ tailWord_2504555).sum := by decide
  have hdescent : baseEnd_2504555 < baseStart_2504555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_2504562 : Nat := 118140960795 + 2504562 * 2 ^ 59
def prefixEnd_2504562 : Nat := 4983230072969 + 3 ^ 40 * 2504562 * 2
def baseEnd_2504562 : Nat := 1286044134986135123356735

theorem tailTrace_2504562 : CollatzResearch.WordTrace tailWord_2504562 prefixEnd_2504562 1286044134986135123356735 := by
  unfold tailWord_2504562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837220188101773495044985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60899253834938062653453293 22837220188101773495044985)
  ·
    refine ⟨17127915141076330121283739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22837220188101773495044985 17127915141076330121283739)
    ·
      refine ⟨25691872711614495181925609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17127915141076330121283739 25691872711614495181925609)
      ·
        refine ⟨19268904533710871386444207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25691872711614495181925609 19268904533710871386444207)
        ·
          refine ⟨28903356800566307079666311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19268904533710871386444207 28903356800566307079666311)
          ·
            refine ⟨43355035200849460619499467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28903356800566307079666311 43355035200849460619499467)
            ·
              refine ⟨65032552801274190929249201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43355035200849460619499467 65032552801274190929249201)
              ·
                refine ⟨48774414600955643196936901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65032552801274190929249201 48774414600955643196936901)
                ·
                  refine ⟨9145202737679183099425669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48774414600955643196936901 9145202737679183099425669)
                  ·
                    refine ⟨1714725513314846831142313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9145202737679183099425669 1714725513314846831142313)
                    ·
                      refine ⟨1286044134986135123356735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714725513314846831142313 1286044134986135123356735)
                      ·
                        rfl

theorem cell23_2504562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_2504562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504562 prefixEnd_2504562 := by exact prefixLift 2504562
  have htrace : WordTrace (prefixWord ++ tailWord_2504562) baseStart_2504562 baseEnd_2504562 := by
    simpa [prefixWord, tailWord_2504562, baseEnd_2504562] using wordTrace_append hprefix tailTrace_2504562
  have hstable : (prefixWord ++ tailWord_2504562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504562).length < 2 ^ (prefixWord ++ tailWord_2504562).sum := by decide
  have hdescent : baseEnd_2504562 < baseStart_2504562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504602 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_2504602 : Nat := 118140960795 + 2504602 * 2 ^ 59
def prefixEnd_2504602 : Nat := 4983230072969 + 3 ^ 40 * 2504602 * 2
def baseEnd_2504602 : Nat := 142896074912479440761839

theorem tailTrace_2504602 : CollatzResearch.WordTrace tailWord_2504602 prefixEnd_2504602 142896074912479440761839 := by
  unfold tailWord_2504602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837584918065545202909015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60900226448174787207757373 22837584918065545202909015)
  ·
    refine ⟨34256377377098317804363523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837584918065545202909015 34256377377098317804363523)
    ·
      refine ⟨51384566065647476706545285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34256377377098317804363523 51384566065647476706545285)
      ·
        refine ⟨9634606137308901882477241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51384566065647476706545285 9634606137308901882477241)
        ·
          refine ⟨7225954602981676411857931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634606137308901882477241 7225954602981676411857931)
          ·
            refine ⟨10838931904472514617786897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225954602981676411857931 10838931904472514617786897)
            ·
              refine ⟨8129198928354385963340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10838931904472514617786897 8129198928354385963340173)
              ·
                refine ⟨3048449598132894736252565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8129198928354385963340173 3048449598132894736252565)
                ·
                  refine ⟨142896074912479440761839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048449598132894736252565 142896074912479440761839)
                  ·
                    rfl

theorem cell23_2504602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_2504602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504602 prefixEnd_2504602 := by exact prefixLift 2504602
  have htrace : WordTrace (prefixWord ++ tailWord_2504602) baseStart_2504602 baseEnd_2504602 := by
    simpa [prefixWord, tailWord_2504602, baseEnd_2504602] using wordTrace_append hprefix tailTrace_2504602
  have hstable : (prefixWord ++ tailWord_2504602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504602).length < 2 ^ (prefixWord ++ tailWord_2504602).sum := by decide
  have hdescent : baseEnd_2504602 < baseStart_2504602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504616 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2504616 : Nat := 118140960795 + 2504616 * 2 ^ 59
def prefixEnd_2504616 : Nat := 4983230072969 + 3 ^ 40 * 2504616 * 2
def baseEnd_2504616 : Nat := 1286071862941477912081487

theorem tailTrace_2504616 : CollatzResearch.WordTrace tailWord_2504616 prefixEnd_2504616 1286071862941477912081487 := by
  unfold tailWord_2504616
  simp only [CollatzResearch.WordTrace]
  refine ⟨45675425147105730601322851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60900566862807640801763801 45675425147105730601322851)
  ·
    refine ⟨68513137720658595901984277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45675425147105730601322851 68513137720658595901984277)
    ·
      refine ⟨3211553330655871682905513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68513137720658595901984277 3211553330655871682905513)
      ·
        refine ⟨2408664997991903762179135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3211553330655871682905513 2408664997991903762179135)
        ·
          refine ⟨3612997496987855643268703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408664997991903762179135 3612997496987855643268703)
          ·
            refine ⟨5419496245481783464903055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612997496987855643268703 5419496245481783464903055)
            ·
              refine ⟨8129244368222675197354583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419496245481783464903055 8129244368222675197354583)
              ·
                refine ⟨12193866552334012796031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129244368222675197354583 12193866552334012796031875)
                ·
                  refine ⟨18290799828501019194047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12193866552334012796031875 18290799828501019194047813)
                  ·
                    refine ⟨3429524967843941098883965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18290799828501019194047813 3429524967843941098883965)
                    ·
                      refine ⟨1286071862941477912081487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3429524967843941098883965 1286071862941477912081487)
                      ·
                        rfl

theorem cell23_2504616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2504616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504616 prefixEnd_2504616 := by exact prefixLift 2504616
  have htrace : WordTrace (prefixWord ++ tailWord_2504616) baseStart_2504616 baseEnd_2504616 := by
    simpa [prefixWord, tailWord_2504616, baseEnd_2504616] using wordTrace_append hprefix tailTrace_2504616
  have hstable : (prefixWord ++ tailWord_2504616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504616).length < 2 ^ (prefixWord ++ tailWord_2504616).sum := by decide
  have hdescent : baseEnd_2504616 < baseStart_2504616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504632 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_2504632 : Nat := 118140960795 + 2504632 * 2 ^ 59
def prefixEnd_2504632 : Nat := 4983230072969 + 3 ^ 40 * 2504632 * 2
def baseEnd_2504632 : Nat := 428693359543983283160471

theorem tailTrace_2504632 : CollatzResearch.WordTrace tailWord_2504632 prefixEnd_2504632 428693359543983283160471 := by
  unfold tailWord_2504632
  simp only [CollatzResearch.WordTrace]
  refine ⟨45675716931076747967614075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60900955908102330623485433 45675716931076747967614075)
  ·
    refine ⟨68513575396615121951421113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45675716931076747967614075 68513575396615121951421113)
    ·
      refine ⟨51385181547461341463565835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68513575396615121951421113 51385181547461341463565835)
      ·
        refine ⟨77077772321192012195348753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51385181547461341463565835 77077772321192012195348753)
        ·
          refine ⟨57808329240894009146511565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77077772321192012195348753 57808329240894009146511565)
          ·
            refine ⟨21678123465335253429941837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57808329240894009146511565 21678123465335253429941837)
            ·
              refine ⟨8129296299500720036228189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21678123465335253429941837 8129296299500720036228189)
              ·
                refine ⟨3048486112312770013585571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8129296299500720036228189 3048486112312770013585571)
                ·
                  refine ⟨4572729168469155020378357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048486112312770013585571 4572729168469155020378357)
                  ·
                    refine ⟨428693359543983283160471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4572729168469155020378357 428693359543983283160471)
                    ·
                      rfl

theorem cell23_2504632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_2504632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504632 prefixEnd_2504632 := by exact prefixLift 2504632
  have htrace : WordTrace (prefixWord ++ tailWord_2504632) baseStart_2504632 baseEnd_2504632 := by
    simpa [prefixWord, tailWord_2504632, baseEnd_2504632] using wordTrace_append hprefix tailTrace_2504632
  have hstable : (prefixWord ++ tailWord_2504632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504632).length < 2 ^ (prefixWord ++ tailWord_2504632).sum := by decide
  have hdescent : baseEnd_2504632 < baseStart_2504632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504636 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 6]
def baseStart_2504636 : Nat := 118140960795 + 2504636 * 2 ^ 59
def prefixEnd_2504636 : Nat := 4983230072969 + 3 ^ 40 * 2504636 * 2
def baseEnd_2504636 : Nat := 142898014728285314870155

theorem tailTrace_2504636 : CollatzResearch.WordTrace tailWord_2504636 prefixEnd_2504636 142898014728285314870155 := by
  unfold tailWord_2504636
  simp only [CollatzResearch.WordTrace]
  refine ⟨45675789877069502309186881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60901053169426003078915841 45675789877069502309186881)
  ·
    refine ⟨34256842407802126731890161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45675789877069502309186881 34256842407802126731890161)
    ·
      refine ⟨25692631805851595048917621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34256842407802126731890161 25692631805851595048917621)
      ·
        refine ⟨2408684231798587035836027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25692631805851595048917621 2408684231798587035836027)
        ·
          refine ⟨3613026347697880553754041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408684231798587035836027 3613026347697880553754041)
          ·
            refine ⟨2709769760773410415315531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3613026347697880553754041 2709769760773410415315531)
            ·
              refine ⟨4064654641160115622973297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709769760773410415315531 4064654641160115622973297)
              ·
                refine ⟨3048490980870086717229973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064654641160115622973297 3048490980870086717229973)
                ·
                  refine ⟨142898014728285314870155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048490980870086717229973 142898014728285314870155)
                  ·
                    rfl

theorem cell23_2504636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_2504636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504636 prefixEnd_2504636 := by exact prefixLift 2504636
  have htrace : WordTrace (prefixWord ++ tailWord_2504636) baseStart_2504636 baseEnd_2504636 := by
    simpa [prefixWord, tailWord_2504636, baseEnd_2504636] using wordTrace_append hprefix tailTrace_2504636
  have hstable : (prefixWord ++ tailWord_2504636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504636).length < 2 ^ (prefixWord ++ tailWord_2504636).sum := by decide
  have hdescent : baseEnd_2504636 < baseStart_2504636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504672 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_2504672 : Nat := 118140960795 + 2504672 * 2 ^ 59
def prefixEnd_2504672 : Nat := 4983230072969 + 3 ^ 40 * 2504672 * 2
def baseEnd_2504672 : Nat := 1286100617858129692981229

theorem tailTrace_2504672 : CollatzResearch.WordTrace tailWord_2504672 prefixEnd_2504672 1286100617858129692981229 := by
  unfold tailWord_2504672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45676446391004291383342135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60901928521339055177789513 45676446391004291383342135)
  ·
    refine ⟨68514669586506437075013203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45676446391004291383342135 68514669586506437075013203)
    ·
      refine ⟨102772004379759655612519805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68514669586506437075013203 102772004379759655612519805)
      ·
        refine ⟨38539501642409870854694927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102772004379759655612519805 38539501642409870854694927)
        ·
          refine ⟨57809252463614806282042391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38539501642409870854694927 57809252463614806282042391)
          ·
            refine ⟨86713878695422209423063587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57809252463614806282042391 86713878695422209423063587)
            ·
              refine ⟨130070818043133314134595381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86713878695422209423063587 130070818043133314134595381)
              ·
                refine ⟨12194139191543748200118317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130070818043133314134595381 12194139191543748200118317)
                ·
                  refine ⟨4572802196828905575044369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12194139191543748200118317 4572802196828905575044369)
                  ·
                    refine ⟨3429601647621679181283277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4572802196828905575044369 3429601647621679181283277)
                    ·
                      refine ⟨1286100617858129692981229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3429601647621679181283277 1286100617858129692981229)
                      ·
                        rfl

theorem cell23_2504672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_2504672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504672 prefixEnd_2504672 := by exact prefixLift 2504672
  have htrace : WordTrace (prefixWord ++ tailWord_2504672) baseStart_2504672 baseEnd_2504672 := by
    simpa [prefixWord, tailWord_2504672, baseEnd_2504672] using wordTrace_append hprefix tailTrace_2504672
  have hstable : (prefixWord ++ tailWord_2504672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504672).length < 2 ^ (prefixWord ++ tailWord_2504672).sum := by decide
  have hdescent : baseEnd_2504672 < baseStart_2504672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504682 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2504682 : Nat := 118140960795 + 2504682 * 2 ^ 59
def prefixEnd_2504682 : Nat := 4983230072969 + 3 ^ 40 * 2504682 * 2
def baseEnd_2504682 : Nat := 1286105752664674653856183

theorem tailTrace_2504682 : CollatzResearch.WordTrace tailWord_2504682 prefixEnd_2504682 1286105752664674653856183 := by
  unfold tailWord_2504682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22838314377993088618637075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60902171674648236316365533 22838314377993088618637075)
  ·
    refine ⟨34257471566989632927955613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22838314377993088618637075 34257471566989632927955613)
    ·
      refine ⟨12846551837621112347983355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34257471566989632927955613 12846551837621112347983355)
      ·
        refine ⟨19269827756431668521975033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12846551837621112347983355 19269827756431668521975033)
        ·
          refine ⟨14452370817323751391481275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19269827756431668521975033 14452370817323751391481275)
          ·
            refine ⟨21678556225985627087221913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14452370817323751391481275 21678556225985627087221913)
            ·
              refine ⟨16258917169489220315416435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21678556225985627087221913 16258917169489220315416435)
              ·
                refine ⟨24388375754233830473124653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16258917169489220315416435 24388375754233830473124653)
                ·
                  refine ⟨9145640907837686427421745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24388375754233830473124653 9145640907837686427421745)
                  ·
                    refine ⟨6859230680878264820566309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9145640907837686427421745 6859230680878264820566309)
                    ·
                      refine ⟨1286105752664674653856183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6859230680878264820566309 1286105752664674653856183)
                      ·
                        rfl

theorem cell23_2504682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2504682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504682 prefixEnd_2504682 := by exact prefixLift 2504682
  have htrace : WordTrace (prefixWord ++ tailWord_2504682) baseStart_2504682 baseEnd_2504682 := by
    simpa [prefixWord, tailWord_2504682, baseEnd_2504682] using wordTrace_append hprefix tailTrace_2504682
  have hstable : (prefixWord ++ tailWord_2504682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504682).length < 2 ^ (prefixWord ++ tailWord_2504682).sum := by decide
  have hdescent : baseEnd_2504682 < baseStart_2504682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504689 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_2504689 : Nat := 118140960795 + 2504689 * 2 ^ 59
def prefixEnd_2504689 : Nat := 4983230072969 + 3 ^ 40 * 2504689 * 2
def baseEnd_2504689 : Nat := 1286109347029256126468651

theorem tailTrace_2504689 : CollatzResearch.WordTrace tailWord_2504689 prefixEnd_2504689 1286109347029256126468651 := by
  unfold tailWord_2504689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91353512822946994670053121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60902341881964663113368747 91353512822946994670053121)
  ·
    refine ⟨68515134617210246002539841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91353512822946994670053121 68515134617210246002539841)
    ·
      refine ⟨51386350962907684501904881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68515134617210246002539841 51386350962907684501904881)
      ·
        refine ⟨38539763222180763376428661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51386350962907684501904881 38539763222180763376428661)
        ·
          refine ⟨3613102802079446566540187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38539763222180763376428661 3613102802079446566540187)
          ·
            refine ⟨5419654203119169849810281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613102802079446566540187 5419654203119169849810281)
            ·
              refine ⟨4064740652339377387357711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419654203119169849810281 4064740652339377387357711)
              ·
                refine ⟨6097110978509066081036567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064740652339377387357711 6097110978509066081036567)
                ·
                  refine ⟨9145666467763599121554851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097110978509066081036567 9145666467763599121554851)
                  ·
                    refine ⟨13718499701645398682332277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9145666467763599121554851 13718499701645398682332277)
                    ·
                      refine ⟨1286109347029256126468651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13718499701645398682332277 1286109347029256126468651)
                      ·
                        rfl

theorem cell23_2504689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_2504689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504689 prefixEnd_2504689 := by exact prefixLift 2504689
  have htrace : WordTrace (prefixWord ++ tailWord_2504689) baseStart_2504689 baseEnd_2504689 := by
    simpa [prefixWord, tailWord_2504689, baseEnd_2504689] using wordTrace_append hprefix tailTrace_2504689
  have hstable : (prefixWord ++ tailWord_2504689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504689).length < 2 ^ (prefixWord ++ tailWord_2504689).sum := by decide
  have hdescent : baseEnd_2504689 < baseStart_2504689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504717 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2504717 : Nat := 118140960795 + 2504717 * 2 ^ 59
def prefixEnd_2504717 : Nat := 4983230072969 + 3 ^ 40 * 2504717 * 2
def baseEnd_2504717 : Nat := 428707908162527338972841

theorem tailTrace_2504717 : CollatzResearch.WordTrace tailWord_2504717 prefixEnd_2504717 428707908162527338972841 := by
  unfold tailWord_2504717
  simp only [CollatzResearch.WordTrace]
  refine ⟨91354534066845555452072405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60903022711230370301381603 91354534066845555452072405)
  ·
    refine ⟨2141121892191692705907947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91354534066845555452072405 2141121892191692705907947)
    ·
      refine ⟨3211682838287539058861921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141121892191692705907947 3211682838287539058861921)
      ·
        refine ⟨2408762128715654294146441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3211682838287539058861921 2408762128715654294146441)
        ·
          refine ⟨1806571596536740720609831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408762128715654294146441 1806571596536740720609831)
          ·
            refine ⟨2709857394805111080914747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806571596536740720609831 2709857394805111080914747)
            ·
              refine ⟨4064786092207666621372121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709857394805111080914747 4064786092207666621372121)
              ·
                refine ⟨3048589569155749966029091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064786092207666621372121 3048589569155749966029091)
                ·
                  refine ⟨4572884353733624949043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048589569155749966029091 4572884353733624949043637)
                  ·
                    refine ⟨428707908162527338972841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4572884353733624949043637 428707908162527338972841)
                    ·
                      rfl

theorem cell23_2504717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2504717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504717 prefixEnd_2504717 := by exact prefixLift 2504717
  have htrace : WordTrace (prefixWord ++ tailWord_2504717) baseStart_2504717 baseEnd_2504717 := by
    simpa [prefixWord, tailWord_2504717, baseEnd_2504717] using wordTrace_append hprefix tailTrace_2504717
  have hstable : (prefixWord ++ tailWord_2504717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504717).length < 2 ^ (prefixWord ++ tailWord_2504717).sum := by decide
  have hdescent : baseEnd_2504717 < baseStart_2504717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504769 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2504769 : Nat := 118140960795 + 2504769 * 2 ^ 59
def prefixEnd_2504769 : Nat := 4983230072969 + 3 ^ 40 * 2504769 * 2
def baseEnd_2504769 : Nat := 428716808493871937822761

theorem tailTrace_2504769 : CollatzResearch.WordTrace tailWord_2504769 prefixEnd_2504769 428716808493871937822761 := by
  unfold tailWord_2504769
  simp only [CollatzResearch.WordTrace]
  refine ⟨91356430662657168332965361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60904287108438112221976907 91356430662657168332965361)
  ·
    refine ⟨68517322996992876249724021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91356430662657168332965361 68517322996992876249724021)
    ·
      refine ⟨6423499030968082148411627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68517322996992876249724021 6423499030968082148411627)
      ·
        refine ⟨9635248546452123222617441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423499030968082148411627 9635248546452123222617441)
        ·
          refine ⟨7226436409839092416963081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9635248546452123222617441 7226436409839092416963081)
          ·
            refine ⟨5419827307379319312722311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7226436409839092416963081 5419827307379319312722311)
            ·
              refine ⟨8129740961068978969083467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419827307379319312722311 8129740961068978969083467)
              ·
                refine ⟨12194611441603468453625201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129740961068978969083467 12194611441603468453625201)
                ·
                  refine ⟨9145958581202601340218901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12194611441603468453625201 9145958581202601340218901)
                  ·
                    refine ⟨428716808493871937822761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9145958581202601340218901 428716808493871937822761)
                    ·
                      rfl

theorem cell23_2504769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2504769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504769 prefixEnd_2504769 := by exact prefixLift 2504769
  have htrace : WordTrace (prefixWord ++ tailWord_2504769) baseStart_2504769 baseEnd_2504769 := by
    simpa [prefixWord, tailWord_2504769, baseEnd_2504769] using wordTrace_append hprefix tailTrace_2504769
  have hstable : (prefixWord ++ tailWord_2504769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504769).length < 2 ^ (prefixWord ++ tailWord_2504769).sum := by decide
  have hdescent : baseEnd_2504769 < baseStart_2504769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504782 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_2504782 : Nat := 118140960795 + 2504782 * 2 ^ 59
def prefixEnd_2504782 : Nat := 4983230072969 + 3 ^ 40 * 2504782 * 2
def baseEnd_2504782 : Nat := 142906344525569362511747

theorem tailTrace_2504782 : CollatzResearch.WordTrace tailWord_2504782 prefixEnd_2504782 142906344525569362511747 := by
  unfold tailWord_2504782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419613101451258944148575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60904603207740047702125733 11419613101451258944148575)
  ·
    refine ⟨17129419652176888416222863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11419613101451258944148575 17129419652176888416222863)
    ·
      refine ⟨25694129478265332624334295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17129419652176888416222863 25694129478265332624334295)
      ·
        refine ⟨38541194217397998936501443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25694129478265332624334295 38541194217397998936501443)
        ·
          refine ⟨57811791326096998404752165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38541194217397998936501443 57811791326096998404752165)
          ·
            refine ⟨10839710873643187200891031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57811791326096998404752165 10839710873643187200891031)
            ·
              refine ⟨16259566310464780801336547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839710873643187200891031 16259566310464780801336547)
              ·
                refine ⟨24389349465697171202004821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16259566310464780801336547 24389349465697171202004821)
                ·
                  refine ⟨142906344525569362511747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24389349465697171202004821 142906344525569362511747)
                  ·
                    rfl

theorem cell23_2504782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_2504782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504782 prefixEnd_2504782 := by exact prefixLift 2504782
  have htrace : WordTrace (prefixWord ++ tailWord_2504782) baseStart_2504782 baseEnd_2504782 := by
    simpa [prefixWord, tailWord_2504782, baseEnd_2504782] using wordTrace_append hprefix tailTrace_2504782
  have hstable : (prefixWord ++ tailWord_2504782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504782).length < 2 ^ (prefixWord ++ tailWord_2504782).sum := by decide
  have hdescent : baseEnd_2504782 < baseStart_2504782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504797 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2504797 : Nat := 118140960795 + 2504797 * 2 ^ 59
def prefixEnd_2504797 : Nat := 4983230072969 + 3 ^ 40 * 2504797 * 2
def baseEnd_2504797 : Nat := 1286164802939941703918155

theorem tailTrace_2504797 : CollatzResearch.WordTrace tailWord_2504797 prefixEnd_2504797 1286164802939941703918155 := by
  unfold tailWord_2504797
  simp only [CollatzResearch.WordTrace]
  refine ⟨91357451906555729114984645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60904967937703819409989763 91357451906555729114984645)
  ·
    refine ⟨17129522232479199209059621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91357451906555729114984645 17129522232479199209059621)
    ·
      refine ⟨3211785418589849851698679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17129522232479199209059621 3211785418589849851698679)
      ·
        refine ⟨4817678127884774777548019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211785418589849851698679 4817678127884774777548019)
        ·
          refine ⟨7226517191827162166322029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817678127884774777548019 7226517191827162166322029)
          ·
            refine ⟨2709943946935185812370761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7226517191827162166322029 2709943946935185812370761)
            ·
              refine ⟨2032457960201389359278071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709943946935185812370761 2032457960201389359278071)
              ·
                refine ⟨3048686940302084038917107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032457960201389359278071 3048686940302084038917107)
                ·
                  refine ⟨4573030410453126058375661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048686940302084038917107 4573030410453126058375661)
                  ·
                    refine ⟨1714886403919922271890873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4573030410453126058375661 1714886403919922271890873)
                    ·
                      refine ⟨1286164802939941703918155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1714886403919922271890873 1286164802939941703918155)
                      ·
                        rfl

theorem cell23_2504797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2504797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504797 prefixEnd_2504797 := by exact prefixLift 2504797
  have htrace : WordTrace (prefixWord ++ tailWord_2504797) baseStart_2504797 baseEnd_2504797 := by
    simpa [prefixWord, tailWord_2504797, baseEnd_2504797] using wordTrace_append hprefix tailTrace_2504797
  have hstable : (prefixWord ++ tailWord_2504797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504797).length < 2 ^ (prefixWord ++ tailWord_2504797).sum := by decide
  have hdescent : baseEnd_2504797 < baseStart_2504797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504866 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2504866 : Nat := 118140960795 + 2504866 * 2 ^ 59
def prefixEnd_2504866 : Nat := 4983230072969 + 3 ^ 40 * 2504866 * 2
def baseEnd_2504866 : Nat := 1286200233105101933955337

theorem tailTrace_2504866 : CollatzResearch.WordTrace tailWord_2504866 prefixEnd_2504866 1286200233105101933955337 := by
  unfold tailWord_2504866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22839992135826438474811613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60906645695537169266164301 22839992135826438474811613)
  ·
    refine ⟨8564997050934914428054355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22839992135826438474811613 8564997050934914428054355)
    ·
      refine ⟨12847495576402371642081533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564997050934914428054355 12847495576402371642081533)
      ·
        refine ⟨4817810841150889365780575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12847495576402371642081533 4817810841150889365780575)
        ·
          refine ⟨7226716261726334048670863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817810841150889365780575 7226716261726334048670863)
          ·
            refine ⟨10840074392589501073006295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226716261726334048670863 10840074392589501073006295)
            ·
              refine ⟨16260111588884251609509443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840074392589501073006295 16260111588884251609509443)
              ·
                refine ⟨24390167383326377414264165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16260111588884251609509443 24390167383326377414264165)
                ·
                  refine ⟨4573156384373695765174531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24390167383326377414264165 4573156384373695765174531)
                  ·
                    refine ⟨6859734576560543647761797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573156384373695765174531 6859734576560543647761797)
                    ·
                      refine ⟨1286200233105101933955337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6859734576560543647761797 1286200233105101933955337)
                      ·
                        rfl

theorem cell23_2504866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2504866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504866 prefixEnd_2504866 := by exact prefixLift 2504866
  have htrace : WordTrace (prefixWord ++ tailWord_2504866) baseStart_2504866 baseEnd_2504866 := by
    simpa [prefixWord, tailWord_2504866, baseEnd_2504866] using wordTrace_append hprefix tailTrace_2504866
  have hstable : (prefixWord ++ tailWord_2504866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504866).length < 2 ^ (prefixWord ++ tailWord_2504866).sum := by decide
  have hdescent : baseEnd_2504866 < baseStart_2504866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504889 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 6]
def baseStart_2504889 : Nat := 118140960795 + 2504889 * 2 ^ 59
def prefixEnd_2504889 : Nat := 4983230072969 + 3 ^ 40 * 2504889 * 2
def baseEnd_2504889 : Nat := 142912449240017260440859

theorem tailTrace_2504889 : CollatzResearch.WordTrace tailWord_2504889 prefixEnd_2504889 142912449240017260440859 := by
  unfold tailWord_2504889
  simp only [CollatzResearch.WordTrace]
  refine ⟨91360807422222428827333721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60907204948148285884889147 91360807422222428827333721)
  ·
    refine ⟨68520605566666821620500291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91360807422222428827333721 68520605566666821620500291)
    ·
      refine ⟨102780908350000232430750437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68520605566666821620500291 102780908350000232430750437)
      ·
        refine ⟨19271420315625043580765707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102780908350000232430750437 19271420315625043580765707)
        ·
          refine ⟨28907130473437565371148561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19271420315625043580765707 28907130473437565371148561)
          ·
            refine ⟨21680347855078174028361421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28907130473437565371148561 21680347855078174028361421)
            ·
              refine ⟨8130130445654315260635533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21680347855078174028361421 8130130445654315260635533)
              ·
                refine ⟨3048798917120368222738325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8130130445654315260635533 3048798917120368222738325)
                ·
                  refine ⟨142912449240017260440859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048798917120368222738325 142912449240017260440859)
                  ·
                    rfl

theorem cell23_2504889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_2504889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504889 prefixEnd_2504889 := by exact prefixLift 2504889
  have htrace : WordTrace (prefixWord ++ tailWord_2504889) baseStart_2504889 baseEnd_2504889 := by
    simpa [prefixWord, tailWord_2504889, baseEnd_2504889] using wordTrace_append hprefix tailTrace_2504889
  have hstable : (prefixWord ++ tailWord_2504889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504889).length < 2 ^ (prefixWord ++ tailWord_2504889).sum := by decide
  have hdescent : baseEnd_2504889 < baseStart_2504889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504912 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2504912 : Nat := 118140960795 + 2504912 * 2 ^ 59
def prefixEnd_2504912 : Nat := 4983230072969 + 3 ^ 40 * 2504912 * 2
def baseEnd_2504912 : Nat := 1286223853215208753980125

theorem tailTrace_2504912 : CollatzResearch.WordTrace tailWord_2504912 prefixEnd_2504912 1286223853215208753980125 := by
  unfold tailWord_2504912
  simp only [CollatzResearch.WordTrace]
  refine ⟨45680823150569551877710495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60907764200759402503613993 45680823150569551877710495)
  ·
    refine ⟨68521234725854327816565743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45680823150569551877710495 68521234725854327816565743)
    ·
      refine ⟨102781852088781491724848615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68521234725854327816565743 102781852088781491724848615)
      ·
        refine ⟨154172778133172237587272923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102781852088781491724848615 154172778133172237587272923)
        ·
          refine ⟨231259167199758356380909385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154172778133172237587272923 231259167199758356380909385)
          ·
            refine ⟨173444375399818767285682039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231259167199758356380909385 173444375399818767285682039)
            ·
              refine ⟨260166563099728150928523059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173444375399818767285682039 260166563099728150928523059)
              ·
                refine ⟨390249844649592226392784589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260166563099728150928523059 390249844649592226392784589)
                ·
                  refine ⟨146343691743597084897294221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390249844649592226392784589 146343691743597084897294221)
                  ·
                    refine ⟨54878884403848906836485333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146343691743597084897294221 54878884403848906836485333)
                    ·
                      refine ⟨1286223853215208753980125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54878884403848906836485333 1286223853215208753980125)
                      ·
                        rfl

theorem cell23_2504912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2504912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504912 prefixEnd_2504912 := by exact prefixLift 2504912
  have htrace : WordTrace (prefixWord ++ tailWord_2504912) baseStart_2504912 baseEnd_2504912 := by
    simpa [prefixWord, tailWord_2504912, baseEnd_2504912] using wordTrace_append hprefix tailTrace_2504912
  have hstable : (prefixWord ++ tailWord_2504912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504912).length < 2 ^ (prefixWord ++ tailWord_2504912).sum := by decide
  have hdescent : baseEnd_2504912 < baseStart_2504912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504939 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4]
def baseStart_2504939 : Nat := 118140960795 + 2504939 * 2 ^ 59
def prefixEnd_2504939 : Nat := 4983230072969 + 3 ^ 40 * 2504939 * 2
def baseEnd_2504939 : Nat := 1286237717192880148342501

theorem tailTrace_2504939 : CollatzResearch.WordTrace tailWord_2504939 prefixEnd_2504939 1286237717192880148342501 := by
  unfold tailWord_2504939
  simp only [CollatzResearch.WordTrace]
  refine ⟨91362631072041287366653871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60908420714694191577769247 91362631072041287366653871)
  ·
    refine ⟨137043946608061931049980807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91362631072041287366653871 137043946608061931049980807)
    ·
      refine ⟨205565919912092896574971211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137043946608061931049980807 205565919912092896574971211)
      ·
        refine ⟨308348879868139344862456817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205565919912092896574971211 308348879868139344862456817)
        ·
          refine ⟨231261659901104508646842613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308348879868139344862456817 231261659901104508646842613)
          ·
            refine ⟨21680780615728547685641495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231261659901104508646842613 21680780615728547685641495)
            ·
              refine ⟨32521170923592821528462243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21680780615728547685641495 32521170923592821528462243)
              ·
                refine ⟨48781756385389232292693365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32521170923592821528462243 48781756385389232292693365)
                ·
                  refine ⟨4573289661130240527440003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48781756385389232292693365 4573289661130240527440003)
                  ·
                    refine ⟨6859934491695360791160005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573289661130240527440003 6859934491695360791160005)
                    ·
                      refine ⟨1286237717192880148342501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6859934491695360791160005 1286237717192880148342501)
                      ·
                        rfl

theorem cell23_2504939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_2504939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504939 prefixEnd_2504939 := by exact prefixLift 2504939
  have htrace : WordTrace (prefixWord ++ tailWord_2504939) baseStart_2504939 baseEnd_2504939 := by
    simpa [prefixWord, tailWord_2504939, baseEnd_2504939] using wordTrace_append hprefix tailTrace_2504939
  have hstable : (prefixWord ++ tailWord_2504939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504939).length < 2 ^ (prefixWord ++ tailWord_2504939).sum := by decide
  have hdescent : baseEnd_2504939 < baseStart_2504939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504956 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2504956 : Nat := 118140960795 + 2504956 * 2 ^ 59
def prefixEnd_2504956 : Nat := 4983230072969 + 3 ^ 40 * 2504956 * 2
def baseEnd_2504956 : Nat := 1286246446364006581829923

theorem tailTrace_2504956 : CollatzResearch.WordTrace tailWord_2504956 prefixEnd_2504956 1286246446364006581829923 := by
  unfold tailWord_2504956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45681625556489849635011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60908834075319799513348481 45681625556489849635011361)
  ·
    refine ⟨34261219167367387226258521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45681625556489849635011361 34261219167367387226258521)
    ·
      refine ⟨25695914375525540419693891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34261219167367387226258521 25695914375525540419693891)
      ·
        refine ⟨38543871563288310629540837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25695914375525540419693891 38543871563288310629540837)
        ·
          refine ⟨7226975918116558243038907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38543871563288310629540837 7226975918116558243038907)
          ·
            refine ⟨10840463877174837364558361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226975918116558243038907 10840463877174837364558361)
            ·
              refine ⟨8130347907881128023418771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10840463877174837364558361 8130347907881128023418771)
              ·
                refine ⟨12195521861821692035128157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130347907881128023418771 12195521861821692035128157)
                ·
                  refine ⟨4573320698183134513173059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12195521861821692035128157 4573320698183134513173059)
                  ·
                    refine ⟨6859981047274701769759589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573320698183134513173059 6859981047274701769759589)
                    ·
                      refine ⟨1286246446364006581829923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6859981047274701769759589 1286246446364006581829923)
                      ·
                        rfl

theorem cell23_2504956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2504956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504956 prefixEnd_2504956 := by exact prefixLift 2504956
  have htrace : WordTrace (prefixWord ++ tailWord_2504956) baseStart_2504956 baseEnd_2504956 := by
    simpa [prefixWord, tailWord_2504956, baseEnd_2504956] using wordTrace_append hprefix tailTrace_2504956
  have hstable : (prefixWord ++ tailWord_2504956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504956).length < 2 ^ (prefixWord ++ tailWord_2504956).sum := by decide
  have hdescent : baseEnd_2504956 < baseStart_2504956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504983 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 2, 4]
def baseStart_2504983 : Nat := 118140960795 + 2504983 * 2 ^ 59
def prefixEnd_2504983 : Nat := 4983230072969 + 3 ^ 40 * 2504983 * 2
def baseEnd_2504983 : Nat := 428753436780559325397433

theorem tailTrace_2504983 : CollatzResearch.WordTrace tailWord_2504983 prefixEnd_2504983 428753436780559325397433 := by
  unfold tailWord_2504983
  simp only [CollatzResearch.WordTrace]
  refine ⟨91364235883881882881255603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60909490589254588587503735 91364235883881882881255603)
  ·
    refine ⟨137046353825822824321883405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91364235883881882881255603 137046353825822824321883405)
    ·
      refine ⟨51392382684683559120706277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137046353825822824321883405 51392382684683559120706277)
      ·
        refine ⟨9636071753378167335132427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51392382684683559120706277 9636071753378167335132427)
        ·
          refine ⟨14454107630067251002698641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636071753378167335132427 14454107630067251002698641)
          ·
            refine ⟨10840580722550438252023981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14454107630067251002698641 10840580722550438252023981)
            ·
              refine ⟨4065217770956414344508993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10840580722550438252023981 4065217770956414344508993)
              ·
                refine ⟨3048913328217310758381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065217770956414344508993 3048913328217310758381745)
                ·
                  refine ⟨2286684996162983068786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3048913328217310758381745 2286684996162983068786309)
                  ·
                    refine ⟨428753436780559325397433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286684996162983068786309 428753436780559325397433)
                    ·
                      rfl

theorem cell23_2504983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_2504983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2504983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2504983 prefixEnd_2504983 := by exact prefixLift 2504983
  have htrace : WordTrace (prefixWord ++ tailWord_2504983) baseStart_2504983 baseEnd_2504983 := by
    simpa [prefixWord, tailWord_2504983, baseEnd_2504983] using wordTrace_append hprefix tailTrace_2504983
  have hstable : (prefixWord ++ tailWord_2504983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504983).length < 2 ^ (prefixWord ++ tailWord_2504983).sum := by decide
  have hdescent : baseEnd_2504983 < baseStart_2504983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505000 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2505000 : Nat := 118140960795 + 2505000 * 2 ^ 59
def prefixEnd_2505000 : Nat := 4983230072969 + 3 ^ 40 * 2505000 * 2
def baseEnd_2505000 : Nat := 428756346504268136559907

theorem tailTrace_2505000 : CollatzResearch.WordTrace tailWord_2505000 prefixEnd_2505000 428756346504268136559907 := by
  unfold tailWord_2505000
  simp only [CollatzResearch.WordTrace]
  refine ⟨45682427962410147392312227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60909903949880196523082969 45682427962410147392312227)
  ·
    refine ⟨68523641943615221088468341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45682427962410147392312227 68523641943615221088468341)
    ·
      refine ⟨6424091432213926977043907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68523641943615221088468341 6424091432213926977043907)
      ·
        refine ⟨9636137148320890465565861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424091432213926977043907 9636137148320890465565861)
        ·
          refine ⟨1806775715310166962293599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9636137148320890465565861 1806775715310166962293599)
          ·
            refine ⟨2710163572965250443440399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806775715310166962293599 2710163572965250443440399)
            ·
              refine ⟨4065245359447875665160599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710163572965250443440399 4065245359447875665160599)
              ·
                refine ⟨6097868039171813497740899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065245359447875665160599 6097868039171813497740899)
                ·
                  refine ⟨9146802058757720246611349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097868039171813497740899 9146802058757720246611349)
                  ·
                    refine ⟨428756346504268136559907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9146802058757720246611349 428756346504268136559907)
                    ·
                      rfl

theorem cell23_2505000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2505000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505000 prefixEnd_2505000 := by exact prefixLift 2505000
  have htrace : WordTrace (prefixWord ++ tailWord_2505000) baseStart_2505000 baseEnd_2505000 := by
    simpa [prefixWord, tailWord_2505000, baseEnd_2505000] using wordTrace_append hprefix tailTrace_2505000
  have hstable : (prefixWord ++ tailWord_2505000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505000).length < 2 ^ (prefixWord ++ tailWord_2505000).sum := by decide
  have hdescent : baseEnd_2505000 < baseStart_2505000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505010 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2505010 : Nat := 118140960795 + 2505010 * 2 ^ 59
def prefixEnd_2505010 : Nat := 4983230072969 + 3 ^ 40 * 2505010 * 2
def baseEnd_2505010 : Nat := 1286274174319349370554675

theorem tailTrace_2505010 : CollatzResearch.WordTrace tailWord_2505010 prefixEnd_2505010 1286274174319349370554675 := by
  unfold tailWord_2505010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841305163696016623122121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60910147103189377661658989 22841305163696016623122121)
  ·
    refine ⟨17130978872772012467341591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22841305163696016623122121 17130978872772012467341591)
    ·
      refine ⟨25696468309158018701012387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17130978872772012467341591 25696468309158018701012387)
      ·
        refine ⟨38544702463737028051518581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25696468309158018701012387 38544702463737028051518581)
        ·
          refine ⟨3613565855975346379829867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38544702463737028051518581 3613565855975346379829867)
          ·
            refine ⟨5420348783963019569744801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613565855975346379829867 5420348783963019569744801)
            ·
              refine ⟨4065261587972264677308601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5420348783963019569744801 4065261587972264677308601)
              ·
                refine ⟨3048946190979198507981451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065261587972264677308601 3048946190979198507981451)
                ·
                  refine ⟨4573419286468797761972177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048946190979198507981451 4573419286468797761972177)
                  ·
                    refine ⟨3430064464851598321479133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573419286468797761972177 3430064464851598321479133)
                    ·
                      refine ⟨1286274174319349370554675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430064464851598321479133 1286274174319349370554675)
                      ·
                        rfl

theorem cell23_2505010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2505010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505010 prefixEnd_2505010 := by exact prefixLift 2505010
  have htrace : WordTrace (prefixWord ++ tailWord_2505010) baseStart_2505010 baseEnd_2505010 := by
    simpa [prefixWord, tailWord_2505010, baseEnd_2505010] using wordTrace_append hprefix tailTrace_2505010
  have hstable : (prefixWord ++ tailWord_2505010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505010).length < 2 ^ (prefixWord ++ tailWord_2505010).sum := by decide
  have hdescent : baseEnd_2505010 < baseStart_2505010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505029 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2505029 : Nat := 118140960795 + 2505029 * 2 ^ 59
def prefixEnd_2505029 : Nat := 4983230072969 + 3 ^ 40 * 2505029 * 2
def baseEnd_2505029 : Nat := 1286283930451784796217087

theorem tailTrace_2505029 : CollatzResearch.WordTrace tailWord_2505029 prefixEnd_2505029 1286283930451784796217087 := by
  unfold tailWord_2505029
  simp only [CollatzResearch.WordTrace]
  refine ⟨91365913641715232737430141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60910609094476821824953427 91365913641715232737430141)
  ·
    refine ⟨34262217615643212276536303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91365913641715232737430141 34262217615643212276536303)
    ·
      refine ⟨51393326423464818414804455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34262217615643212276536303 51393326423464818414804455)
      ·
        refine ⟨77089989635197227622206683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51393326423464818414804455 77089989635197227622206683)
        ·
          refine ⟨115634984452795841433310025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77089989635197227622206683 115634984452795841433310025)
          ·
            refine ⟨86726238339596881074982519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115634984452795841433310025 86726238339596881074982519)
            ·
              refine ⟨130089357509395321612473779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86726238339596881074982519 130089357509395321612473779)
              ·
                refine ⟨195134036264092982418710669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130089357509395321612473779 195134036264092982418710669)
                ·
                  refine ⟨73175263599034868407016501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195134036264092982418710669 73175263599034868407016501)
                  ·
                    refine ⟨6860180962409518913157797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73175263599034868407016501 6860180962409518913157797)
                    ·
                      refine ⟨1286283930451784796217087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6860180962409518913157797 1286283930451784796217087)
                      ·
                        rfl

theorem cell23_2505029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2505029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505029 prefixEnd_2505029 := by exact prefixLift 2505029
  have htrace : WordTrace (prefixWord ++ tailWord_2505029) baseStart_2505029 baseEnd_2505029 := by
    simpa [prefixWord, tailWord_2505029, baseEnd_2505029] using wordTrace_append hprefix tailTrace_2505029
  have hstable : (prefixWord ++ tailWord_2505029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505029).length < 2 ^ (prefixWord ++ tailWord_2505029).sum := by decide
  have hdescent : baseEnd_2505029 < baseStart_2505029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505039 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 6]
def baseStart_2505039 : Nat := 118140960795 + 2505039 * 2 ^ 59
def prefixEnd_2505039 : Nat := 4983230072969 + 3 ^ 40 * 2505039 * 2
def baseEnd_2505039 : Nat := 428763021752776585697347

theorem tailTrace_2505039 : CollatzResearch.WordTrace tailWord_2505039 prefixEnd_2505039 428763021752776585697347 := by
  unfold tailWord_2505039
  simp only [CollatzResearch.WordTrace]
  refine ⟨91366278371679004445294171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60910852247786002963529447 91366278371679004445294171)
  ·
    refine ⟨137049417557518506667941257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91366278371679004445294171 137049417557518506667941257)
    ·
      refine ⟨102787063168138880000955943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137049417557518506667941257 102787063168138880000955943)
      ·
        refine ⟨154180594752208320001433915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102787063168138880000955943 154180594752208320001433915)
        ·
          refine ⟨231270892128312480002150873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154180594752208320001433915 231270892128312480002150873)
          ·
            refine ⟨173453169096234360001613155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231270892128312480002150873 173453169096234360001613155)
            ·
              refine ⟨260179753644351540002419733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173453169096234360001613155 260179753644351540002419733)
              ·
                refine ⟨12195925952078978437613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260179753644351540002419733 12195925952078978437613425)
                ·
                  refine ⟨9146944464059233828210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12195925952078978437613425 9146944464059233828210069)
                  ·
                    refine ⟨428763021752776585697347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9146944464059233828210069 428763021752776585697347)
                    ·
                      rfl

theorem cell23_2505039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_2505039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505039 prefixEnd_2505039 := by exact prefixLift 2505039
  have htrace : WordTrace (prefixWord ++ tailWord_2505039) baseStart_2505039 baseEnd_2505039 := by
    simpa [prefixWord, tailWord_2505039, baseEnd_2505039] using wordTrace_append hprefix tailTrace_2505039
  have hstable : (prefixWord ++ tailWord_2505039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505039).length < 2 ^ (prefixWord ++ tailWord_2505039).sum := by decide
  have hdescent : baseEnd_2505039 < baseStart_2505039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505049 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2505049 : Nat := 118140960795 + 2505049 * 2 ^ 59
def prefixEnd_2505049 : Nat := 4983230072969 + 3 ^ 40 * 2505049 * 2
def baseEnd_2505049 : Nat := 1286294200064874717966995

theorem tailTrace_2505049 : CollatzResearch.WordTrace tailWord_2505049 prefixEnd_2505049 1286294200064874717966995 := by
  unfold tailWord_2505049
  simp only [CollatzResearch.WordTrace]
  refine ⟨91366643101642776153158201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60911095401095184102105467 91366643101642776153158201)
  ·
    refine ⟨68524982326232082114868651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91366643101642776153158201 68524982326232082114868651)
    ·
      refine ⟨102787473489348123172302977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68524982326232082114868651 102787473489348123172302977)
      ·
        refine ⟨77090605117011092379227233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102787473489348123172302977 77090605117011092379227233)
        ·
          refine ⟨57817953837758319284420425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77090605117011092379227233 57817953837758319284420425)
          ·
            refine ⟨43363465378318739463315319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57817953837758319284420425 43363465378318739463315319)
            ·
              refine ⟨65045198067478109194972979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43363465378318739463315319 65045198067478109194972979)
              ·
                refine ⟨97567797101217163792459469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65045198067478109194972979 97567797101217163792459469)
                ·
                  refine ⟨36587923912956436422172301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97567797101217163792459469 36587923912956436422172301)
                  ·
                    refine ⟨13720471467358663658314613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36587923912956436422172301 13720471467358663658314613)
                    ·
                      refine ⟨1286294200064874717966995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13720471467358663658314613 1286294200064874717966995)
                      ·
                        rfl

theorem cell23_2505049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2505049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505049 prefixEnd_2505049 := by exact prefixLift 2505049
  have htrace : WordTrace (prefixWord ++ tailWord_2505049) baseStart_2505049 baseEnd_2505049 := by
    simpa [prefixWord, tailWord_2505049, baseEnd_2505049] using wordTrace_append hprefix tailTrace_2505049
  have hstable : (prefixWord ++ tailWord_2505049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505049).length < 2 ^ (prefixWord ++ tailWord_2505049).sum := by decide
  have hdescent : baseEnd_2505049 < baseStart_2505049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2505079 : Nat := 118140960795 + 2505079 * 2 ^ 59
def prefixEnd_2505079 : Nat := 4983230072969 + 3 ^ 40 * 2505079 * 2
def baseEnd_2505079 : Nat := 1286309604484509600591857

theorem tailTrace_2505079 : CollatzResearch.WordTrace tailWord_2505079 prefixEnd_2505079 1286309604484509600591857 := by
  unfold tailWord_2505079
  simp only [CollatzResearch.WordTrace]
  refine ⟨91367737291534091276750291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60911824861022727517833527 91367737291534091276750291)
  ·
    refine ⟨137051605937301136915125437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91367737291534091276750291 137051605937301136915125437)
    ·
      refine ⟨51394352226487926343172039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137051605937301136915125437 51394352226487926343172039)
      ·
        refine ⟨77091528339731889514758059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51394352226487926343172039 77091528339731889514758059)
        ·
          refine ⟨115637292509597834272137089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77091528339731889514758059 115637292509597834272137089)
          ·
            refine ⟨86727969382198375704102817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115637292509597834272137089 86727969382198375704102817)
            ·
              refine ⟨65045977036648781778077113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86727969382198375704102817 65045977036648781778077113)
              ·
                refine ⟨48784482777486586333557835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65045977036648781778077113 48784482777486586333557835)
                ·
                  refine ⟨73176724166229879500336753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48784482777486586333557835 73176724166229879500336753)
                  ·
                    refine ⟨54882543124672409625252565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73176724166229879500336753 54882543124672409625252565)
                    ·
                      refine ⟨1286309604484509600591857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54882543124672409625252565 1286309604484509600591857)
                      ·
                        rfl

theorem cell23_2505079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2505079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505079 prefixEnd_2505079 := by exact prefixLift 2505079
  have htrace : WordTrace (prefixWord ++ tailWord_2505079) baseStart_2505079 baseEnd_2505079 := by
    simpa [prefixWord, tailWord_2505079, baseEnd_2505079] using wordTrace_append hprefix tailTrace_2505079
  have hstable : (prefixWord ++ tailWord_2505079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505079).length < 2 ^ (prefixWord ++ tailWord_2505079).sum := by decide
  have hdescent : baseEnd_2505079 < baseStart_2505079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505097 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 2, 2, 2]
def baseStart_2505097 : Nat := 118140960795 + 2505097 * 2 ^ 59
def prefixEnd_2505097 : Nat := 4983230072969 + 3 ^ 40 * 2505097 * 2
def baseEnd_2505097 : Nat := 1286318847136290530166775

theorem tailTrace_2505097 : CollatzResearch.WordTrace tailWord_2505097 prefixEnd_2505097 1286318847136290530166775 := by
  unfold tailWord_2505097
  simp only [CollatzResearch.WordTrace]
  refine ⟨91368393805468880350905545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60912262536979253567270363 91368393805468880350905545)
  ·
    refine ⟨68526295354101660263179159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91368393805468880350905545 68526295354101660263179159)
    ·
      refine ⟨102789443031152490394768739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68526295354101660263179159 102789443031152490394768739)
      ·
        refine ⟨154184164546728735592153109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102789443031152490394768739 154184164546728735592153109)
        ·
          refine ⟨7227382713127909480882177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154184164546728735592153109 7227382713127909480882177)
          ·
            refine ⟨5420537034845932110661633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7227382713127909480882177 5420537034845932110661633)
            ·
              refine ⟨4065402776134449082996225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5420537034845932110661633 4065402776134449082996225)
              ·
                refine ⟨3049052082100836812247169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065402776134449082996225 3049052082100836812247169)
                ·
                  refine ⟨2286789061575627609185377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049052082100836812247169 2286789061575627609185377)
                  ·
                    refine ⟨1715091796181720706889033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2286789061575627609185377 1715091796181720706889033)
                    ·
                      refine ⟨1286318847136290530166775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1715091796181720706889033 1286318847136290530166775)
                      ·
                        rfl

theorem cell23_2505097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2, 2].length) (baseStart_2505097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505097 prefixEnd_2505097 := by exact prefixLift 2505097
  have htrace : WordTrace (prefixWord ++ tailWord_2505097) baseStart_2505097 baseEnd_2505097 := by
    simpa [prefixWord, tailWord_2505097, baseEnd_2505097] using wordTrace_append hprefix tailTrace_2505097
  have hstable : (prefixWord ++ tailWord_2505097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505097).length < 2 ^ (prefixWord ++ tailWord_2505097).sum := by decide
  have hdescent : baseEnd_2505097 < baseStart_2505097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505166 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2505166 : Nat := 118140960795 + 2505166 * 2 ^ 59
def prefixEnd_2505166 : Nat := 4983230072969 + 3 ^ 40 * 2505166 * 2
def baseEnd_2505166 : Nat := 1286354277301450760203957

theorem tailTrace_2505166 : CollatzResearch.WordTrace tailWord_2505166 prefixEnd_2505166 1286354277301450760203957 := by
  unfold tailWord_2505166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421363805277363141895919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60913940294812603423444901 11421363805277363141895919)
  ·
    refine ⟨17132045707916044712843879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11421363805277363141895919 17132045707916044712843879)
    ·
      refine ⟨25698068561874067069265819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17132045707916044712843879 25698068561874067069265819)
      ·
        refine ⟨38547102842811100603898729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25698068561874067069265819 38547102842811100603898729)
        ·
          refine ⟨28910327132108325452924047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38547102842811100603898729 28910327132108325452924047)
          ·
            refine ⟨43365490698162488179386071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28910327132108325452924047 43365490698162488179386071)
            ·
              refine ⟨65048236047243732269079107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43365490698162488179386071 65048236047243732269079107)
              ·
                refine ⟨97572354070865598403618661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65048236047243732269079107 97572354070865598403618661)
                ·
                  refine ⟨18294816388287299700678499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97572354070865598403618661 18294816388287299700678499)
                  ·
                    refine ⟨27442224582430949551017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18294816388287299700678499 27442224582430949551017749)
                    ·
                      refine ⟨1286354277301450760203957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27442224582430949551017749 1286354277301450760203957)
                      ·
                        rfl

theorem cell23_2505166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2505166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505166 prefixEnd_2505166 := by exact prefixLift 2505166
  have htrace : WordTrace (prefixWord ++ tailWord_2505166) baseStart_2505166 baseEnd_2505166 := by
    simpa [prefixWord, tailWord_2505166, baseEnd_2505166] using wordTrace_append hprefix tailTrace_2505166
  have hstable : (prefixWord ++ tailWord_2505166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505166).length < 2 ^ (prefixWord ++ tailWord_2505166).sum := by decide
  have hdescent : baseEnd_2505166 < baseStart_2505166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505173 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2505173 : Nat := 118140960795 + 2505173 * 2 ^ 59
def prefixEnd_2505173 : Nat := 4983230072969 + 3 ^ 40 * 2505173 * 2
def baseEnd_2505173 : Nat := 1286357871666032232816425

theorem tailTrace_2505173 : CollatzResearch.WordTrace tailWord_2505173 prefixEnd_2505173 1286357871666032232816425 := by
  unfold tailWord_2505173
  simp only [CollatzResearch.WordTrace]
  refine ⟨91371165753193545330672173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60914110502129030220448115 91371165753193545330672173)
  ·
    refine ⟨34264187157447579499002065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91371165753193545330672173 34264187157447579499002065)
    ·
      refine ⟨25698140368085684624251549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34264187157447579499002065 25698140368085684624251549)
      ·
        refine ⟨9636802638032131734094331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25698140368085684624251549 9636802638032131734094331)
        ·
          refine ⟨14455203957048197601141497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636802638032131734094331 14455203957048197601141497)
          ·
            refine ⟨10841402967786148200856123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14455203957048197601141497 10841402967786148200856123)
            ·
              refine ⟨16262104451679222301284185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841402967786148200856123 16262104451679222301284185)
              ·
                refine ⟨12196578338759416725963139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16262104451679222301284185 12196578338759416725963139)
                ·
                  refine ⟨18294867508139125088944709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12196578338759416725963139 18294867508139125088944709)
                  ·
                    refine ⟨3430287657776085954177133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18294867508139125088944709 3430287657776085954177133)
                    ·
                      refine ⟨1286357871666032232816425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430287657776085954177133 1286357871666032232816425)
                      ·
                        rfl

theorem cell23_2505173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2505173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505173 prefixEnd_2505173 := by exact prefixLift 2505173
  have htrace : WordTrace (prefixWord ++ tailWord_2505173) baseStart_2505173 baseEnd_2505173 := by
    simpa [prefixWord, tailWord_2505173, baseEnd_2505173] using wordTrace_append hprefix tailTrace_2505173
  have hstable : (prefixWord ++ tailWord_2505173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505173).length < 2 ^ (prefixWord ++ tailWord_2505173).sum := by decide
  have hdescent : baseEnd_2505173 < baseStart_2505173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505240 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_2505240 : Nat := 118140960795 + 2505240 * 2 ^ 59
def prefixEnd_2505240 : Nat := 4983230072969 + 3 ^ 40 * 2505240 * 2
def baseEnd_2505240 : Nat := 428797424956627823559539

theorem tailTrace_2505240 : CollatzResearch.WordTrace tailWord_2505240 prefixEnd_2505240 428797424956627823559539 := by
  unfold tailWord_2505240
  simp only [CollatzResearch.WordTrace]
  refine ⟨45686804721975407886680587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60915739629300543848907449 45686804721975407886680587)
  ·
    refine ⟨68530207082963111830020881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45686804721975407886680587 68530207082963111830020881)
    ·
      refine ⟨51397655312222333872515661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68530207082963111830020881 51397655312222333872515661)
      ·
        refine ⟨19274120742083375202193373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51397655312222333872515661 19274120742083375202193373)
        ·
          refine ⟨7227795278281265700822515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19274120742083375202193373 7227795278281265700822515)
          ·
            refine ⟨10841692917421898551233773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227795278281265700822515 10841692917421898551233773)
            ·
              refine ⟨4065634844033211956712665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10841692917421898551233773 4065634844033211956712665)
              ·
                refine ⟨3049226133024908967534499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065634844033211956712665 3049226133024908967534499)
                ·
                  refine ⟨4573839199537363451301749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049226133024908967534499 4573839199537363451301749)
                  ·
                    refine ⟨428797424956627823559539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4573839199537363451301749 428797424956627823559539)
                    ·
                      rfl

theorem cell23_2505240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_2505240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505240 prefixEnd_2505240 := by exact prefixLift 2505240
  have htrace : WordTrace (prefixWord ++ tailWord_2505240) baseStart_2505240 baseEnd_2505240 := by
    simpa [prefixWord, tailWord_2505240, baseEnd_2505240] using wordTrace_append hprefix tailTrace_2505240
  have hstable : (prefixWord ++ tailWord_2505240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505240).length < 2 ^ (prefixWord ++ tailWord_2505240).sum := by decide
  have hdescent : baseEnd_2505240 < baseStart_2505240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505253 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_2505253 : Nat := 118140960795 + 2505253 * 2 ^ 59
def prefixEnd_2505253 : Nat := 4983230072969 + 3 ^ 40 * 2505253 * 2
def baseEnd_2505253 : Nat := 428799650039463973272019

theorem tailTrace_2505253 : CollatzResearch.WordTrace tailWord_2505253 prefixEnd_2505253 428799650039463973272019 := by
  unfold tailWord_2505253
  simp only [CollatzResearch.WordTrace]
  refine ⟨91374083592903718993584413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60916055728602479329056275 91374083592903718993584413)
  ·
    refine ⟨34265281347338894622594155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91374083592903718993584413 34265281347338894622594155)
    ·
      refine ⟨51397922021008341933891233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34265281347338894622594155 51397922021008341933891233)
      ·
        refine ⟨38548441515756256450418425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51397922021008341933891233 38548441515756256450418425)
        ·
          refine ⟨28911331136817192337813819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38548441515756256450418425 28911331136817192337813819)
          ·
            refine ⟨43366996705225788506720729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28911331136817192337813819 43366996705225788506720729)
            ·
              refine ⟨32525247528919341380040547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43366996705225788506720729 32525247528919341380040547)
              ·
                refine ⟨48787871293379012070060821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32525247528919341380040547 48787871293379012070060821)
                ·
                  refine ⟨2286931466877141190784101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48787871293379012070060821 2286931466877141190784101)
                  ·
                    refine ⟨428799650039463973272019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286931466877141190784101 428799650039463973272019)
                    ·
                      rfl

theorem cell23_2505253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_2505253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505253 prefixEnd_2505253 := by exact prefixLift 2505253
  have htrace : WordTrace (prefixWord ++ tailWord_2505253) baseStart_2505253 baseEnd_2505253 := by
    simpa [prefixWord, tailWord_2505253, baseEnd_2505253] using wordTrace_append hprefix tailTrace_2505253
  have hstable : (prefixWord ++ tailWord_2505253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505253).length < 2 ^ (prefixWord ++ tailWord_2505253).sum := by decide
  have hdescent : baseEnd_2505253 < baseStart_2505253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505273 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2505273 : Nat := 118140960795 + 2505273 * 2 ^ 59
def prefixEnd_2505273 : Nat := 4983230072969 + 3 ^ 40 * 2505273 * 2
def baseEnd_2505273 : Nat := 1286409219731481841565965

theorem tailTrace_2505273 : CollatzResearch.WordTrace tailWord_2505273 prefixEnd_2505273 1286409219731481841565965 := by
  unfold tailWord_2505273
  simp only [CollatzResearch.WordTrace]
  refine ⟨91374813052831262409312473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60916542035220841606208315 91374813052831262409312473)
  ·
    refine ⟨68531109789623446806984355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91374813052831262409312473 68531109789623446806984355)
    ·
      refine ⟨102796664684435170210476533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68531109789623446806984355 102796664684435170210476533)
      ·
        refine ⟨9637187314165797207232175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102796664684435170210476533 9637187314165797207232175)
        ·
          refine ⟨14455780971248695810848263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637187314165797207232175 14455780971248695810848263)
          ·
            refine ⟨21683671456873043716272395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455780971248695810848263 21683671456873043716272395)
            ·
              refine ⟨32525507185309565574408593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21683671456873043716272395 32525507185309565574408593)
              ·
                refine ⟨24394130388982174180806445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32525507185309565574408593 24394130388982174180806445)
                ·
                  refine ⟨9147798895868315317802417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24394130388982174180806445 9147798895868315317802417)
                  ·
                    refine ⟨6860849171901236488351813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9147798895868315317802417 6860849171901236488351813)
                    ·
                      refine ⟨1286409219731481841565965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6860849171901236488351813 1286409219731481841565965)
                      ·
                        rfl

theorem cell23_2505273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2505273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505273 prefixEnd_2505273 := by exact prefixLift 2505273
  have htrace : WordTrace (prefixWord ++ tailWord_2505273) baseStart_2505273 baseEnd_2505273 := by
    simpa [prefixWord, tailWord_2505273, baseEnd_2505273] using wordTrace_append hprefix tailTrace_2505273
  have hstable : (prefixWord ++ tailWord_2505273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505273).length < 2 ^ (prefixWord ++ tailWord_2505273).sum := by decide
  have hdescent : baseEnd_2505273 < baseStart_2505273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505290 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2505290 : Nat := 118140960795 + 2505290 * 2 ^ 59
def prefixEnd_2505290 : Nat := 4983230072969 + 3 ^ 40 * 2505290 * 2
def baseEnd_2505290 : Nat := 1286417948902608275053387

theorem tailTrace_2505290 : CollatzResearch.WordTrace tailWord_2505290 prefixEnd_2505290 1286417948902608275053387 := by
  unfold tailWord_2505290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843858273442418578170331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60916955395846449541787549 22843858273442418578170331)
  ·
    refine ⟨34265787410163627867255497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22843858273442418578170331 34265787410163627867255497)
    ·
      refine ⟨25699340557622720900441623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34265787410163627867255497 25699340557622720900441623)
      ·
        refine ⟨38549010836434081350662435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25699340557622720900441623 38549010836434081350662435)
        ·
          refine ⟨57823516254651122025993653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38549010836434081350662435 57823516254651122025993653)
          ·
            refine ⟨5420954648873542689936905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57823516254651122025993653 5420954648873542689936905)
            ·
              refine ⟨4065715986655157017452679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5420954648873542689936905 4065715986655157017452679)
              ·
                refine ⟨6098573979982735526179019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065715986655157017452679 6098573979982735526179019)
                ·
                  refine ⟨9147860969974103289268529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6098573979982735526179019 9147860969974103289268529)
                  ·
                    refine ⟨6860895727480577466951397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9147860969974103289268529 6860895727480577466951397)
                    ·
                      refine ⟨1286417948902608275053387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6860895727480577466951397 1286417948902608275053387)
                      ·
                        rfl

theorem cell23_2505290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2505290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505290 prefixEnd_2505290 := by exact prefixLift 2505290
  have htrace : WordTrace (prefixWord ++ tailWord_2505290) baseStart_2505290 baseEnd_2505290 := by
    simpa [prefixWord, tailWord_2505290, baseEnd_2505290] using wordTrace_append hprefix tailTrace_2505290
  have hstable : (prefixWord ++ tailWord_2505290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505290).length < 2 ^ (prefixWord ++ tailWord_2505290).sum := by decide
  have hdescent : baseEnd_2505290 < baseStart_2505290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505300 : List Nat := [2, 4, 1, 1, 1, 4, 3, 7]
def baseStart_2505300 : Nat := 118140960795 + 2505300 * 2 ^ 59
def prefixEnd_2505300 : Nat := 4983230072969 + 3 ^ 40 * 2505300 * 2
def baseEnd_2505300 : Nat := 47645299396635305034383

theorem tailTrace_2505300 : CollatzResearch.WordTrace tailWord_2505300 prefixEnd_2505300 47645299396635305034383 := by
  unfold tailWord_2505300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45687898911866723010272677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60917198549155630680363569 45687898911866723010272677)
  ·
    refine ⟨8566481045975010564426127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45687898911866723010272677 8566481045975010564426127)
    ·
      refine ⟨12849721568962515846639191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566481045975010564426127 12849721568962515846639191)
      ·
        refine ⟨19274582353443773769958787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849721568962515846639191 19274582353443773769958787)
        ·
          refine ⟨28911873530165660654938181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19274582353443773769958787 28911873530165660654938181)
          ·
            refine ⟨5420976286906061372800909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28911873530165660654938181 5420976286906061372800909)
            ·
              refine ⟨2032866107589773014800341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5420976286906061372800909 2032866107589773014800341)
              ·
                refine ⟨47645299396635305034383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2032866107589773014800341 47645299396635305034383)
                ·
                  rfl

theorem cell23_2505300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 7].length) (baseStart_2505300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505300 prefixEnd_2505300 := by exact prefixLift 2505300
  have htrace : WordTrace (prefixWord ++ tailWord_2505300) baseStart_2505300 baseEnd_2505300 := by
    simpa [prefixWord, tailWord_2505300, baseEnd_2505300] using wordTrace_append hprefix tailTrace_2505300
  have hstable : (prefixWord ++ tailWord_2505300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505300).length < 2 ^ (prefixWord ++ tailWord_2505300).sum := by decide
  have hdescent : baseEnd_2505300 < baseStart_2505300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505327 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_2505327 : Nat := 118140960795 + 2505327 * 2 ^ 59
def prefixEnd_2505327 : Nat := 4983230072969 + 3 ^ 40 * 2505327 * 2
def baseEnd_2505327 : Nat := 1286436947686824630290717

theorem tailTrace_2505327 : CollatzResearch.WordTrace tailWord_2505327 prefixEnd_2505327 1286436947686824630290717 := by
  unfold tailWord_2505327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91376782594635629631778235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60917855063090419754518823 91376782594635629631778235)
  ·
    refine ⟨137065173891953444447667353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91376782594635629631778235 137065173891953444447667353)
    ·
      refine ⟨102798880418965083335750515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137065173891953444447667353 102798880418965083335750515)
      ·
        refine ⟨154198320628447625003625773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102798880418965083335750515 154198320628447625003625773)
        ·
          refine ⟨57824370235667859376359665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154198320628447625003625773 57824370235667859376359665)
          ·
            refine ⟨43368277676750894532269749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57824370235667859376359665 43368277676750894532269749)
            ·
              refine ⟨4065776032195396362400289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43368277676750894532269749 4065776032195396362400289)
              ·
                refine ⟨3049332024146547271800217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065776032195396362400289 3049332024146547271800217)
                ·
                  refine ⟨2286999018109910453850163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049332024146547271800217 2286999018109910453850163)
                  ·
                    refine ⟨3430498527164865680775245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2286999018109910453850163 3430498527164865680775245)
                    ·
                      refine ⟨1286436947686824630290717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430498527164865680775245 1286436947686824630290717)
                      ·
                        rfl

theorem cell23_2505327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_2505327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505327 prefixEnd_2505327 := by exact prefixLift 2505327
  have htrace : WordTrace (prefixWord ++ tailWord_2505327) baseStart_2505327 baseEnd_2505327 := by
    simpa [prefixWord, tailWord_2505327, baseEnd_2505327] using wordTrace_append hprefix tailTrace_2505327
  have hstable : (prefixWord ++ tailWord_2505327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505327).length < 2 ^ (prefixWord ++ tailWord_2505327).sum := by decide
  have hdescent : baseEnd_2505327 < baseStart_2505327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505344 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3]
def baseStart_2505344 : Nat := 118140960795 + 2505344 * 2 ^ 59
def prefixEnd_2505344 : Nat := 4983230072969 + 3 ^ 40 * 2505344 * 2
def baseEnd_2505344 : Nat := 1286445676857951063778139

theorem tailTrace_2505344 : CollatzResearch.WordTrace tailWord_2505344 prefixEnd_2505344 1286445676857951063778139 := by
  unfold tailWord_2505344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688701317787020767573543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60918268423716027690098057 45688701317787020767573543)
  ·
    refine ⟨68533051976680531151360315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45688701317787020767573543 68533051976680531151360315)
    ·
      refine ⟨102799577965020796727040473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68533051976680531151360315 102799577965020796727040473)
      ·
        refine ⟨77099683473765597545280355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102799577965020796727040473 77099683473765597545280355)
        ·
          refine ⟨115649525210648396317920533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77099683473765597545280355 115649525210648396317920533)
          ·
            refine ⟨5421071494249143577402525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115649525210648396317920533 5421071494249143577402525)
            ·
              refine ⟨2032901810343428841525947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5421071494249143577402525 2032901810343428841525947)
              ·
                refine ⟨3049352715515143262288921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032901810343428841525947 3049352715515143262288921)
                ·
                  refine ⟨2287014536636357446716691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049352715515143262288921 2287014536636357446716691)
                  ·
                    refine ⟨3430521804954536170075037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2287014536636357446716691 3430521804954536170075037)
                    ·
                      refine ⟨1286445676857951063778139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430521804954536170075037 1286445676857951063778139)
                      ·
                        rfl

theorem cell23_2505344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_2505344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505344 prefixEnd_2505344 := by exact prefixLift 2505344
  have htrace : WordTrace (prefixWord ++ tailWord_2505344) baseStart_2505344 baseEnd_2505344 := by
    simpa [prefixWord, tailWord_2505344, baseEnd_2505344] using wordTrace_append hprefix tailTrace_2505344
  have hstable : (prefixWord ++ tailWord_2505344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505344).length < 2 ^ (prefixWord ++ tailWord_2505344).sum := by decide
  have hdescent : baseEnd_2505344 < baseStart_2505344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505353 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_2505353 : Nat := 118140960795 + 2505353 * 2 ^ 59
def prefixEnd_2505353 : Nat := 4983230072969 + 3 ^ 40 * 2505353 * 2
def baseEnd_2505353 : Nat := 1286450298183841528565597

theorem tailTrace_2505353 : CollatzResearch.WordTrace tailWord_2505353 prefixEnd_2505353 1286450298183841528565597 := by
  unfold tailWord_2505353
  simp only [CollatzResearch.WordTrace]
  refine ⟨91377730892541436072224713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60918487261694290714816475 91377730892541436072224713)
  ·
    refine ⟨68533298169406077054168535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91377730892541436072224713 68533298169406077054168535)
    ·
      refine ⟨102799947254109115581252803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68533298169406077054168535 102799947254109115581252803)
      ·
        refine ⟨154199920881163673371879205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102799947254109115581252803 154199920881163673371879205)
        ·
          refine ⟨28912485165218188757227351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154199920881163673371879205 28912485165218188757227351)
          ·
            refine ⟨43368727747827283135841027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28912485165218188757227351 43368727747827283135841027)
            ·
              refine ⟨65053091621740924703761541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43368727747827283135841027 65053091621740924703761541)
              ·
                refine ⟨12197454679076423381955289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65053091621740924703761541 12197454679076423381955289)
                ·
                  refine ⟨9148091009307317536466467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12197454679076423381955289 9148091009307317536466467)
                  ·
                    refine ⟨13722136513960976304699701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9148091009307317536466467 13722136513960976304699701)
                    ·
                      refine ⟨1286450298183841528565597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13722136513960976304699701 1286450298183841528565597)
                      ·
                        rfl

theorem cell23_2505353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_2505353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505353 prefixEnd_2505353 := by exact prefixLift 2505353
  have htrace : WordTrace (prefixWord ++ tailWord_2505353) baseStart_2505353 baseEnd_2505353 := by
    simpa [prefixWord, tailWord_2505353, baseEnd_2505353] using wordTrace_append hprefix tailTrace_2505353
  have hstable : (prefixWord ++ tailWord_2505353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505353).length < 2 ^ (prefixWord ++ tailWord_2505353).sum := by decide
  have hdescent : baseEnd_2505353 < baseStart_2505353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505367 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_2505367 : Nat := 118140960795 + 2505367 * 2 ^ 59
def prefixEnd_2505367 : Nat := 4983230072969 + 3 ^ 40 * 2505367 * 2
def baseEnd_2505367 : Nat := 1286457486913004473790533

theorem tailTrace_2505367 : CollatzResearch.WordTrace tailWord_2505367 prefixEnd_2505367 1286457486913004473790533 := by
  unfold tailWord_2505367
  simp only [CollatzResearch.WordTrace]
  refine ⟨91378241514490716463234355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60918827676327144308822903 91378241514490716463234355)
  ·
    refine ⟨137067362271736074694851533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91378241514490716463234355 137067362271736074694851533)
    ·
      refine ⟨51400260851901028010569325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137067362271736074694851533 51400260851901028010569325)
      ·
        refine ⟨19275097819462885503963497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51400260851901028010569325 19275097819462885503963497)
        ·
          refine ⟨14456323364597164127972623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19275097819462885503963497 14456323364597164127972623)
          ·
            refine ⟨21684485046895746191958935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14456323364597164127972623 21684485046895746191958935)
            ·
              refine ⟨32526727570343619287938403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21684485046895746191958935 32526727570343619287938403)
              ·
                refine ⟨48790091355515428931907605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32526727570343619287938403 48790091355515428931907605)
                ·
                  refine ⟨2287035532289785731183169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48790091355515428931907605 2287035532289785731183169)
                  ·
                    refine ⟨1715276649217339298387377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2287035532289785731183169 1715276649217339298387377)
                    ·
                      refine ⟨1286457486913004473790533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1715276649217339298387377 1286457486913004473790533)
                      ·
                        rfl

theorem cell23_2505367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_2505367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505367 prefixEnd_2505367 := by exact prefixLift 2505367
  have htrace : WordTrace (prefixWord ++ tailWord_2505367) baseStart_2505367 baseEnd_2505367 := by
    simpa [prefixWord, tailWord_2505367, baseEnd_2505367] using wordTrace_append hprefix tailTrace_2505367
  have hstable : (prefixWord ++ tailWord_2505367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505367).length < 2 ^ (prefixWord ++ tailWord_2505367).sum := by decide
  have hdescent : baseEnd_2505367 < baseStart_2505367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505373 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 9]
def baseStart_2505373 : Nat := 118140960795 + 2505373 * 2 ^ 59
def prefixEnd_2505373 : Nat := 4983230072969 + 3 ^ 40 * 2505373 * 2
def baseEnd_2505373 : Nat := 142940063088547938923945

theorem tailTrace_2505373 : CollatzResearch.WordTrace tailWord_2505373 prefixEnd_2505373 142940063088547938923945 := by
  unfold tailWord_2505373
  simp only [CollatzResearch.WordTrace]
  refine ⟨91378460352468979487952773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60918973568312652991968515 91378460352468979487952773)
  ·
    refine ⟨17133461316087933653991145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91378460352468979487952773 17133461316087933653991145)
    ·
      refine ⟨12850095987065950240493359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17133461316087933653991145 12850095987065950240493359)
      ·
        refine ⟨19275143980598925360740039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12850095987065950240493359 19275143980598925360740039)
        ·
          refine ⟨28912715970898388041110059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19275143980598925360740039 28912715970898388041110059)
          ·
            refine ⟨43369073956347582061665089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28912715970898388041110059 43369073956347582061665089)
            ·
              refine ⟨32526805467260686546248817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43369073956347582061665089 32526805467260686546248817)
              ·
                refine ⟨24395104100445514909686613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32526805467260686546248817 24395104100445514909686613)
                ·
                  refine ⟨142940063088547938923945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24395104100445514909686613 142940063088547938923945)
                  ·
                    rfl

theorem cell23_2505373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_2505373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505373 prefixEnd_2505373 := by exact prefixLift 2505373
  have htrace : WordTrace (prefixWord ++ tailWord_2505373) baseStart_2505373 baseEnd_2505373 := by
    simpa [prefixWord, tailWord_2505373, baseEnd_2505373] using wordTrace_append hprefix tailTrace_2505373
  have hstable : (prefixWord ++ tailWord_2505373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505373).length < 2 ^ (prefixWord ++ tailWord_2505373).sum := by decide
  have hdescent : baseEnd_2505373 < baseStart_2505373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505413 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2505413 : Nat := 118140960795 + 2505413 * 2 ^ 59
def prefixEnd_2505413 : Nat := 4983230072969 + 3 ^ 40 * 2505413 * 2
def baseEnd_2505413 : Nat := 1286481107023111293815321

theorem tailTrace_2505413 : CollatzResearch.WordTrace tailWord_2505413 prefixEnd_2505413 1286481107023111293815321 := by
  unfold tailWord_2505413
  simp only [CollatzResearch.WordTrace]
  refine ⟨91379919272324066319408893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60919946181549377546272595 91379919272324066319408893)
  ·
    refine ⟨34267469727121524869778335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91379919272324066319408893 34267469727121524869778335)
    ·
      refine ⟨51401204590682287304667503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34267469727121524869778335 51401204590682287304667503)
      ·
        refine ⟨77101806886023430957001255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51401204590682287304667503 77101806886023430957001255)
        ·
          refine ⟨115652710329035146435501883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77101806886023430957001255 115652710329035146435501883)
          ·
            refine ⟨173479065493552719653252825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115652710329035146435501883 173479065493552719653252825)
            ·
              refine ⟨130109299120164539739939619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173479065493552719653252825 130109299120164539739939619)
              ·
                refine ⟨195163948680246809609909429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130109299120164539739939619 195163948680246809609909429)
                ·
                  refine ⟨18296620188773138400929009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195163948680246809609909429 18296620188773138400929009)
                  ·
                    refine ⟨13722465141579853800696757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18296620188773138400929009 13722465141579853800696757)
                    ·
                      refine ⟨1286481107023111293815321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13722465141579853800696757 1286481107023111293815321)
                      ·
                        rfl

theorem cell23_2505413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2505413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505413 prefixEnd_2505413 := by exact prefixLift 2505413
  have htrace : WordTrace (prefixWord ++ tailWord_2505413) baseStart_2505413 baseEnd_2505413 := by
    simpa [prefixWord, tailWord_2505413, baseEnd_2505413] using wordTrace_append hprefix tailTrace_2505413
  have hstable : (prefixWord ++ tailWord_2505413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505413).length < 2 ^ (prefixWord ++ tailWord_2505413).sum := by decide
  have hdescent : baseEnd_2505413 < baseStart_2505413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505457 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_2505457 : Nat := 118140960795 + 2505457 * 2 ^ 59
def prefixEnd_2505457 : Nat := 4983230072969 + 3 ^ 40 * 2505457 * 2
def baseEnd_2505457 : Nat := 1286503700171909121665119

theorem tailTrace_2505457 : CollatzResearch.WordTrace tailWord_2505457 prefixEnd_2505457 1286503700171909121665119 := by
  unfold tailWord_2505457
  simp only [CollatzResearch.WordTrace]
  refine ⟨91381524084164661834010625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60921016056109774556007083 91381524084164661834010625)
  ·
    refine ⟨68536143063123496375507969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91381524084164661834010625 68536143063123496375507969)
    ·
      refine ⟨51402107297342622281630977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68536143063123496375507969 51402107297342622281630977)
      ·
        refine ⟨38551580473006966711223233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51402107297342622281630977 38551580473006966711223233)
        ·
          refine ⟨28913685354755225033417425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38551580473006966711223233 28913685354755225033417425)
          ·
            refine ⟨21685264016066418775063069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28913685354755225033417425 21685264016066418775063069)
            ·
              refine ⟨8131974006024907040648651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21685264016066418775063069 8131974006024907040648651)
              ·
                refine ⟨12197961009037360560972977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131974006024907040648651 12197961009037360560972977)
                ·
                  refine ⟨9148470756778020420729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12197961009037360560972977 9148470756778020420729733)
                  ·
                    refine ⟨1715338266895878828886825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9148470756778020420729733 1715338266895878828886825)
                    ·
                      refine ⟨1286503700171909121665119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1715338266895878828886825 1286503700171909121665119)
                      ·
                        rfl

theorem cell23_2505457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_2505457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505457 prefixEnd_2505457 := by exact prefixLift 2505457
  have htrace : WordTrace (prefixWord ++ tailWord_2505457) baseStart_2505457 baseEnd_2505457 := by
    simpa [prefixWord, tailWord_2505457, baseEnd_2505457] using wordTrace_append hprefix tailTrace_2505457
  have hstable : (prefixWord ++ tailWord_2505457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505457).length < 2 ^ (prefixWord ++ tailWord_2505457).sum := by decide
  have hdescent : baseEnd_2505457 < baseStart_2505457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505463 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 10]
def baseStart_2505463 : Nat := 118140960795 + 2505463 * 2 ^ 59
def prefixEnd_2505463 : Nat := 4983230072969 + 3 ^ 40 * 2505463 * 2
def baseEnd_2505463 : Nat := 142945197895092899798899

theorem tailTrace_2505463 : CollatzResearch.WordTrace tailWord_2505463 prefixEnd_2505463 142945197895092899798899 := by
  unfold tailWord_2505463
  simp only [CollatzResearch.WordTrace]
  refine ⟨91381742922142924858729043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60921161948095283239152695 91381742922142924858729043)
  ·
    refine ⟨137072614383214387288093565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91381742922142924858729043 137072614383214387288093565)
    ·
      refine ⟨51402230393705395233035087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137072614383214387288093565 51402230393705395233035087)
      ·
        refine ⟨77103345590558092849552631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51402230393705395233035087 77103345590558092849552631)
        ·
          refine ⟨115655018385837139274328947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77103345590558092849552631 115655018385837139274328947)
          ·
            refine ⟨173482527578755708911493421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115655018385837139274328947 173482527578755708911493421)
            ·
              refine ⟨65055947842033390841810033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173482527578755708911493421 65055947842033390841810033)
              ·
                refine ⟨48791960881525043131357525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65055947842033390841810033 48791960881525043131357525)
                ·
                  refine ⟨142945197895092899798899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48791960881525043131357525 142945197895092899798899)
                  ·
                    rfl

theorem cell23_2505463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 10].length) (baseStart_2505463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505463 prefixEnd_2505463 := by exact prefixLift 2505463
  have htrace : WordTrace (prefixWord ++ tailWord_2505463) baseStart_2505463 baseEnd_2505463 := by
    simpa [prefixWord, tailWord_2505463, baseEnd_2505463] using wordTrace_append hprefix tailTrace_2505463
  have hstable : (prefixWord ++ tailWord_2505463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505463).length < 2 ^ (prefixWord ++ tailWord_2505463).sum := by decide
  have hdescent : baseEnd_2505463 < baseStart_2505463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505474 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2505474 : Nat := 118140960795 + 2505474 * 2 ^ 59
def prefixEnd_2505474 : Nat := 4983230072969 + 3 ^ 40 * 2505474 * 2
def baseEnd_2505474 : Nat := 1286512429343035555152541

theorem tailTrace_2505474 : CollatzResearch.WordTrace tailWord_2505474 prefixEnd_2505474 1286512429343035555152541 := by
  unfold tailWord_2505474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845536031275768434344869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60921429416735382491586317 22845536031275768434344869)
  ·
    refine ⟨4283538005864206581439663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22845536031275768434344869 4283538005864206581439663)
    ·
      refine ⟨6425307008796309872159495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283538005864206581439663 6425307008796309872159495)
      ·
        refine ⟨9637960513194464808239243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425307008796309872159495 9637960513194464808239243)
        ·
          refine ⟨14456940769791697212358865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637960513194464808239243 14456940769791697212358865)
          ·
            refine ⟨10842705577343772909269149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14456940769791697212358865 10842705577343772909269149)
            ·
              refine ⟨4066014591503914840975931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10842705577343772909269149 4066014591503914840975931)
              ·
                refine ⟨6099021887255872261463897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066014591503914840975931 6099021887255872261463897)
                ·
                  refine ⟨4574266415441904196097923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099021887255872261463897 4574266415441904196097923)
                  ·
                    refine ⟨6861399623162856294146885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574266415441904196097923 6861399623162856294146885)
                    ·
                      refine ⟨1286512429343035555152541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6861399623162856294146885 1286512429343035555152541)
                      ·
                        rfl

theorem cell23_2505474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2505474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505474 prefixEnd_2505474 := by exact prefixLift 2505474
  have htrace : WordTrace (prefixWord ++ tailWord_2505474) baseStart_2505474 baseEnd_2505474 := by
    simpa [prefixWord, tailWord_2505474, baseEnd_2505474] using wordTrace_append hprefix tailTrace_2505474
  have hstable : (prefixWord ++ tailWord_2505474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505474).length < 2 ^ (prefixWord ++ tailWord_2505474).sum := by decide
  have hdescent : baseEnd_2505474 < baseStart_2505474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505500 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2505500 : Nat := 118140960795 + 2505500 * 2 ^ 59
def prefixEnd_2505500 : Nat := 4983230072969 + 3 ^ 40 * 2505500 * 2
def baseEnd_2505500 : Nat := 1286525779840052453427421

theorem tailTrace_2505500 : CollatzResearch.WordTrace tailWord_2505500 prefixEnd_2505500 1286525779840052453427421 := by
  unfold tailWord_2505500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45691546211504440088912977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60922061615339253451883969 45691546211504440088912977)
  ·
    refine ⟨34268659658628330066684733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45691546211504440088912977 34268659658628330066684733)
    ·
      refine ⟨12850747371985623775006775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34268659658628330066684733 12850747371985623775006775)
      ·
        refine ⟨19276121057978435662510163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12850747371985623775006775 19276121057978435662510163)
        ·
          refine ⟨28914181586967653493765245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19276121057978435662510163 28914181586967653493765245)
          ·
            refine ⟨10842818095112870060161967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28914181586967653493765245 10842818095112870060161967)
            ·
              refine ⟨16264227142669305090242951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10842818095112870060161967 16264227142669305090242951)
              ·
                refine ⟨24396340714003957635364427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16264227142669305090242951 24396340714003957635364427)
                ·
                  refine ⟨36594511071005936453046641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24396340714003957635364427 36594511071005936453046641)
                  ·
                    refine ⟨27445883303254452339784981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36594511071005936453046641 27445883303254452339784981)
                    ·
                      refine ⟨1286525779840052453427421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27445883303254452339784981 1286525779840052453427421)
                      ·
                        rfl

theorem cell23_2505500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2505500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505500 prefixEnd_2505500 := by exact prefixLift 2505500
  have htrace : WordTrace (prefixWord ++ tailWord_2505500) baseStart_2505500 baseEnd_2505500 := by
    simpa [prefixWord, tailWord_2505500, baseEnd_2505500] using wordTrace_append hprefix tailTrace_2505500
  have hstable : (prefixWord ++ tailWord_2505500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505500).length < 2 ^ (prefixWord ++ tailWord_2505500).sum := by decide
  have hdescent : baseEnd_2505500 < baseStart_2505500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505501 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2505501 : Nat := 118140960795 + 2505501 * 2 ^ 59
def prefixEnd_2505501 : Nat := 4983230072969 + 3 ^ 40 * 2505501 * 2
def baseEnd_2505501 : Nat := 428842097773568983171639

theorem tailTrace_2505501 : CollatzResearch.WordTrace tailWord_2505501 prefixEnd_2505501 428842097773568983171639 := by
  unfold tailWord_2505501
  simp only [CollatzResearch.WordTrace]
  refine ⟨91383128896005257348612357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60922085930670171565741571 91383128896005257348612357)
  ·
    refine ⟨17134336668000985752864817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91383128896005257348612357 17134336668000985752864817)
    ·
      refine ⟨12850752501000739314648613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17134336668000985752864817 12850752501000739314648613)
      ·
        refine ⟨2409516093937638621496615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12850752501000739314648613 2409516093937638621496615)
        ·
          refine ⟨3614274140906457932244923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409516093937638621496615 3614274140906457932244923)
          ·
            refine ⟨5421411211359686898367385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614274140906457932244923 5421411211359686898367385)
            ·
              refine ⟨4066058408519765173775539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5421411211359686898367385 4066058408519765173775539)
              ·
                refine ⟨6099087612779647760663309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066058408519765173775539 6099087612779647760663309)
                ·
                  refine ⟨2287157854792367910248741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6099087612779647760663309 2287157854792367910248741)
                  ·
                    refine ⟨428842097773568983171639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287157854792367910248741 428842097773568983171639)
                    ·
                      rfl

theorem cell23_2505501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2505501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505501 prefixEnd_2505501 := by exact prefixLift 2505501
  have htrace : WordTrace (prefixWord ++ tailWord_2505501) baseStart_2505501 baseEnd_2505501 := by
    simpa [prefixWord, tailWord_2505501, baseEnd_2505501] using wordTrace_append hprefix tailTrace_2505501
  have hstable : (prefixWord ++ tailWord_2505501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505501).length < 2 ^ (prefixWord ++ tailWord_2505501).sum := by decide
  have hdescent : baseEnd_2505501 < baseStart_2505501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505527 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 1, 5]
def baseStart_2505527 : Nat := 118140960795 + 2505527 * 2 ^ 59
def prefixEnd_2505527 : Nat := 4983230072969 + 3 ^ 40 * 2505527 * 2
def baseEnd_2505527 : Nat := 428846547939241282596599

theorem tailTrace_2505527 : CollatzResearch.WordTrace tailWord_2505527 prefixEnd_2505527 428846547939241282596599 := by
  unfold tailWord_2505527
  simp only [CollatzResearch.WordTrace]
  refine ⟨91384077193911063789058835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60922718129274042526039223 91384077193911063789058835)
  ·
    refine ⟨137076115790866595683588253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91384077193911063789058835 137076115790866595683588253)
    ·
      refine ⟨51403543421574973381345595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137076115790866595683588253 51403543421574973381345595)
      ·
        refine ⟨77105315132362460072018393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51403543421574973381345595 77105315132362460072018393)
        ·
          refine ⟨57828986349271845054013795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77105315132362460072018393 57828986349271845054013795)
          ·
            refine ⟨86743479523907767581020693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57828986349271845054013795 86743479523907767581020693)
            ·
              refine ⟨4066100602683176605360345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86743479523907767581020693 4066100602683176605360345)
              ·
                refine ⟨3049575452012382454020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4066100602683176605360345 3049575452012382454020259)
                ·
                  refine ⟨4574363178018573681030389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049575452012382454020259 4574363178018573681030389)
                  ·
                    refine ⟨428846547939241282596599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4574363178018573681030389 428846547939241282596599)
                    ·
                      rfl

theorem cell23_2505527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_2505527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505527 prefixEnd_2505527 := by exact prefixLift 2505527
  have htrace : WordTrace (prefixWord ++ tailWord_2505527) baseStart_2505527 baseEnd_2505527 := by
    simpa [prefixWord, tailWord_2505527, baseEnd_2505527] using wordTrace_append hprefix tailTrace_2505527
  have hstable : (prefixWord ++ tailWord_2505527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505527).length < 2 ^ (prefixWord ++ tailWord_2505527).sum := by decide
  have hdescent : baseEnd_2505527 < baseStart_2505527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505557 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2505557 : Nat := 118140960795 + 2505557 * 2 ^ 59
def prefixEnd_2505557 : Nat := 4983230072969 + 3 ^ 40 * 2505557 * 2
def baseEnd_2505557 : Nat := 428851682745786243471553

theorem tailTrace_2505557 : CollatzResearch.WordTrace tailWord_2505557 prefixEnd_2505557 428851682745786243471553 := by
  unfold tailWord_2505557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91385171383802378912650925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60923447589201585941767283 91385171383802378912650925)
  ·
    refine ⟨34269439268925892092244097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91385171383802378912650925 34269439268925892092244097)
    ·
      refine ⟨25702079451694419069183073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34269439268925892092244097 25702079451694419069183073)
      ·
        refine ⟨19276559588770814301887305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25702079451694419069183073 19276559588770814301887305)
        ·
          refine ⟨14457419691578110726415479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19276559588770814301887305 14457419691578110726415479)
          ·
            refine ⟨21686129537367166089623219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14457419691578110726415479 21686129537367166089623219)
            ·
              refine ⟨32529194306050749134434829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21686129537367166089623219 32529194306050749134434829)
              ·
                refine ⟨12198447864769030925413061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32529194306050749134434829 12198447864769030925413061)
                ·
                  refine ⟨2287208974644193298514949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12198447864769030925413061 2287208974644193298514949)
                  ·
                    refine ⟨428851682745786243471553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287208974644193298514949 428851682745786243471553)
                    ·
                      rfl

theorem cell23_2505557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2505557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505557 prefixEnd_2505557 := by exact prefixLift 2505557
  have htrace : WordTrace (prefixWord ++ tailWord_2505557) baseStart_2505557 baseEnd_2505557 := by
    simpa [prefixWord, tailWord_2505557, baseEnd_2505557] using wordTrace_append hprefix tailTrace_2505557
  have hstable : (prefixWord ++ tailWord_2505557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505557).length < 2 ^ (prefixWord ++ tailWord_2505557).sum := by decide
  have hdescent : baseEnd_2505557 < baseStart_2505557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505567 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2505567 : Nat := 118140960795 + 2505567 * 2 ^ 59
def prefixEnd_2505567 : Nat := 4983230072969 + 3 ^ 40 * 2505567 * 2
def baseEnd_2505567 : Nat := 1286560183043903691289613

theorem tailTrace_2505567 : CollatzResearch.WordTrace tailWord_2505567 prefixEnd_2505567 1286560183043903691289613 := by
  unfold tailWord_2505567
  simp only [CollatzResearch.WordTrace]
  refine ⟨91385536113766150620514955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60923690742510767080343303 91385536113766150620514955)
  ·
    refine ⟨137078304170649225930772433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91385536113766150620514955 137078304170649225930772433)
    ·
      refine ⟨102808728127986919448079325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137078304170649225930772433 102808728127986919448079325)
      ·
        refine ⟨38553273047995094793029747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102808728127986919448079325 38553273047995094793029747)
        ·
          refine ⟨57829909571992642189544621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38553273047995094793029747 57829909571992642189544621)
          ·
            refine ⟨21686216089497240821079233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57829909571992642189544621 21686216089497240821079233)
            ·
              refine ⟨16264662067122930615809425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21686216089497240821079233 16264662067122930615809425)
              ·
                refine ⟨12198496550342197961857069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16264662067122930615809425 12198496550342197961857069)
                ·
                  refine ⟨4574436206378324235696401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12198496550342197961857069 4574436206378324235696401)
                  ·
                    refine ⟨3430827154783743176772301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574436206378324235696401 3430827154783743176772301)
                    ·
                      refine ⟨1286560183043903691289613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430827154783743176772301 1286560183043903691289613)
                      ·
                        rfl

theorem cell23_2505567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2505567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505567 prefixEnd_2505567 := by exact prefixLift 2505567
  have htrace : WordTrace (prefixWord ++ tailWord_2505567) baseStart_2505567 baseEnd_2505567 := by
    simpa [prefixWord, tailWord_2505567, baseEnd_2505567] using wordTrace_append hprefix tailTrace_2505567
  have hstable : (prefixWord ++ tailWord_2505567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505567).length < 2 ^ (prefixWord ++ tailWord_2505567).sum := by decide
  have hdescent : baseEnd_2505567 < baseStart_2505567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505584 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_2505584 : Nat := 118140960795 + 2505584 * 2 ^ 59
def prefixEnd_2505584 : Nat := 4983230072969 + 3 ^ 40 * 2505584 * 2
def baseEnd_2505584 : Nat := 1286568912215030124777035

theorem tailTrace_2505584 : CollatzResearch.WordTrace tailWord_2505584 prefixEnd_2505584 1286568912215030124777035 := by
  unfold tailWord_2505584
  simp only [CollatzResearch.WordTrace]
  refine ⟨45693078077352281261941903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60924104103136375015922537 45693078077352281261941903)
  ·
    refine ⟨68539617116028421892912855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45693078077352281261941903 68539617116028421892912855)
    ·
      refine ⟨102809425674042632839369283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68539617116028421892912855 102809425674042632839369283)
      ·
        refine ⟨154214138511063949259053925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102809425674042632839369283 154214138511063949259053925)
        ·
          refine ⟨28915150970824490486072611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154214138511063949259053925 28915150970824490486072611)
          ·
            refine ⟨43372726456236735729108917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915150970824490486072611 43372726456236735729108917)
            ·
              refine ⟨4066193105272193974603961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43372726456236735729108917 4066193105272193974603961)
              ·
                refine ⟨3049644828954145480952971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4066193105272193974603961 3049644828954145480952971)
                ·
                  refine ⟨4574467243431218221429457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049644828954145480952971 4574467243431218221429457)
                  ·
                    refine ⟨3430850432573413666072093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574467243431218221429457 3430850432573413666072093)
                    ·
                      refine ⟨1286568912215030124777035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430850432573413666072093 1286568912215030124777035)
                      ·
                        rfl

theorem cell23_2505584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_2505584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505584 prefixEnd_2505584 := by exact prefixLift 2505584
  have htrace : WordTrace (prefixWord ++ tailWord_2505584) baseStart_2505584 baseEnd_2505584 := by
    simpa [prefixWord, tailWord_2505584, baseEnd_2505584] using wordTrace_append hprefix tailTrace_2505584
  have hstable : (prefixWord ++ tailWord_2505584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505584).length < 2 ^ (prefixWord ++ tailWord_2505584).sum := by decide
  have hdescent : baseEnd_2505584 < baseStart_2505584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505597 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2505597 : Nat := 118140960795 + 2505597 * 2 ^ 59
def prefixEnd_2505597 : Nat := 4983230072969 + 3 ^ 40 * 2505597 * 2
def baseEnd_2505597 : Nat := 1286575587463538573914475

theorem tailTrace_2505597 : CollatzResearch.WordTrace tailWord_2505597 prefixEnd_2505597 1286575587463538573914475 := by
  unfold tailWord_2505597
  simp only [CollatzResearch.WordTrace]
  refine ⟨91386630303657465744107045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60924420202438310496071363 91386630303657465744107045)
  ·
    refine ⟨17134993181935774827020071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91386630303657465744107045 17134993181935774827020071)
    ·
      refine ⟨25702489772903662240530107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17134993181935774827020071 25702489772903662240530107)
      ·
        refine ⟨38553734659355493360795161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25702489772903662240530107 38553734659355493360795161)
        ·
          refine ⟨28915300994516620020596371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38553734659355493360795161 28915300994516620020596371)
          ·
            refine ⟨43372951491774930030894557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915300994516620020596371 43372951491774930030894557)
            ·
              refine ⟨16264856809415598761585459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43372951491774930030894557 16264856809415598761585459)
              ·
                refine ⟨24397285214123398142378189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16264856809415598761585459 24397285214123398142378189)
                ·
                  refine ⟨9148981955296274303391821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24397285214123398142378189 9148981955296274303391821)
                  ·
                    refine ⟨3430868233236102863771933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9148981955296274303391821 3430868233236102863771933)
                    ·
                      refine ⟨1286575587463538573914475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430868233236102863771933 1286575587463538573914475)
                      ·
                        rfl

theorem cell23_2505597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2505597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505597 prefixEnd_2505597 := by exact prefixLift 2505597
  have htrace : WordTrace (prefixWord ++ tailWord_2505597) baseStart_2505597 baseEnd_2505597 := by
    simpa [prefixWord, tailWord_2505597, baseEnd_2505597] using wordTrace_append hprefix tailTrace_2505597
  have hstable : (prefixWord ++ tailWord_2505597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505597).length < 2 ^ (prefixWord ++ tailWord_2505597).sum := by decide
  have hdescent : baseEnd_2505597 < baseStart_2505597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505631 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2505631 : Nat := 118140960795 + 2505631 * 2 ^ 59
def prefixEnd_2505631 : Nat := 4983230072969 + 3 ^ 40 * 2505631 * 2
def baseEnd_2505631 : Nat := 1286593045805791440889319

theorem tailTrace_2505631 : CollatzResearch.WordTrace tailWord_2505631 prefixEnd_2505631 1286593045805791440889319 := by
  unfold tailWord_2505631
  simp only [CollatzResearch.WordTrace]
  refine ⟨91387870385534289550844747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60925246923689526367229831 91387870385534289550844747)
  ·
    refine ⟨137081805578301434326267121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91387870385534289550844747 137081805578301434326267121)
    ·
      refine ⟨102811354183726075744700341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137081805578301434326267121 102811354183726075744700341)
      ·
        refine ⟨9638564454724319601065657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102811354183726075744700341 9638564454724319601065657)
        ·
          refine ⟨7228923341043239700799243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9638564454724319601065657 7228923341043239700799243)
          ·
            refine ⟨10843385011564859551198865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7228923341043239700799243 10843385011564859551198865)
            ·
              refine ⟨8132538758673644663399149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10843385011564859551198865 8132538758673644663399149)
              ·
                refine ⟨3049702034502616748774681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8132538758673644663399149 3049702034502616748774681)
                ·
                  refine ⟨2287276525876962561581011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049702034502616748774681 2287276525876962561581011)
                  ·
                    refine ⟨3430914788815443842371517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2287276525876962561581011 3430914788815443842371517)
                    ·
                      refine ⟨1286593045805791440889319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430914788815443842371517 1286593045805791440889319)
                      ·
                        rfl

theorem cell23_2505631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2505631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505631 prefixEnd_2505631 := by exact prefixLift 2505631
  have htrace : WordTrace (prefixWord ++ tailWord_2505631) baseStart_2505631 baseEnd_2505631 := by
    simpa [prefixWord, tailWord_2505631, baseEnd_2505631] using wordTrace_append hprefix tailTrace_2505631
  have hstable : (prefixWord ++ tailWord_2505631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505631).length < 2 ^ (prefixWord ++ tailWord_2505631).sum := by decide
  have hdescent : baseEnd_2505631 < baseStart_2505631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505684 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2505684 : Nat := 118140960795 + 2505684 * 2 ^ 59
def prefixEnd_2505684 : Nat := 4983230072969 + 3 ^ 40 * 2505684 * 2
def baseEnd_2505684 : Nat := 1286620260280479733526575

theorem tailTrace_2505684 : CollatzResearch.WordTrace tailWord_2505684 prefixEnd_2505684 1286620260280479733526575 := by
  unfold tailWord_2505684
  simp only [CollatzResearch.WordTrace]
  refine ⟨45694901727171139801262053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60926535636228186401682737 45694901727171139801262053)
  ·
    refine ⟨8567794073844588712736635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45694901727171139801262053 8567794073844588712736635)
    ·
      refine ⟨12851691110766883069104953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567794073844588712736635 12851691110766883069104953)
      ·
        refine ⟨9638768333075162301828715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12851691110766883069104953 9638768333075162301828715)
        ·
          refine ⟨14458152499612743452743073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638768333075162301828715 14458152499612743452743073)
          ·
            refine ⟨10843614374709557589557305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14458152499612743452743073 10843614374709557589557305)
            ·
              refine ⟨8132710781032168192167979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10843614374709557589557305 8132710781032168192167979)
              ·
                refine ⟨12199066171548252288251969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132710781032168192167979 12199066171548252288251969)
                ·
                  refine ⟨9149299628661189216188977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12199066171548252288251969 9149299628661189216188977)
                  ·
                    refine ⟨6861974721495891912141733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9149299628661189216188977 6861974721495891912141733)
                    ·
                      refine ⟨1286620260280479733526575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6861974721495891912141733 1286620260280479733526575)
                      ·
                        rfl

theorem cell23_2505684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2505684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505684 prefixEnd_2505684 := by exact prefixLift 2505684
  have htrace : WordTrace (prefixWord ++ tailWord_2505684) baseStart_2505684 baseEnd_2505684 := by
    simpa [prefixWord, tailWord_2505684, baseEnd_2505684] using wordTrace_append hprefix tailTrace_2505684
  have hstable : (prefixWord ++ tailWord_2505684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505684).length < 2 ^ (prefixWord ++ tailWord_2505684).sum := by decide
  have hdescent : baseEnd_2505684 < baseStart_2505684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505687 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2505687 : Nat := 118140960795 + 2505687 * 2 ^ 59
def prefixEnd_2505687 : Nat := 4983230072969 + 3 ^ 40 * 2505687 * 2
def baseEnd_2505687 : Nat := 1286621800722443221789061

theorem tailTrace_2505687 : CollatzResearch.WordTrace tailWord_2505687 prefixEnd_2505687 1286621800722443221789061 := by
  unfold tailWord_2505687
  simp only [CollatzResearch.WordTrace]
  refine ⟨91389912873331411114883315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60926608582220940743255543 91389912873331411114883315)
  ·
    refine ⟨137084869309997116672324973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91389912873331411114883315 137084869309997116672324973)
    ·
      refine ⟨51406825991248918752121865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137084869309997116672324973 51406825991248918752121865)
      ·
        refine ⟨38555119493436689064091399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51406825991248918752121865 38555119493436689064091399)
        ·
          refine ⟨57832679240155033596137099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38555119493436689064091399 57832679240155033596137099)
          ·
            refine ⟨86749018860232550394205649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57832679240155033596137099 86749018860232550394205649)
            ·
              refine ⟨65061764145174412795654237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86749018860232550394205649 65061764145174412795654237)
              ·
                refine ⟨24398161554440404798370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65061764145174412795654237 24398161554440404798370339)
                ·
                  refine ⟨36597242331660607197555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24398161554440404798370339 36597242331660607197555509)
                  ·
                    refine ⟨3430991468593181924770829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36597242331660607197555509 3430991468593181924770829)
                    ·
                      refine ⟨1286621800722443221789061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3430991468593181924770829 1286621800722443221789061)
                      ·
                        rfl

theorem cell23_2505687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2505687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505687 prefixEnd_2505687 := by exact prefixLift 2505687
  have htrace : WordTrace (prefixWord ++ tailWord_2505687) baseStart_2505687 baseEnd_2505687 := by
    simpa [prefixWord, tailWord_2505687, baseEnd_2505687] using wordTrace_append hprefix tailTrace_2505687
  have hstable : (prefixWord ++ tailWord_2505687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505687).length < 2 ^ (prefixWord ++ tailWord_2505687).sum := by decide
  have hdescent : baseEnd_2505687 < baseStart_2505687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505711 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 5]
def baseStart_2505711 : Nat := 118140960795 + 2505711 * 2 ^ 59
def prefixEnd_2505711 : Nat := 4983230072969 + 3 ^ 40 * 2505711 * 2
def baseEnd_2505711 : Nat := 142959347139794569765439

theorem tailTrace_2505711 : CollatzResearch.WordTrace tailWord_2505711 prefixEnd_2505711 142959347139794569765439 := by
  unfold tailWord_2505711
  simp only [CollatzResearch.WordTrace]
  refine ⟨91390788225244463213756987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60927192150162975475837991 91390788225244463213756987)
  ·
    refine ⟨137086182337866694820635481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91390788225244463213756987 137086182337866694820635481)
    ·
      refine ⟨102814636753400021115476611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137086182337866694820635481 102814636753400021115476611)
      ·
        refine ⟨154221955130100031673214917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102814636753400021115476611 154221955130100031673214917)
        ·
          refine ⟨28916616586893755938727797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154221955130100031673214917 28916616586893755938727797)
          ·
            refine ⟨2710932805021289619255731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28916616586893755938727797 2710932805021289619255731)
            ·
              refine ⟨4066399207531934428883597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710932805021289619255731 4066399207531934428883597)
              ·
                refine ⟨1524899702824475410831349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4066399207531934428883597 1524899702824475410831349)
                ·
                  refine ⟨142959347139794569765439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524899702824475410831349 142959347139794569765439)
                  ·
                    rfl

theorem cell23_2505711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 5].length) (baseStart_2505711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505711 prefixEnd_2505711 := by exact prefixLift 2505711
  have htrace : WordTrace (prefixWord ++ tailWord_2505711) baseStart_2505711 baseEnd_2505711 := by
    simpa [prefixWord, tailWord_2505711, baseEnd_2505711] using wordTrace_append hprefix tailTrace_2505711
  have hstable : (prefixWord ++ tailWord_2505711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505711).length < 2 ^ (prefixWord ++ tailWord_2505711).sum := by decide
  have hdescent : baseEnd_2505711 < baseStart_2505711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505724 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2505724 : Nat := 118140960795 + 2505724 * 2 ^ 59
def prefixEnd_2505724 : Nat := 4983230072969 + 3 ^ 40 * 2505724 * 2
def baseEnd_2505724 : Nat := 428880266502219859008797

theorem tailTrace_2505724 : CollatzResearch.WordTrace tailWord_2505724 prefixEnd_2505724 428880266502219859008797 := by
  unfold tailWord_2505724
  simp only [CollatzResearch.WordTrace]
  refine ⟨45695631187098683216990113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60927508249464910955986817 45695631187098683216990113)
  ·
    refine ⟨34271723390324012412742585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45695631187098683216990113 34271723390324012412742585)
    ·
      refine ⟨25703792542743009309556939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34271723390324012412742585 25703792542743009309556939)
      ·
        refine ⟨38555688814114513964335409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25703792542743009309556939 38555688814114513964335409)
        ·
          refine ⟨28916766610585885473251557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38555688814114513964335409 28916766610585885473251557)
          ·
            refine ⟨5421893739484853526234667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28916766610585885473251557 5421893739484853526234667)
            ·
              refine ⟨8132840609227280289352001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421893739484853526234667 8132840609227280289352001)
              ·
                refine ⟨6099630456920460217014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8132840609227280289352001 6099630456920460217014001)
                ·
                  refine ⟨4574722842690345162760501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099630456920460217014001 4574722842690345162760501)
                  ·
                    refine ⟨428880266502219859008797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4574722842690345162760501 428880266502219859008797)
                    ·
                      rfl

theorem cell23_2505724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2505724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505724 prefixEnd_2505724 := by exact prefixLift 2505724
  have htrace : WordTrace (prefixWord ++ tailWord_2505724) baseStart_2505724 baseEnd_2505724 := by
    simpa [prefixWord, tailWord_2505724, baseEnd_2505724] using wordTrace_append hprefix tailTrace_2505724
  have hstable : (prefixWord ++ tailWord_2505724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505724).length < 2 ^ (prefixWord ++ tailWord_2505724).sum := by decide
  have hdescent : baseEnd_2505724 < baseStart_2505724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505754 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_2505754 : Nat := 118140960795 + 2505754 * 2 ^ 59
def prefixEnd_2505754 : Nat := 4983230072969 + 3 ^ 40 * 2505754 * 2
def baseEnd_2505754 : Nat := 428885401308764819883751

theorem tailTrace_2505754 : CollatzResearch.WordTrace tailWord_2505754 prefixEnd_2505754 428885401308764819883751 := by
  unfold tailWord_2505754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22848089141022170389393079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60928237709392454371714877 22848089141022170389393079)
  ·
    refine ⟨34272133711533255584089619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22848089141022170389393079 34272133711533255584089619)
    ·
      refine ⟨51408200567299883376134429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34272133711533255584089619 51408200567299883376134429)
      ·
        refine ⟨19278075212737456266050411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51408200567299883376134429 19278075212737456266050411)
        ·
          refine ⟨28917112819106184399075617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19278075212737456266050411 28917112819106184399075617)
          ·
            refine ⟨21687834614329638299306713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28917112819106184399075617 21687834614329638299306713)
            ·
              refine ⟨16265875960747228724480035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21687834614329638299306713 16265875960747228724480035)
              ·
                refine ⟨24398813941120843086720053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16265875960747228724480035 24398813941120843086720053)
                ·
                  refine ⟨2287388806980079039380005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24398813941120843086720053 2287388806980079039380005)
                  ·
                    refine ⟨428885401308764819883751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287388806980079039380005 428885401308764819883751)
                    ·
                      rfl

theorem cell23_2505754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_2505754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505754 prefixEnd_2505754 := by exact prefixLift 2505754
  have htrace : WordTrace (prefixWord ++ tailWord_2505754) baseStart_2505754 baseEnd_2505754 := by
    simpa [prefixWord, tailWord_2505754, baseEnd_2505754] using wordTrace_append hprefix tailTrace_2505754
  have hstable : (prefixWord ++ tailWord_2505754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505754).length < 2 ^ (prefixWord ++ tailWord_2505754).sum := by decide
  have hdescent : baseEnd_2505754 < baseStart_2505754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505761 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2505761 : Nat := 118140960795 + 2505761 * 2 ^ 59
def prefixEnd_2505761 : Nat := 4983230072969 + 3 ^ 40 * 2505761 * 2
def baseEnd_2505761 : Nat := 1286659798290875932263721

theorem tailTrace_2505761 : CollatzResearch.WordTrace tailWord_2505761 prefixEnd_2505761 1286659798290875932263721 := by
  unfold tailWord_2505761
  simp only [CollatzResearch.WordTrace]
  refine ⟨91392611875063321753077137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60928407916708881168718091 91392611875063321753077137)
  ·
    refine ⟨68544458906297491314807853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91392611875063321753077137 68544458906297491314807853)
    ·
      refine ⟨25704172089861559243052945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68544458906297491314807853 25704172089861559243052945)
      ·
        refine ⟨19278129067396169432289709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25704172089861559243052945 19278129067396169432289709)
        ·
          refine ⟨7229298400273563537108641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19278129067396169432289709 7229298400273563537108641)
          ·
            refine ⟨5421973800205172652831481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229298400273563537108641 5421973800205172652831481)
            ·
              refine ⟨4066480350153879489623611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5421973800205172652831481 4066480350153879489623611)
              ·
                refine ⟨6099720525230819234435417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066480350153879489623611 6099720525230819234435417)
                ·
                  refine ⟨4574790393923114425826563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099720525230819234435417 4574790393923114425826563)
                  ·
                    refine ⟨6862185590884671638739845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574790393923114425826563 6862185590884671638739845)
                    ·
                      refine ⟨1286659798290875932263721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6862185590884671638739845 1286659798290875932263721)
                      ·
                        rfl

theorem cell23_2505761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2505761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505761 prefixEnd_2505761 := by exact prefixLift 2505761
  have htrace : WordTrace (prefixWord ++ tailWord_2505761) baseStart_2505761 baseEnd_2505761 := by
    simpa [prefixWord, tailWord_2505761, baseEnd_2505761] using wordTrace_append hprefix tailTrace_2505761
  have hstable : (prefixWord ++ tailWord_2505761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505761).length < 2 ^ (prefixWord ++ tailWord_2505761).sum := by decide
  have hdescent : baseEnd_2505761 < baseStart_2505761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505771 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 1, 4]
def baseStart_2505771 : Nat := 118140960795 + 2505771 * 2 ^ 59
def prefixEnd_2505771 : Nat := 4983230072969 + 3 ^ 40 * 2505771 * 2
def baseEnd_2505771 : Nat := 428888311032473631046225

theorem tailTrace_2505771 : CollatzResearch.WordTrace tailWord_2505771 prefixEnd_2505771 428888311032473631046225 := by
  unfold tailWord_2505771
  simp only [CollatzResearch.WordTrace]
  refine ⟨91392976605027093460941167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60928651070018062307294111 91392976605027093460941167)
  ·
    refine ⟨137089464907540640191411751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91392976605027093460941167 137089464907540640191411751)
    ·
      refine ⟨205634197361310960287117627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137089464907540640191411751 205634197361310960287117627)
      ·
        refine ⟨308451296041966440430676441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205634197361310960287117627 308451296041966440430676441)
        ·
          refine ⟨231338472031474830323007331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308451296041966440430676441 231338472031474830323007331)
          ·
            refine ⟨347007708047212245484510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231338472031474830323007331 347007708047212245484510997)
            ·
              refine ⟨16265986314713074007086453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 347007708047212245484510997 16265986314713074007086453)
              ·
                refine ⟨1524936217004350688164355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16265986314713074007086453 1524936217004350688164355)
                ·
                  refine ⟨2287404325506526032246533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524936217004350688164355 2287404325506526032246533)
                  ·
                    refine ⟨428888311032473631046225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287404325506526032246533 428888311032473631046225)
                    ·
                      rfl

theorem cell23_2505771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 4].length) (baseStart_2505771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505771 prefixEnd_2505771 := by exact prefixLift 2505771
  have htrace : WordTrace (prefixWord ++ tailWord_2505771) baseStart_2505771 baseEnd_2505771 := by
    simpa [prefixWord, tailWord_2505771, baseEnd_2505771] using wordTrace_append hprefix tailTrace_2505771
  have hstable : (prefixWord ++ tailWord_2505771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505771).length < 2 ^ (prefixWord ++ tailWord_2505771).sum := by decide
  have hdescent : baseEnd_2505771 < baseStart_2505771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505774 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2505774 : Nat := 118140960795 + 2505774 * 2 ^ 59
def prefixEnd_2505774 : Nat := 4983230072969 + 3 ^ 40 * 2505774 * 2
def baseEnd_2505774 : Nat := 1286666473539384381401161

theorem tailTrace_2505774 : CollatzResearch.WordTrace tailWord_2505774 prefixEnd_2505774 1286666473539384381401161 := by
  unfold tailWord_2505774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424135753002028121662547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60928724016010816648866917 11424135753002028121662547)
  ·
    refine ⟨17136203629503042182493821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11424135753002028121662547 17136203629503042182493821)
    ·
      refine ⟨6426076361063640818435183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17136203629503042182493821 6426076361063640818435183)
      ·
        refine ⟨9639114541595461227652775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426076361063640818435183 9639114541595461227652775)
        ·
          refine ⟨14458671812393191841479163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639114541595461227652775 14458671812393191841479163)
          ·
            refine ⟨21688007718589787762218745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14458671812393191841479163 21688007718589787762218745)
            ·
              refine ⟨16266005788942340821664059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21688007718589787762218745 16266005788942340821664059)
              ·
                refine ⟨24399008683413511232496089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16266005788942340821664059 24399008683413511232496089)
                ·
                  refine ⟨18299256512560133424372067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24399008683413511232496089 18299256512560133424372067)
                  ·
                    refine ⟨27448884768840200136558101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18299256512560133424372067 27448884768840200136558101)
                    ·
                      refine ⟨1286666473539384381401161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27448884768840200136558101 1286666473539384381401161)
                      ·
                        rfl

theorem cell23_2505774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2505774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505774 prefixEnd_2505774 := by exact prefixLift 2505774
  have htrace : WordTrace (prefixWord ++ tailWord_2505774) baseStart_2505774 baseEnd_2505774 := by
    simpa [prefixWord, tailWord_2505774, baseEnd_2505774] using wordTrace_append hprefix tailTrace_2505774
  have hstable : (prefixWord ++ tailWord_2505774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505774).length < 2 ^ (prefixWord ++ tailWord_2505774).sum := by decide
  have hdescent : baseEnd_2505774 < baseStart_2505774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505784 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 6]
def baseStart_2505784 : Nat := 118140960795 + 2505784 * 2 ^ 59
def prefixEnd_2505784 : Nat := 4983230072969 + 3 ^ 40 * 2505784 * 2
def baseEnd_2505784 : Nat := 142963512038436593586235

theorem tailTrace_2505784 : CollatzResearch.WordTrace tailWord_2505784 prefixEnd_2505784 142963512038436593586235 := by
  unfold tailWord_2505784
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696725376989998340582203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60928967169319997787442937 45696725376989998340582203)
  ·
    refine ⟨68545088065484997510873305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45696725376989998340582203 68545088065484997510873305)
    ·
      refine ⟨51408816049113748133154979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68545088065484997510873305 51408816049113748133154979)
      ·
        refine ⟨77113224073670622199732469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51408816049113748133154979 77113224073670622199732469)
        ·
          refine ⟨7229364756906620831224919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77113224073670622199732469 7229364756906620831224919)
          ·
            refine ⟨10844047135359931246837379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229364756906620831224919 10844047135359931246837379)
            ·
              refine ⟨16266070703039896870256069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10844047135359931246837379 16266070703039896870256069)
              ·
                refine ⟨3049888256819980663173013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16266070703039896870256069 3049888256819980663173013)
                ·
                  refine ⟨142963512038436593586235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3049888256819980663173013 142963512038436593586235)
                  ·
                    rfl

theorem cell23_2505784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_2505784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505784 prefixEnd_2505784 := by exact prefixLift 2505784
  have htrace : WordTrace (prefixWord ++ tailWord_2505784) baseStart_2505784 baseEnd_2505784 := by
    simpa [prefixWord, tailWord_2505784, baseEnd_2505784] using wordTrace_append hprefix tailTrace_2505784
  have hstable : (prefixWord ++ tailWord_2505784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505784).length < 2 ^ (prefixWord ++ tailWord_2505784).sum := by decide
  have hdescent : baseEnd_2505784 < baseStart_2505784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505788 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_2505788 : Nat := 118140960795 + 2505788 * 2 ^ 59
def prefixEnd_2505788 : Nat := 4983230072969 + 3 ^ 40 * 2505788 * 2
def baseEnd_2505788 : Nat := 428891220756182442208699

theorem tailTrace_2505788 : CollatzResearch.WordTrace tailWord_2505788 prefixEnd_2505788 428891220756182442208699 := by
  unfold tailWord_2505788
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696798322982752682155009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60929064430643670242873345 45696798322982752682155009)
  ·
    refine ⟨34272598742237064511616257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45696798322982752682155009 34272598742237064511616257)
    ·
      refine ⟨25704449056677798383712193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34272598742237064511616257 25704449056677798383712193)
      ·
        refine ⟨19278336792508348787784145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25704449056677798383712193 19278336792508348787784145)
        ·
          refine ⟨14458752594381261590838109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19278336792508348787784145 14458752594381261590838109)
          ·
            refine ⟨5422032222892973096564291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14458752594381261590838109 5422032222892973096564291)
            ·
              refine ⟨8133048334339459644846437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422032222892973096564291 8133048334339459644846437)
              ·
                refine ⟨1524946562688648683408707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8133048334339459644846437 1524946562688648683408707)
                ·
                  refine ⟨2287419844032973025113061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524946562688648683408707 2287419844032973025113061)
                  ·
                    refine ⟨428891220756182442208699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287419844032973025113061 428891220756182442208699)
                    ·
                      rfl

theorem cell23_2505788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_2505788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505788 prefixEnd_2505788 := by exact prefixLift 2505788
  have htrace : WordTrace (prefixWord ++ tailWord_2505788) baseStart_2505788 baseEnd_2505788 := by
    simpa [prefixWord, tailWord_2505788, baseEnd_2505788] using wordTrace_append hprefix tailTrace_2505788
  have hstable : (prefixWord ++ tailWord_2505788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505788).length < 2 ^ (prefixWord ++ tailWord_2505788).sum := by decide
  have hdescent : baseEnd_2505788 < baseStart_2505788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505822 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2505822 : Nat := 118140960795 + 2505822 * 2 ^ 59
def prefixEnd_2505822 : Nat := 4983230072969 + 3 ^ 40 * 2505822 * 2
def baseEnd_2505822 : Nat := 428897040203600064533647

theorem tailTrace_2505822 : CollatzResearch.WordTrace tailWord_2505822 prefixEnd_2505822 428897040203600064533647 := by
  unfold tailWord_2505822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424354590980291146380965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60929891151894886114031813 11424354590980291146380965)
  ·
    refine ⟨2142066485808804589946431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11424354590980291146380965 2142066485808804589946431)
    ·
      refine ⟨3213099728713206884919647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142066485808804589946431 3213099728713206884919647)
      ·
        refine ⟨4819649593069810327379471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3213099728713206884919647 4819649593069810327379471)
        ·
          refine ⟨7229474389604715491069207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819649593069810327379471 7229474389604715491069207)
          ·
            refine ⟨10844211584407073236603811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229474389604715491069207 10844211584407073236603811)
            ·
              refine ⟨16266317376610609854905717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10844211584407073236603811 16266317376610609854905717)
              ·
                refine ⟨1524967254057244673897411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16266317376610609854905717 1524967254057244673897411)
                ·
                  refine ⟨2287450881085867010846117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524967254057244673897411 2287450881085867010846117)
                  ·
                    refine ⟨428897040203600064533647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287450881085867010846117 428897040203600064533647)
                    ·
                      rfl

theorem cell23_2505822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2505822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505822 prefixEnd_2505822 := by exact prefixLift 2505822
  have htrace : WordTrace (prefixWord ++ tailWord_2505822) baseStart_2505822 baseEnd_2505822 := by
    simpa [prefixWord, tailWord_2505822, baseEnd_2505822] using wordTrace_append hprefix tailTrace_2505822
  have hstable : (prefixWord ++ tailWord_2505822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505822).length < 2 ^ (prefixWord ++ tailWord_2505822).sum := by decide
  have hdescent : baseEnd_2505822 < baseStart_2505822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505831 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2505831 : Nat := 118140960795 + 2505831 * 2 ^ 59
def prefixEnd_2505831 : Nat := 4983230072969 + 3 ^ 40 * 2505831 * 2
def baseEnd_2505831 : Nat := 428898580645563552796133

theorem tailTrace_2505831 : CollatzResearch.WordTrace tailWord_2505831 prefixEnd_2505831 428898580645563552796133 := by
  unfold tailWord_2505831
  simp only [CollatzResearch.WordTrace]
  refine ⟨91395164984809723708125347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60930109989873149138750231 91395164984809723708125347)
  ·
    refine ⟨137092747477214585562188021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91395164984809723708125347 137092747477214585562188021)
    ·
      refine ⟨12852445075988867396455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137092747477214585562188021 12852445075988867396455127)
      ·
        refine ⟨19278667613983301094682691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12852445075988867396455127 19278667613983301094682691)
        ·
          refine ⟨28918001420974951642024037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19278667613983301094682691 28918001420974951642024037)
          ·
            refine ⟨5422125266432803432879507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28918001420974951642024037 5422125266432803432879507)
            ·
              refine ⟨8133187899649205149319261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422125266432803432879507 8133187899649205149319261)
              ·
                refine ⟨3049945462368451930994723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8133187899649205149319261 3049945462368451930994723)
                ·
                  refine ⟨4574918193552677896492085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049945462368451930994723 4574918193552677896492085)
                  ·
                    refine ⟨428898580645563552796133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4574918193552677896492085 428898580645563552796133)
                    ·
                      rfl

theorem cell23_2505831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2505831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505831 prefixEnd_2505831 := by exact prefixLift 2505831
  have htrace : WordTrace (prefixWord ++ tailWord_2505831) baseStart_2505831 baseEnd_2505831 := by
    simpa [prefixWord, tailWord_2505831, baseEnd_2505831] using wordTrace_append hprefix tailTrace_2505831
  have hstable : (prefixWord ++ tailWord_2505831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505831).length < 2 ^ (prefixWord ++ tailWord_2505831).sum := by decide
  have hdescent : baseEnd_2505831 < baseStart_2505831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505922 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2505922 : Nat := 118140960795 + 2505922 * 2 ^ 59
def prefixEnd_2505922 : Nat := 4983230072969 + 3 ^ 40 * 2505922 * 2
def baseEnd_2505922 : Nat := 1286742468676249802350481

theorem tailTrace_2505922 : CollatzResearch.WordTrace tailWord_2505922 prefixEnd_2505922 1286742468676249802350481 := by
  unfold tailWord_2505922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22849621006870011562422005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60932322684986697499792013 22849621006870011562422005)
  ·
    refine ⟨2142151969394063583977063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22849621006870011562422005 2142151969394063583977063)
    ·
      refine ⟨3213227954091095375965595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142151969394063583977063 3213227954091095375965595)
      ·
        refine ⟨4819841931136643063948393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3213227954091095375965595 4819841931136643063948393)
        ·
          refine ⟨3614881448352482297961295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4819841931136643063948393 3614881448352482297961295)
          ·
            refine ⟨5422322172528723446941943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614881448352482297961295 5422322172528723446941943)
            ·
              refine ⟨8133483258793085170412915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422322172528723446941943 8133483258793085170412915)
              ·
                refine ⟨12200224888189627755619373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133483258793085170412915 12200224888189627755619373)
                ·
                  refine ⟨4575084333071110408357265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12200224888189627755619373 4575084333071110408357265)
                  ·
                    refine ⟨3431313249803332806267949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4575084333071110408357265 3431313249803332806267949)
                    ·
                      refine ⟨1286742468676249802350481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3431313249803332806267949 1286742468676249802350481)
                      ·
                        rfl

theorem cell23_2505922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2505922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505922 prefixEnd_2505922 := by exact prefixLift 2505922
  have htrace : WordTrace (prefixWord ++ tailWord_2505922) baseStart_2505922 baseEnd_2505922 := by
    simpa [prefixWord, tailWord_2505922, baseEnd_2505922] using wordTrace_append hprefix tailTrace_2505922
  have hstable : (prefixWord ++ tailWord_2505922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505922).length < 2 ^ (prefixWord ++ tailWord_2505922).sum := by decide
  have hdescent : baseEnd_2505922 < baseStart_2505922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505971 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_2505971 : Nat := 118140960795 + 2505971 * 2 ^ 59
def prefixEnd_2505971 : Nat := 4983230072969 + 3 ^ 40 * 2505971 * 2
def baseEnd_2505971 : Nat := 1286767629228320110637755

theorem tailTrace_2505971 : CollatzResearch.WordTrace tailWord_2505971 prefixEnd_2505971 1286767629228320110637755 := by
  unfold tailWord_2505971
  simp only [CollatzResearch.WordTrace]
  refine ⟨91400271204302527618221767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60933514136201685078814511 91400271204302527618221767)
  ·
    refine ⟨137100406806453791427332651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91400271204302527618221767 137100406806453791427332651)
    ·
      refine ⟨205650610209680687140998977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137100406806453791427332651 205650610209680687140998977)
      ·
        refine ⟨154237957657260515355749233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205650610209680687140998977 154237957657260515355749233)
        ·
          refine ⟨115678468242945386516811925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154237957657260515355749233 115678468242945386516811925)
          ·
            refine ⟨5422428198888064992975559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115678468242945386516811925 5422428198888064992975559)
            ·
              refine ⟨8133642298332097489463339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422428198888064992975559 8133642298332097489463339)
              ·
                refine ⟨12200463447498146234195009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133642298332097489463339 12200463447498146234195009)
                ·
                  refine ⟨9150347585623609675646257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12200463447498146234195009 9150347585623609675646257)
                  ·
                    refine ⟨6862760689217707256734693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9150347585623609675646257 6862760689217707256734693)
                    ·
                      refine ⟨1286767629228320110637755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6862760689217707256734693 1286767629228320110637755)
                      ·
                        rfl

theorem cell23_2505971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_2505971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505971 prefixEnd_2505971 := by exact prefixLift 2505971
  have htrace : WordTrace (prefixWord ++ tailWord_2505971) baseStart_2505971 baseEnd_2505971 := by
    simpa [prefixWord, tailWord_2505971, baseEnd_2505971] using wordTrace_append hprefix tailTrace_2505971
  have hstable : (prefixWord ++ tailWord_2505971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505971).length < 2 ^ (prefixWord ++ tailWord_2505971).sum := by decide
  have hdescent : baseEnd_2505971 < baseStart_2505971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505998 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_2505998 : Nat := 118140960795 + 2505998 * 2 ^ 59
def prefixEnd_2505998 : Nat := 4983230072969 + 3 ^ 40 * 2505998 * 2
def baseEnd_2505998 : Nat := 142975721467332389444459

theorem tailTrace_2505998 : CollatzResearch.WordTrace tailWord_2505998 prefixEnd_2505998 142975721467332389444459 := by
  unfold tailWord_2505998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425156996900588903681831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60934170650136474152969765 11425156996900588903681831)
  ·
    refine ⟨17137735495350883355522747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11425156996900588903681831 17137735495350883355522747)
    ·
      refine ⟨25706603243026325033284121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17137735495350883355522747 25706603243026325033284121)
      ·
        refine ⟨19279952432269743774963091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25706603243026325033284121 19279952432269743774963091)
        ·
          refine ⟨28919928648404615662444637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19279952432269743774963091 28919928648404615662444637)
          ·
            refine ⟨10844973243151730873416739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28919928648404615662444637 10844973243151730873416739)
            ·
              refine ⟨16267459864727596310125109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10844973243151730873416739 16267459864727596310125109)
              ·
                refine ⟨1525074362318212154074229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16267459864727596310125109 1525074362318212154074229)
                ·
                  refine ⟨142975721467332389444459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525074362318212154074229 142975721467332389444459)
                  ·
                    rfl

theorem cell23_2505998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_2505998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2505998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2505998 prefixEnd_2505998 := by exact prefixLift 2505998
  have htrace : WordTrace (prefixWord ++ tailWord_2505998) baseStart_2505998 baseEnd_2505998 := by
    simpa [prefixWord, tailWord_2505998, baseEnd_2505998] using wordTrace_append hprefix tailTrace_2505998
  have hstable : (prefixWord ++ tailWord_2505998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505998).length < 2 ^ (prefixWord ++ tailWord_2505998).sum := by decide
  have hdescent : baseEnd_2505998 < baseStart_2505998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506071 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 8]
def baseStart_2506071 : Nat := 118140960795 + 2506071 * 2 ^ 59
def prefixEnd_2506071 : Nat := 4983230072969 + 3 ^ 40 * 2506071 * 2
def baseEnd_2506071 : Nat := 142979886365974413265255

theorem tailTrace_2506071 : CollatzResearch.WordTrace tailWord_2506071 prefixEnd_2506071 142979886365974413265255 := by
  unfold tailWord_2506071
  simp only [CollatzResearch.WordTrace]
  refine ⟨91403918503940244696862067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60935945669293496464574711 91403918503940244696862067)
  ·
    refine ⟨137105877755910367045293101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91403918503940244696862067 137105877755910367045293101)
    ·
      refine ⟨51414704158466387641984913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137105877755910367045293101 51414704158466387641984913)
      ·
        refine ⟨38561028118849790731488685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51414704158466387641984913 38561028118849790731488685)
        ·
          refine ⟨14460385544568671524308257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38561028118849790731488685 14460385544568671524308257)
          ·
            refine ⟨10845289158426503643231193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14460385544568671524308257 10845289158426503643231193)
            ·
              refine ⟨8133966868819877732423395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10845289158426503643231193 8133966868819877732423395)
              ·
                refine ⟨12200950303229816598635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133966868819877732423395 12200950303229816598635093)
                ·
                  refine ⟨142979886365974413265255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12200950303229816598635093 142979886365974413265255)
                  ·
                    rfl

theorem cell23_2506071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 8].length) (baseStart_2506071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506071 prefixEnd_2506071 := by exact prefixLift 2506071
  have htrace : WordTrace (prefixWord ++ tailWord_2506071) baseStart_2506071 baseEnd_2506071 := by
    simpa [prefixWord, tailWord_2506071, baseEnd_2506071] using wordTrace_append hprefix tailTrace_2506071
  have hstable : (prefixWord ++ tailWord_2506071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506071).length < 2 ^ (prefixWord ++ tailWord_2506071).sum := by decide
  have hdescent : baseEnd_2506071 < baseStart_2506071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506126 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_2506126 : Nat := 118140960795 + 2506126 * 2 ^ 59
def prefixEnd_2506126 : Nat := 4983230072969 + 3 ^ 40 * 2506126 * 2
def baseEnd_2506126 : Nat := 428949072909922334733181

theorem tailTrace_2506126 : CollatzResearch.WordTrace tailWord_2506126 prefixEnd_2506126 428949072909922334733181 := by
  unfold tailWord_2506126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425740564842623636264279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60937283012493992726742821 11425740564842623636264279)
  ·
    refine ⟨17138610847263935454396419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11425740564842623636264279 17138610847263935454396419)
    ·
      refine ⟨25707916270895903181594629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17138610847263935454396419 25707916270895903181594629)
      ·
        refine ⟨4820234300792981846548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25707916270895903181594629 4820234300792981846548993)
        ·
          refine ⟨3615175725594736384911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4820234300792981846548993 3615175725594736384911745)
          ·
            refine ⟨2711381794196052288683809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615175725594736384911745 2711381794196052288683809)
            ·
              refine ⟨2033536345647039216512857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711381794196052288683809 2033536345647039216512857)
              ·
                refine ⟨1525152259235279412384643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033536345647039216512857 1525152259235279412384643)
                ·
                  refine ⟨2287728388852919118576965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525152259235279412384643 2287728388852919118576965)
                  ·
                    refine ⟨428949072909922334733181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287728388852919118576965 428949072909922334733181)
                    ·
                      rfl

theorem cell23_2506126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_2506126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506126 prefixEnd_2506126 := by exact prefixLift 2506126
  have htrace : WordTrace (prefixWord ++ tailWord_2506126) baseStart_2506126 baseEnd_2506126 := by
    simpa [prefixWord, tailWord_2506126, baseEnd_2506126] using wordTrace_append hprefix tailTrace_2506126
  have hstable : (prefixWord ++ tailWord_2506126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506126).length < 2 ^ (prefixWord ++ tailWord_2506126).sum := by decide
  have hdescent : baseEnd_2506126 < baseStart_2506126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506138 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2506138 : Nat := 118140960795 + 2506138 * 2 ^ 59
def prefixEnd_2506138 : Nat := 4983230072969 + 3 ^ 40 * 2506138 * 2
def baseEnd_2506138 : Nat := 1286853380497620957249487

theorem tailTrace_2506138 : CollatzResearch.WordTrace tailWord_2506138 prefixEnd_2506138 1286853380497620957249487 := by
  unfold tailWord_2506138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851590548674378784887767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60937574796465010093034045 22851590548674378784887767)
  ·
    refine ⟨34277385823011568177331651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22851590548674378784887767 34277385823011568177331651)
    ·
      refine ⟨51416078734517352265997477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34277385823011568177331651 51416078734517352265997477)
      ·
        refine ⟨9640514762722003549874527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51416078734517352265997477 9640514762722003549874527)
        ·
          refine ⟨14460772144083005324811791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640514762722003549874527 14460772144083005324811791)
          ·
            refine ⟨21691158216124507987217687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14460772144083005324811791 21691158216124507987217687)
            ·
              refine ⟨32536737324186761980826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21691158216124507987217687 32536737324186761980826531)
              ·
                refine ⟨48805105986280142971239797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32536737324186761980826531 48805105986280142971239797)
                ·
                  refine ⟨4575478686213763403553731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48805105986280142971239797 4575478686213763403553731)
                  ·
                    refine ⟨6863218029320645105330597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575478686213763403553731 6863218029320645105330597)
                    ·
                      refine ⟨1286853380497620957249487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6863218029320645105330597 1286853380497620957249487)
                      ·
                        rfl

theorem cell23_2506138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2506138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506138 prefixEnd_2506138 := by exact prefixLift 2506138
  have htrace : WordTrace (prefixWord ++ tailWord_2506138) baseStart_2506138 baseEnd_2506138 := by
    simpa [prefixWord, tailWord_2506138, baseEnd_2506138] using wordTrace_append hprefix tailTrace_2506138
  have hstable : (prefixWord ++ tailWord_2506138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506138).length < 2 ^ (prefixWord ++ tailWord_2506138).sum := by decide
  have hdescent : baseEnd_2506138 < baseStart_2506138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506148 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_2506148 : Nat := 118140960795 + 2506148 * 2 ^ 59
def prefixEnd_2506148 : Nat := 4983230072969 + 3 ^ 40 * 2506148 * 2
def baseEnd_2506148 : Nat := 428952838434721972708147

theorem tailTrace_2506148 : CollatzResearch.WordTrace tailWord_2506148 prefixEnd_2506148 428952838434721972708147 := by
  unfold tailWord_2506148
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703363462330643423707549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60937817949774191231610065 45703363462330643423707549)
  ·
    refine ⟨17138761298373991283890331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45703363462330643423707549 17138761298373991283890331)
    ·
      refine ⟨25708141947560986925835497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17138761298373991283890331 25708141947560986925835497)
      ·
        refine ⟨19281106460670740194376623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25708141947560986925835497 19281106460670740194376623)
        ·
          refine ⟨28921659691006110291564935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19281106460670740194376623 28921659691006110291564935)
          ·
            refine ⟨43382489536509165437347403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28921659691006110291564935 43382489536509165437347403)
            ·
              refine ⟨65073734304763748156021105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43382489536509165437347403 65073734304763748156021105)
              ·
                refine ⟨48805300728572811117015829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65073734304763748156021105 48805300728572811117015829)
                ·
                  refine ⟨2287748471651850521110117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48805300728572811117015829 2287748471651850521110117)
                  ·
                    refine ⟨428952838434721972708147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287748471651850521110117 428952838434721972708147)
                    ·
                      rfl

theorem cell23_2506148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_2506148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506148 prefixEnd_2506148 := by exact prefixLift 2506148
  have htrace : WordTrace (prefixWord ++ tailWord_2506148) baseStart_2506148 baseEnd_2506148 := by
    simpa [prefixWord, tailWord_2506148, baseEnd_2506148] using wordTrace_append hprefix tailTrace_2506148
  have hstable : (prefixWord ++ tailWord_2506148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506148).length < 2 ^ (prefixWord ++ tailWord_2506148).sum := by decide
  have hdescent : baseEnd_2506148 < baseStart_2506148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506168 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2506168 : Nat := 118140960795 + 2506168 * 2 ^ 59
def prefixEnd_2506168 : Nat := 4983230072969 + 3 ^ 40 * 2506168 * 2
def baseEnd_2506168 : Nat := 1286868784917255839874349

theorem tailTrace_2506168 : CollatzResearch.WordTrace tailWord_2506168 prefixEnd_2506168 1286868784917255839874349 := by
  unfold tailWord_2506168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703728192294415131571579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60938304256392553508762105 45703728192294415131571579)
  ·
    refine ⟨68555592288441622697357369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45703728192294415131571579 68555592288441622697357369)
    ·
      refine ⟨51416694216331217023018027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68555592288441622697357369 51416694216331217023018027)
      ·
        refine ⟨77125041324496825534527041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51416694216331217023018027 77125041324496825534527041)
        ·
          refine ⟨57843780993372619150895281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77125041324496825534527041 57843780993372619150895281)
          ·
            refine ⟨43382835745029464363171461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57843780993372619150895281 43382835745029464363171461)
            ·
              refine ⟨8134281702193024568094649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43382835745029464363171461 8134281702193024568094649)
              ·
                refine ⟨6100711276644768426070987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8134281702193024568094649 6100711276644768426070987)
                ·
                  refine ⟨9151066914967152639106481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100711276644768426070987 9151066914967152639106481)
                  ·
                    refine ⟨6863300186225364479329861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9151066914967152639106481 6863300186225364479329861)
                    ·
                      refine ⟨1286868784917255839874349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6863300186225364479329861 1286868784917255839874349)
                      ·
                        rfl

theorem cell23_2506168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2506168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506168 prefixEnd_2506168 := by exact prefixLift 2506168
  have htrace : WordTrace (prefixWord ++ tailWord_2506168) baseStart_2506168 baseEnd_2506168 := by
    simpa [prefixWord, tailWord_2506168, baseEnd_2506168] using wordTrace_append hprefix tailTrace_2506168
  have hstable : (prefixWord ++ tailWord_2506168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506168).length < 2 ^ (prefixWord ++ tailWord_2506168).sum := by decide
  have hdescent : baseEnd_2506168 < baseStart_2506168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506169 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_2506169 : Nat := 118140960795 + 2506169 * 2 ^ 59
def prefixEnd_2506169 : Nat := 4983230072969 + 3 ^ 40 * 2506169 * 2
def baseEnd_2506169 : Nat := 428956432799303445320615

theorem tailTrace_2506169 : CollatzResearch.WordTrace tailWord_2506169 prefixEnd_2506169 428956432799303445320615 := by
  unfold tailWord_2506169
  simp only [CollatzResearch.WordTrace]
  refine ⟨91407492857585207433929561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60938328571723471622619707 91407492857585207433929561)
  ·
    refine ⟨68555619643188905575447171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91407492857585207433929561 68555619643188905575447171)
    ·
      refine ⟨102833429464783358363170757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68555619643188905575447171 102833429464783358363170757)
      ·
        refine ⟨19281268024646879693094517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102833429464783358363170757 19281268024646879693094517)
        ·
          refine ⟨1807618877310644971227611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19281268024646879693094517 1807618877310644971227611)
          ·
            refine ⟨2711428315965967456841417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807618877310644971227611 2711428315965967456841417)
            ·
              refine ⟨2033571236974475592631063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711428315965967456841417 2033571236974475592631063)
              ·
                refine ⟨3050356855461713388946595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033571236974475592631063 3050356855461713388946595)
                ·
                  refine ⟨4575535283192570083419893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050356855461713388946595 4575535283192570083419893)
                  ·
                    refine ⟨428956432799303445320615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4575535283192570083419893 428956432799303445320615)
                    ·
                      rfl

theorem cell23_2506169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_2506169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506169 prefixEnd_2506169 := by exact prefixLift 2506169
  have htrace : WordTrace (prefixWord ++ tailWord_2506169) baseStart_2506169 baseEnd_2506169 := by
    simpa [prefixWord, tailWord_2506169, baseEnd_2506169] using wordTrace_append hprefix tailTrace_2506169
  have hstable : (prefixWord ++ tailWord_2506169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506169).length < 2 ^ (prefixWord ++ tailWord_2506169).sum := by decide
  have hdescent : baseEnd_2506169 < baseStart_2506169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506172 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2506172 : Nat := 118140960795 + 2506172 * 2 ^ 59
def prefixEnd_2506172 : Nat := 4983230072969 + 3 ^ 40 * 2506172 * 2
def baseEnd_2506172 : Nat := 1286870838839873824224331

theorem tailTrace_2506172 : CollatzResearch.WordTrace tailWord_2506172 prefixEnd_2506172 1286870838839873824224331 := by
  unfold tailWord_2506172
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703801138287169473144385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60938401517716225964192513 45703801138287169473144385)
  ·
    refine ⟨34277850853715377104858289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45703801138287169473144385 34277850853715377104858289)
    ·
      refine ⟨25708388140286532828643717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34277850853715377104858289 25708388140286532828643717)
      ·
        refine ⟨4820322776303724905370697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25708388140286532828643717 4820322776303724905370697)
        ·
          refine ⟨3615242082227793679028023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4820322776303724905370697 3615242082227793679028023)
          ·
            refine ⟨5422863123341690518542035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615242082227793679028023 5422863123341690518542035)
            ·
              refine ⟨8134294685012535777813053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422863123341690518542035 8134294685012535777813053)
              ·
                refine ⟨3050360506879700916679895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134294685012535777813053 3050360506879700916679895)
                ·
                  refine ⟨4575540760319551375019843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050360506879700916679895 4575540760319551375019843)
                  ·
                    refine ⟨6863311140479327062529765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575540760319551375019843 6863311140479327062529765)
                    ·
                      refine ⟨1286870838839873824224331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6863311140479327062529765 1286870838839873824224331)
                      ·
                        rfl

theorem cell23_2506172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2506172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506172 prefixEnd_2506172 := by exact prefixLift 2506172
  have htrace : WordTrace (prefixWord ++ tailWord_2506172) baseStart_2506172 baseEnd_2506172 := by
    simpa [prefixWord, tailWord_2506172, baseEnd_2506172] using wordTrace_append hprefix tailTrace_2506172
  have hstable : (prefixWord ++ tailWord_2506172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506172).length < 2 ^ (prefixWord ++ tailWord_2506172).sum := by decide
  have hdescent : baseEnd_2506172 < baseStart_2506172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506191 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 9]
def baseStart_2506191 : Nat := 118140960795 + 2506191 * 2 ^ 59
def prefixEnd_2506191 : Nat := 4983230072969 + 3 ^ 40 * 2506191 * 2
def baseEnd_2506191 : Nat := 428960198324103083295581

theorem tailTrace_2506191 : CollatzResearch.WordTrace tailWord_2506191 prefixEnd_2506191 428960198324103083295581 := by
  unfold tailWord_2506191
  simp only [CollatzResearch.WordTrace]
  refine ⟨91408295263505505191230427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60938863509003670127486951 91408295263505505191230427)
  ·
    refine ⟨137112442895258257786845641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91408295263505505191230427 137112442895258257786845641)
    ·
      refine ⟨102834332171443693340134231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137112442895258257786845641 102834332171443693340134231)
      ·
        refine ⟨154251498257165540010201347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102834332171443693340134231 154251498257165540010201347)
        ·
          refine ⟨231377247385748310015302021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154251498257165540010201347 231377247385748310015302021)
          ·
            refine ⟨43383233884827808127869129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231377247385748310015302021 43383233884827808127869129)
            ·
              refine ⟨32537425413620856095901847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43383233884827808127869129 32537425413620856095901847)
              ·
                refine ⟨48806138120431284143852771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32537425413620856095901847 48806138120431284143852771)
                ·
                  refine ⟨73209207180646926215779157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48806138120431284143852771 73209207180646926215779157)
                  ·
                    refine ⟨428960198324103083295581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73209207180646926215779157 428960198324103083295581)
                    ·
                      rfl

theorem cell23_2506191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_2506191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506191 prefixEnd_2506191 := by exact prefixLift 2506191
  have htrace : WordTrace (prefixWord ++ tailWord_2506191) baseStart_2506191 baseEnd_2506191 := by
    simpa [prefixWord, tailWord_2506191, baseEnd_2506191] using wordTrace_append hprefix tailTrace_2506191
  have hstable : (prefixWord ++ tailWord_2506191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506191).length < 2 ^ (prefixWord ++ tailWord_2506191).sum := by decide
  have hdescent : baseEnd_2506191 < baseStart_2506191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506232 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_2506232 : Nat := 118140960795 + 2506232 * 2 ^ 59
def prefixEnd_2506232 : Nat := 4983230072969 + 3 ^ 40 * 2506232 * 2
def baseEnd_2506232 : Nat := 1286901647679143589474055

theorem tailTrace_2506232 : CollatzResearch.WordTrace tailWord_2506232 prefixEnd_2506232 1286901647679143589474055 := by
  unfold tailWord_2506232
  simp only [CollatzResearch.WordTrace]
  refine ⟨45704895328178484596736475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60939860437571312795648633 45704895328178484596736475)
  ·
    refine ⟨68557342992267726895104713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45704895328178484596736475 68557342992267726895104713)
    ·
      refine ⟨51418007244200795171328535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68557342992267726895104713 51418007244200795171328535)
      ·
        refine ⟨77127010866301192756992803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51418007244200795171328535 77127010866301192756992803)
        ·
          refine ⟨115690516299451789135489205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77127010866301192756992803 115690516299451789135489205)
          ·
            refine ⟨10845985903073605231452113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115690516299451789135489205 10845985903073605231452113)
            ·
              refine ⟨8134489427305203923589085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10845985903073605231452113 8134489427305203923589085)
              ·
                refine ⟨3050433535239451471345907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134489427305203923589085 3050433535239451471345907)
                ·
                  refine ⟨4575650302859177207018861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050433535239451471345907 4575650302859177207018861)
                  ·
                    refine ⟨1715868863572191452632073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4575650302859177207018861 1715868863572191452632073)
                    ·
                      refine ⟨1286901647679143589474055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1715868863572191452632073 1286901647679143589474055)
                      ·
                        rfl

theorem cell23_2506232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_2506232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506232 prefixEnd_2506232 := by exact prefixLift 2506232
  have htrace : WordTrace (prefixWord ++ tailWord_2506232) baseStart_2506232 baseEnd_2506232 := by
    simpa [prefixWord, tailWord_2506232, baseEnd_2506232] using wordTrace_append hprefix tailTrace_2506232
  have hstable : (prefixWord ++ tailWord_2506232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506232).length < 2 ^ (prefixWord ++ tailWord_2506232).sum := by decide
  have hdescent : baseEnd_2506232 < baseStart_2506232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506268 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 9]
def baseStart_2506268 : Nat := 118140960795 + 2506268 * 2 ^ 59
def prefixEnd_2506268 : Nat := 4983230072969 + 3 ^ 40 * 2506268 * 2
def baseEnd_2506268 : Nat := 142991125886967272069321

theorem tailTrace_2506268 : CollatzResearch.WordTrace tailWord_2506268 prefixEnd_2506268 142991125886967272069321 := by
  unfold tailWord_2506268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45705551842113273670891729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60940735789484364894522305 45705551842113273670891729)
  ·
    refine ⟨34279163881584955253168797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45705551842113273670891729 34279163881584955253168797)
    ·
      refine ⟨12854686455594358219938299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34279163881584955253168797 12854686455594358219938299)
      ·
        refine ⟨19282029683391537329907449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854686455594358219938299 19282029683391537329907449)
        ·
          refine ⟨14461522262543652997430587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19282029683391537329907449 14461522262543652997430587)
          ·
            refine ⟨21692283393815479496145881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14461522262543652997430587 21692283393815479496145881)
            ·
              refine ⟨16269212545361609622109411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21692283393815479496145881 16269212545361609622109411)
              ·
                refine ⟨24403818818042414433164117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16269212545361609622109411 24403818818042414433164117)
                ·
                  refine ⟨142991125886967272069321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24403818818042414433164117 142991125886967272069321)
                  ·
                    rfl

theorem cell23_2506268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_2506268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506268 prefixEnd_2506268 := by exact prefixLift 2506268
  have htrace : WordTrace (prefixWord ++ tailWord_2506268) baseStart_2506268 baseEnd_2506268 := by
    simpa [prefixWord, tailWord_2506268, baseEnd_2506268] using wordTrace_append hprefix tailTrace_2506268
  have hstable : (prefixWord ++ tailWord_2506268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506268).length < 2 ^ (prefixWord ++ tailWord_2506268).sum := by decide
  have hdescent : baseEnd_2506268 < baseStart_2506268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506332 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2506332 : Nat := 118140960795 + 2506332 * 2 ^ 59
def prefixEnd_2506332 : Nat := 4983230072969 + 3 ^ 40 * 2506332 * 2
def baseEnd_2506332 : Nat := 428984331914864399407865

theorem tailTrace_2506332 : CollatzResearch.WordTrace tailWord_2506332 prefixEnd_2506332 428984331914864399407865 := by
  unfold tailWord_2506332
  simp only [CollatzResearch.WordTrace]
  refine ⟨45706718977997343136056625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60942291970663124181408833 45706718977997343136056625)
  ·
    refine ⟨34280039233498007352042469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45706718977997343136056625 34280039233498007352042469)
    ·
      refine ⟨6427507356280876378507963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34280039233498007352042469 6427507356280876378507963)
      ·
        refine ⟨9641261034421314567761945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427507356280876378507963 9641261034421314567761945)
        ·
          refine ⟨7230945775815985925821459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9641261034421314567761945 7230945775815985925821459)
          ·
            refine ⟨10846418663723978888732189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7230945775815985925821459 10846418663723978888732189)
            ·
              refine ⟨4067406998896492083274571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10846418663723978888732189 4067406998896492083274571)
              ·
                refine ⟨6101110498344738124911857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067406998896492083274571 6101110498344738124911857)
                ·
                  refine ⟨4575832873758553593683893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6101110498344738124911857 4575832873758553593683893)
                  ·
                    refine ⟨428984331914864399407865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4575832873758553593683893 428984331914864399407865)
                    ·
                      rfl

theorem cell23_2506332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2506332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506332 prefixEnd_2506332 := by exact prefixLift 2506332
  have htrace : WordTrace (prefixWord ++ tailWord_2506332) baseStart_2506332 baseEnd_2506332 := by
    simpa [prefixWord, tailWord_2506332, baseEnd_2506332] using wordTrace_append hprefix tailTrace_2506332
  have hstable : (prefixWord ++ tailWord_2506332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506332).length < 2 ^ (prefixWord ++ tailWord_2506332).sum := by decide
  have hdescent : baseEnd_2506332 < baseStart_2506332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506352 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2]
def baseStart_2506352 : Nat := 118140960795 + 2506352 * 2 ^ 59
def prefixEnd_2506352 : Nat := 4983230072969 + 3 ^ 40 * 2506352 * 2
def baseEnd_2506352 : Nat := 1286963265357683119973503

theorem tailTrace_2506352 : CollatzResearch.WordTrace tailWord_2506352 prefixEnd_2506352 1286963265357683119973503 := by
  unfold tailWord_2506352
  simp only [CollatzResearch.WordTrace]
  refine ⟨45707083707961114843920655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60942778277281486458560873 45707083707961114843920655)
  ·
    refine ⟨68560625561941672265880983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45707083707961114843920655 68560625561941672265880983)
    ·
      refine ⟨102840938342912508398821475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68560625561941672265880983 102840938342912508398821475)
      ·
        refine ⟨154261407514368762598232213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102840938342912508398821475 154261407514368762598232213)
        ·
          refine ⟨7231003477236035746792135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154261407514368762598232213 7231003477236035746792135)
          ·
            refine ⟨10846505215854053620188203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231003477236035746792135 10846505215854053620188203)
            ·
              refine ⟨16269757823781080430282305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10846505215854053620188203 16269757823781080430282305)
              ·
                refine ⟨12202318367835810322711729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16269757823781080430282305 12202318367835810322711729)
                ·
                  refine ⟨9151738775876857742033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12202318367835810322711729 9151738775876857742033797)
                  ·
                    refine ⟨1715951020476910826631337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9151738775876857742033797 1715951020476910826631337)
                    ·
                      refine ⟨1286963265357683119973503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1715951020476910826631337 1286963265357683119973503)
                      ·
                        rfl

theorem cell23_2506352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2].length) (baseStart_2506352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506352 prefixEnd_2506352 := by exact prefixLift 2506352
  have htrace : WordTrace (prefixWord ++ tailWord_2506352) baseStart_2506352 baseEnd_2506352 := by
    simpa [prefixWord, tailWord_2506352, baseEnd_2506352] using wordTrace_append hprefix tailTrace_2506352
  have hstable : (prefixWord ++ tailWord_2506352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506352).length < 2 ^ (prefixWord ++ tailWord_2506352).sum := by decide
  have hdescent : baseEnd_2506352 < baseStart_2506352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506452 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_2506452 : Nat := 118140960795 + 2506452 * 2 ^ 59
def prefixEnd_2506452 : Nat := 4983230072969 + 3 ^ 40 * 2506452 * 2
def baseEnd_2506452 : Nat := 429004871141044242907681

theorem tailTrace_2506452 : CollatzResearch.WordTrace tailWord_2506452 prefixEnd_2506452 429004871141044242907681 := by
  unfold tailWord_2506452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45708907357779973383240805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60945209810373297844321073 45708907357779973383240805)
  ·
    refine ⟨8570420129583745009357651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45708907357779973383240805 8570420129583745009357651)
    ·
      refine ⟨12855630194375617514036477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570420129583745009357651 12855630194375617514036477)
      ·
        refine ⟨4820861322890856567763679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12855630194375617514036477 4820861322890856567763679)
        ·
          refine ⟨7231291984336284851645519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820861322890856567763679 7231291984336284851645519)
          ·
            refine ⟨10846937976504427277468279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231291984336284851645519 10846937976504427277468279)
            ·
              refine ⟨16270406964756640916202419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10846937976504427277468279 16270406964756640916202419)
              ·
                refine ⟨24405610447134961374303629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16270406964756640916202419 24405610447134961374303629)
                ·
                  refine ⟨9152103917675610515363861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24405610447134961374303629 9152103917675610515363861)
                  ·
                    refine ⟨429004871141044242907681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9152103917675610515363861 429004871141044242907681)
                    ·
                      rfl

theorem cell23_2506452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_2506452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506452 prefixEnd_2506452 := by exact prefixLift 2506452
  have htrace : WordTrace (prefixWord ++ tailWord_2506452) baseStart_2506452 baseEnd_2506452 := by
    simpa [prefixWord, tailWord_2506452, baseEnd_2506452] using wordTrace_append hprefix tailTrace_2506452
  have hstable : (prefixWord ++ tailWord_2506452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506452).length < 2 ^ (prefixWord ++ tailWord_2506452).sum := by decide
  have hdescent : baseEnd_2506452 < baseStart_2506452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506465 : List Nat := [1, 2, 3, 1, 5, 11]
def baseStart_2506465 : Nat := 118140960795 + 2506465 * 2 ^ 59
def prefixEnd_2506465 : Nat := 4983230072969 + 3 ^ 40 * 2506465 * 2
def baseEnd_2506465 : Nat := 5296383903998523365681

theorem tailTrace_2506465 : CollatzResearch.WordTrace tailWord_2506465 prefixEnd_2506465 5296383903998523365681 := by
  unfold tailWord_2506465
  simp only [CollatzResearch.WordTrace]
  refine ⟨91418288864512849986704849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60945525909675233324469899 91418288864512849986704849)
  ·
    refine ⟨68563716648384637490028637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91418288864512849986704849 68563716648384637490028637)
    ·
      refine ⟨25711393743144239058760739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68563716648384637490028637 25711393743144239058760739)
      ·
        refine ⟨38567090614716358588141109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25711393743144239058760739 38567090614716358588141109)
        ·
          refine ⟨3615664745129658617638229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38567090614716358588141109 3615664745129658617638229)
          ·
            refine ⟨5296383903998523365681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3615664745129658617638229 5296383903998523365681)
            ·
              rfl

theorem cell23_2506465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 11].length) (baseStart_2506465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506465 prefixEnd_2506465 := by exact prefixLift 2506465
  have htrace : WordTrace (prefixWord ++ tailWord_2506465) baseStart_2506465 baseEnd_2506465 := by
    simpa [prefixWord, tailWord_2506465, baseEnd_2506465] using wordTrace_append hprefix tailTrace_2506465
  have hstable : (prefixWord ++ tailWord_2506465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506465).length < 2 ^ (prefixWord ++ tailWord_2506465).sum := by decide
  have hdescent : baseEnd_2506465 < baseStart_2506465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506469 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_2506469 : Nat := 118140960795 + 2506469 * 2 ^ 59
def prefixEnd_2506469 : Nat := 4983230072969 + 3 ^ 40 * 2506469 * 2
def baseEnd_2506469 : Nat := 429007780864753054070155

theorem tailTrace_2506469 : CollatzResearch.WordTrace tailWord_2506469 prefixEnd_2506469 429007780864753054070155 := by
  unfold tailWord_2506469
  simp only [CollatzResearch.WordTrace]
  refine ⟨91418434756498358669850461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60945623170998905779900307 91418434756498358669850461)
  ·
    refine ⟨34281913033686884501193923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91418434756498358669850461 34281913033686884501193923)
    ·
      refine ⟨51422869550530326751790885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34281913033686884501193923 51422869550530326751790885)
      ·
        refine ⟨9641788040724436265960791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51422869550530326751790885 9641788040724436265960791)
        ·
          refine ⟨14462682061086654398941187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9641788040724436265960791 14462682061086654398941187)
          ·
            refine ⟨21694023091629981598411781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14462682061086654398941187 21694023091629981598411781)
            ·
              refine ⟨4067629329680621549702209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21694023091629981598411781 4067629329680621549702209)
              ·
                refine ⟨3050721997260466162276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067629329680621549702209 3050721997260466162276657)
                ·
                  refine ⟨2288041497945349621707493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3050721997260466162276657 2288041497945349621707493)
                  ·
                    refine ⟨429007780864753054070155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288041497945349621707493 429007780864753054070155)
                    ·
                      rfl

theorem cell23_2506469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_2506469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506469 prefixEnd_2506469 := by exact prefixLift 2506469
  have htrace : WordTrace (prefixWord ++ tailWord_2506469) baseStart_2506469 baseEnd_2506469 := by
    simpa [prefixWord, tailWord_2506469, baseEnd_2506469] using wordTrace_append hprefix tailTrace_2506469
  have hstable : (prefixWord ++ tailWord_2506469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506469).length < 2 ^ (prefixWord ++ tailWord_2506469).sum := by decide
  have hdescent : baseEnd_2506469 < baseStart_2506469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
