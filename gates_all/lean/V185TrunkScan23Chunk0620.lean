import V185TrunkScan23Chunk0619

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3666284 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_3666284 : Nat := 118140960795 + 3666284 * 2 ^ 59
def prefixEnd_3666284 : Nat := 4983230072969 + 3 ^ 40 * 3666284 * 2
def baseEnd_3666284 : Nat := 627521969296212960229691

theorem tailTrace_3666284 : CollatzResearch.WordTrace tailWord_3666284 prefixEnd_3666284 627521969296212960229691 := by
  unfold tailWord_3666284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66860181524843347150922953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89146908699791129534563937 66860181524843347150922953)
  ·
    refine ⟨50145136143632510363192215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66860181524843347150922953 50145136143632510363192215)
    ·
      refine ⟨75217704215448765544788323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50145136143632510363192215 75217704215448765544788323)
      ·
        refine ⟨112826556323173148317182485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75217704215448765544788323 112826556323173148317182485)
        ·
          refine ⟨5288744827648741327367929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112826556323173148317182485 5288744827648741327367929)
          ·
            refine ⟨3966558620736555995525947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5288744827648741327367929 3966558620736555995525947)
            ·
              refine ⟨5949837931104833993288921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966558620736555995525947 5949837931104833993288921)
              ·
                refine ⟨4462378448328625494966691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949837931104833993288921 4462378448328625494966691)
                ·
                  refine ⟨6693567672492938242450037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462378448328625494966691 6693567672492938242450037)
                  ·
                    refine ⟨627521969296212960229691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6693567672492938242450037 627521969296212960229691)
                    ·
                      rfl

theorem cell23_3666284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_3666284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666284 prefixEnd_3666284 := by exact prefixLift 3666284
  have htrace : WordTrace (prefixWord ++ tailWord_3666284) baseStart_3666284 baseEnd_3666284 := by
    simpa [prefixWord, tailWord_3666284, baseEnd_3666284] using wordTrace_append hprefix tailTrace_3666284
  have hstable : (prefixWord ++ tailWord_3666284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666284).length < 2 ^ (prefixWord ++ tailWord_3666284).sum := by decide
  have hdescent : baseEnd_3666284 < baseStart_3666284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666334 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3666334 : Nat := 118140960795 + 3666334 * 2 ^ 59
def prefixEnd_3666334 : Nat := 4983230072969 + 3 ^ 40 * 3666334 * 2
def baseEnd_3666334 : Nat := 1882591581921363685063843

theorem tailTrace_3666334 : CollatzResearch.WordTrace tailWord_3666334 prefixEnd_3666334 1882591581921363685063843 := by
  unfold tailWord_3666334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715273337438194105145757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89148124466337035227444037 16715273337438194105145757)
  ·
    refine ⟨6268227501539322789429659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16715273337438194105145757 6268227501539322789429659)
    ·
      refine ⟨9402341252308984184144489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6268227501539322789429659 9402341252308984184144489)
      ·
        refine ⟨7051755939231738138108367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9402341252308984184144489 7051755939231738138108367)
        ·
          refine ⟨10577633908847607207162551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051755939231738138108367 10577633908847607207162551)
          ·
            refine ⟨15866450863271410810743827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577633908847607207162551 15866450863271410810743827)
            ·
              refine ⟨23799676294907116216115741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15866450863271410810743827 23799676294907116216115741)
              ·
                refine ⟨8924878610590168581043403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23799676294907116216115741 8924878610590168581043403)
                ·
                  refine ⟨13387317915885252871565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924878610590168581043403 13387317915885252871565105)
                  ·
                    refine ⟨10040488436913939653673829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13387317915885252871565105 10040488436913939653673829)
                    ·
                      refine ⟨1882591581921363685063843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10040488436913939653673829 1882591581921363685063843)
                      ·
                        rfl

theorem cell23_3666334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3666334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666334 prefixEnd_3666334 := by exact prefixLift 3666334
  have htrace : WordTrace (prefixWord ++ tailWord_3666334) baseStart_3666334 baseEnd_3666334 := by
    simpa [prefixWord, tailWord_3666334, baseEnd_3666334] using wordTrace_append hprefix tailTrace_3666334
  have hstable : (prefixWord ++ tailWord_3666334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666334).length < 2 ^ (prefixWord ++ tailWord_3666334).sum := by decide
  have hdescent : baseEnd_3666334 < baseStart_3666334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666344 : List Nat := [2, 1, 6, 1, 1, 2, 3, 7]
def baseStart_3666344 : Nat := 118140960795 + 3666344 * 2 ^ 59
def prefixEnd_3666344 : Nat := 4983230072969 + 3 ^ 40 * 3666344 * 2
def baseEnd_3666344 : Nat := 69725804323255875775511

theorem tailTrace_3666344 : CollatzResearch.WordTrace tailWord_3666344 prefixEnd_3666344 69725804323255875775511 := by
  unfold tailWord_3666344
  simp only [CollatzResearch.WordTrace]
  refine ⟨66861275714734662274515043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89148367619646216366020057 66861275714734662274515043)
  ·
    refine ⟨100291913572101993411772565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66861275714734662274515043 100291913572101993411772565)
    ·
      refine ⟨4701183448692280941176839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100291913572101993411772565 4701183448692280941176839)
      ·
        refine ⟨7051775173038421411765259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701183448692280941176839 7051775173038421411765259)
        ·
          refine ⟨10577662759557632117647889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051775173038421411765259 10577662759557632117647889)
          ·
            refine ⟨7933247069668224088235917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577662759557632117647889 7933247069668224088235917)
            ·
              refine ⟨2974967651125584033088469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7933247069668224088235917 2974967651125584033088469)
              ·
                refine ⟨69725804323255875775511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2974967651125584033088469 69725804323255875775511)
                ·
                  rfl

theorem cell23_3666344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 7].length) (baseStart_3666344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666344 prefixEnd_3666344 := by exact prefixLift 3666344
  have htrace : WordTrace (prefixWord ++ tailWord_3666344) baseStart_3666344 baseEnd_3666344 := by
    simpa [prefixWord, tailWord_3666344, baseEnd_3666344] using wordTrace_append hprefix tailTrace_3666344
  have hstable : (prefixWord ++ tailWord_3666344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666344).length < 2 ^ (prefixWord ++ tailWord_3666344).sum := by decide
  have hdescent : baseEnd_3666344 < baseStart_3666344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666377 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 4, 2]
def baseStart_3666377 : Nat := 118140960795 + 3666377 * 2 ^ 59
def prefixEnd_3666377 : Nat := 4983230072969 + 3 ^ 40 * 3666377 * 2
def baseEnd_3666377 : Nat := 1882613661589507016826145

theorem tailTrace_3666377 : CollatzResearch.WordTrace tailWord_3666377 prefixEnd_3666377 1882613661589507016826145 := by
  unfold tailWord_3666377
  simp only [CollatzResearch.WordTrace]
  refine ⟨133723755038349771184981385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89149170025566514123320923 133723755038349771184981385)
  ·
    refine ⟨100292816278762328388736039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133723755038349771184981385 100292816278762328388736039)
    ·
      refine ⟨150439224418143492583104059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100292816278762328388736039 150439224418143492583104059)
      ·
        refine ⟨225658836627215238874656089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150439224418143492583104059 225658836627215238874656089)
        ·
          refine ⟨169244127470411429155992067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225658836627215238874656089 169244127470411429155992067)
          ·
            refine ⟨253866191205617143733988101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169244127470411429155992067 253866191205617143733988101)
            ·
              refine ⟨47599910851053214450122769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253866191205617143733988101 47599910851053214450122769)
              ·
                refine ⟨35699933138289910837592077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47599910851053214450122769 35699933138289910837592077)
                ·
                  refine ⟨13387474926858716564097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35699933138289910837592077 13387474926858716564097029)
                  ·
                    refine ⟨2510151548786009355768193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13387474926858716564097029 2510151548786009355768193)
                    ·
                      refine ⟨1882613661589507016826145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510151548786009355768193 1882613661589507016826145)
                      ·
                        rfl

theorem cell23_3666377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4, 2].length) (baseStart_3666377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666377 prefixEnd_3666377 := by exact prefixLift 3666377
  have htrace : WordTrace (prefixWord ++ tailWord_3666377) baseStart_3666377 baseEnd_3666377 := by
    simpa [prefixWord, tailWord_3666377, baseEnd_3666377] using wordTrace_append hprefix tailTrace_3666377
  have hstable : (prefixWord ++ tailWord_3666377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666377).length < 2 ^ (prefixWord ++ tailWord_3666377).sum := by decide
  have hdescent : baseEnd_3666377 < baseStart_3666377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666388 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3666388 : Nat := 118140960795 + 3666388 * 2 ^ 59
def prefixEnd_3666388 : Nat := 4983230072969 + 3 ^ 40 * 3666388 * 2
def baseEnd_3666388 : Nat := 1882619309876706473788595

theorem tailTrace_3666388 : CollatzResearch.WordTrace tailWord_3666388 prefixEnd_3666388 1882619309876706473788595 := by
  unfold tailWord_3666388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862078120654960031815909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89149437494206613375754545 66862078120654960031815909)
  ·
    refine ⟨12536639647622805005965483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66862078120654960031815909 12536639647622805005965483)
    ·
      refine ⟨18804959471434207508948225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536639647622805005965483 18804959471434207508948225)
      ·
        refine ⟨14103719603575655631711169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18804959471434207508948225 14103719603575655631711169)
        ·
          refine ⟨10577789702681741723783377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14103719603575655631711169 10577789702681741723783377)
          ·
            refine ⟨7933342277011306292837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577789702681741723783377 7933342277011306292837533)
            ·
              refine ⟨2975003353879239859814075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7933342277011306292837533 2975003353879239859814075)
              ·
                refine ⟨4462505030818859789721113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975003353879239859814075 4462505030818859789721113)
                ·
                  refine ⟨3346878773114144842290835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462505030818859789721113 3346878773114144842290835)
                  ·
                    refine ⟨5020318159671217263436253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346878773114144842290835 5020318159671217263436253)
                    ·
                      refine ⟨1882619309876706473788595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020318159671217263436253 1882619309876706473788595)
                      ·
                        rfl

theorem cell23_3666388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3666388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666388 prefixEnd_3666388 := by exact prefixLift 3666388
  have htrace : WordTrace (prefixWord ++ tailWord_3666388) baseStart_3666388 baseEnd_3666388 := by
    simpa [prefixWord, tailWord_3666388, baseEnd_3666388] using wordTrace_append hprefix tailTrace_3666388
  have hstable : (prefixWord ++ tailWord_3666388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666388).length < 2 ^ (prefixWord ++ tailWord_3666388).sum := by decide
  have hdescent : baseEnd_3666388 < baseStart_3666388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666397 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3666397 : Nat := 118140960795 + 3666397 * 2 ^ 59
def prefixEnd_3666397 : Nat := 4983230072969 + 3 ^ 40 * 3666397 * 2
def baseEnd_3666397 : Nat := 1882623931202596938576053

theorem tailTrace_3666397 : CollatzResearch.WordTrace tailWord_3666397 prefixEnd_3666397 1882623931202596938576053 := by
  unfold tailWord_3666397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133724484498277314600709445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89149656332184876400472963 133724484498277314600709445)
  ·
    refine ⟨25073340843426996487633021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133724484498277314600709445 25073340843426996487633021)
    ·
      refine ⟨9402502816285123682862383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25073340843426996487633021 9402502816285123682862383)
      ·
        refine ⟨14103754224427685524293575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402502816285123682862383 14103754224427685524293575)
        ·
          refine ⟨21155631336641528286440363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103754224427685524293575 21155631336641528286440363)
          ·
            refine ⟨31733447004962292429660545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21155631336641528286440363 31733447004962292429660545)
            ·
              refine ⟨23800085253721719322245409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31733447004962292429660545 23800085253721719322245409)
              ·
                refine ⟨17850063940291289491684057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23800085253721719322245409 17850063940291289491684057)
                ·
                  refine ⟨13387547955218467118763043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17850063940291289491684057 13387547955218467118763043)
                  ·
                    refine ⟨20081321932827700678144565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13387547955218467118763043 20081321932827700678144565)
                    ·
                      refine ⟨1882623931202596938576053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20081321932827700678144565 1882623931202596938576053)
                      ·
                        rfl

theorem cell23_3666397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3666397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666397 prefixEnd_3666397 := by exact prefixLift 3666397
  have htrace : WordTrace (prefixWord ++ tailWord_3666397) baseStart_3666397 baseEnd_3666397 := by
    simpa [prefixWord, tailWord_3666397, baseEnd_3666397] using wordTrace_append hprefix tailTrace_3666397
  have hstable : (prefixWord ++ tailWord_3666397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666397).length < 2 ^ (prefixWord ++ tailWord_3666397).sum := by decide
  have hdescent : baseEnd_3666397 < baseStart_3666397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666400 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 7]
def baseStart_3666400 : Nat := 118140960795 + 3666400 * 2 ^ 59
def prefixEnd_3666400 : Nat := 4983230072969 + 3 ^ 40 * 3666400 * 2
def baseEnd_3666400 : Nat := 209180607960506714093171

theorem tailTrace_3666400 : CollatzResearch.WordTrace tailWord_3666400 prefixEnd_3666400 209180607960506714093171 := by
  unfold tailWord_3666400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862296958633223056534327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89149729278177630742045769 66862296958633223056534327)
  ·
    refine ⟨100293445437949834584801491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66862296958633223056534327 100293445437949834584801491)
    ·
      refine ⟨150440168156924751877202237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100293445437949834584801491 150440168156924751877202237)
      ·
        refine ⟨56415063058846781953950839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150440168156924751877202237 56415063058846781953950839)
        ·
          refine ⟨84622594588270172930926259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56415063058846781953950839 84622594588270172930926259)
          ·
            refine ⟨126933891882405259396389389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84622594588270172930926259 126933891882405259396389389)
            ·
              refine ⟨47600209455901972273646021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126933891882405259396389389 47600209455901972273646021)
              ·
                refine ⟨8925039272981619801308629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47600209455901972273646021 8925039272981619801308629)
                ·
                  refine ⟨209180607960506714093171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8925039272981619801308629 209180607960506714093171)
                  ·
                    rfl

theorem cell23_3666400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_3666400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666400 prefixEnd_3666400 := by exact prefixLift 3666400
  have htrace : WordTrace (prefixWord ++ tailWord_3666400) baseStart_3666400 baseEnd_3666400 := by
    simpa [prefixWord, tailWord_3666400, baseEnd_3666400] using wordTrace_append hprefix tailTrace_3666400
  have hstable : (prefixWord ++ tailWord_3666400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666400).length < 2 ^ (prefixWord ++ tailWord_3666400).sum := by decide
  have hdescent : baseEnd_3666400 < baseStart_3666400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666507 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 6]
def baseStart_3666507 : Nat := 118140960795 + 3666507 * 2 ^ 59
def prefixEnd_3666507 : Nat := 4983230072969 + 3 ^ 40 * 3666507 * 2
def baseEnd_3666507 : Nat := 209186712674954612022283

theorem tailTrace_3666507 : CollatzResearch.WordTrace tailWord_3666507 prefixEnd_3666507 209186712674954612022283 := by
  unfold tailWord_3666507
  simp only [CollatzResearch.WordTrace]
  refine ⟨133728496527878803387213775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89152331018585868924809183 133728496527878803387213775)
  ·
    refine ⟨200592744791818205080820663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133728496527878803387213775 200592744791818205080820663)
    ·
      refine ⟨300889117187727307621230995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200592744791818205080820663 300889117187727307621230995)
      ·
        refine ⟨451333675781590961431846493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300889117187727307621230995 451333675781590961431846493)
        ·
          refine ⟨169250128418096610536942435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451333675781590961431846493 169250128418096610536942435)
          ·
            refine ⟨253875192627144915805413653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169250128418096610536942435 253875192627144915805413653)
            ·
              refine ⟨11900399654397417928378765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253875192627144915805413653 11900399654397417928378765)
              ·
                refine ⟨4462649870399031723142037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11900399654397417928378765 4462649870399031723142037)
                ·
                  refine ⟨209186712674954612022283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4462649870399031723142037 209186712674954612022283)
                  ·
                    rfl

theorem cell23_3666507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 6].length) (baseStart_3666507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666507 prefixEnd_3666507 := by exact prefixLift 3666507
  have htrace : WordTrace (prefixWord ++ tailWord_3666507) baseStart_3666507 baseEnd_3666507 := by
    simpa [prefixWord, tailWord_3666507, baseEnd_3666507] using wordTrace_append hprefix tailTrace_3666507
  have hstable : (prefixWord ++ tailWord_3666507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666507).length < 2 ^ (prefixWord ++ tailWord_3666507).sum := by decide
  have hdescent : baseEnd_3666507 < baseStart_3666507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666541 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 6]
def baseStart_3666541 : Nat := 118140960795 + 3666541 * 2 ^ 59
def prefixEnd_3666541 : Nat := 4983230072969 + 3 ^ 40 * 3666541 * 2
def baseEnd_3666541 : Nat := 209188652490760486130599

theorem tailTrace_3666541 : CollatzResearch.WordTrace tailWord_3666541 prefixEnd_3666541 209188652490760486130599 := by
  unfold tailWord_3666541
  simp only [CollatzResearch.WordTrace]
  refine ⟨133729736609755627193951477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89153157739837084795967651 133729736609755627193951477)
  ·
    refine ⟨12537162807164590049432951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133729736609755627193951477 12537162807164590049432951)
    ·
      refine ⟨18805744210746885074149427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537162807164590049432951 18805744210746885074149427)
      ·
        refine ⟨28208616316120327611224141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18805744210746885074149427 28208616316120327611224141)
        ·
          refine ⟨10578231118545122854209053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28208616316120327611224141 10578231118545122854209053)
          ·
            refine ⟨3966836669454421070328395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10578231118545122854209053 3966836669454421070328395)
            ·
              refine ⟨5950255004181631605492593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966836669454421070328395 5950255004181631605492593)
              ·
                refine ⟨4462691253136223704119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950255004181631605492593 4462691253136223704119445)
                ·
                  refine ⟨209188652490760486130599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4462691253136223704119445 209188652490760486130599)
                  ·
                    rfl

theorem cell23_3666541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_3666541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666541 prefixEnd_3666541 := by exact prefixLift 3666541
  have htrace : WordTrace (prefixWord ++ tailWord_3666541) baseStart_3666541 baseEnd_3666541 := by
    simpa [prefixWord, tailWord_3666541, baseEnd_3666541] using wordTrace_append hprefix tailTrace_3666541
  have hstable : (prefixWord ++ tailWord_3666541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666541).length < 2 ^ (prefixWord ++ tailWord_3666541).sum := by decide
  have hdescent : baseEnd_3666541 < baseStart_3666541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666584 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_3666584 : Nat := 118140960795 + 3666584 * 2 ^ 59
def prefixEnd_3666584 : Nat := 4983230072969 + 3 ^ 40 * 3666584 * 2
def baseEnd_3666584 : Nat := 627573317361662568979231

theorem tailTrace_3666584 : CollatzResearch.WordTrace tailWord_3666584 prefixEnd_3666584 627573317361662568979231 := by
  unfold tailWord_3666584
  simp only [CollatzResearch.WordTrace]
  refine ⟨66865652474299922768883403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89154203299066563691844537 66865652474299922768883403)
  ·
    refine ⟨100298478711449884153325105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66865652474299922768883403 100298478711449884153325105)
    ·
      refine ⟨75223859033587413114993829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100298478711449884153325105 75223859033587413114993829)
      ·
        refine ⟨14104473568797639959061343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75223859033587413114993829 14104473568797639959061343)
        ·
          refine ⟨21156710353196459938592015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104473568797639959061343 21156710353196459938592015)
          ·
            refine ⟨31735065529794689907888023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21156710353196459938592015 31735065529794689907888023)
            ·
              refine ⟨47602598294692034861832035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31735065529794689907888023 47602598294692034861832035)
              ·
                refine ⟨71403897442038052292748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47602598294692034861832035 71403897442038052292748053)
                ·
                  refine ⟨3347057692595533701222565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71403897442038052292748053 3347057692595533701222565)
                  ·
                    refine ⟨627573317361662568979231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3347057692595533701222565 627573317361662568979231)
                    ·
                      rfl

theorem cell23_3666584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_3666584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666584 prefixEnd_3666584 := by exact prefixLift 3666584
  have htrace : WordTrace (prefixWord ++ tailWord_3666584) baseStart_3666584 baseEnd_3666584 := by
    simpa [prefixWord, tailWord_3666584, baseEnd_3666584] using wordTrace_append hprefix tailTrace_3666584
  have hstable : (prefixWord ++ tailWord_3666584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666584).length < 2 ^ (prefixWord ++ tailWord_3666584).sum := by decide
  have hdescent : baseEnd_3666584 < baseStart_3666584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666587 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_3666587 : Nat := 118140960795 + 3666587 * 2 ^ 59
def prefixEnd_3666587 : Nat := 4983230072969 + 3 ^ 40 * 3666587 * 2
def baseEnd_3666587 : Nat := 1882721492526951195200179

theorem tailTrace_3666587 : CollatzResearch.WordTrace tailWord_3666587 prefixEnd_3666587 1882721492526951195200179 := by
  unfold tailWord_3666587
  simp only [CollatzResearch.WordTrace]
  refine ⟨133731414367588977050126015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89154276245059318033417343 133731414367588977050126015)
  ·
    refine ⟨200597121551383465575189023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133731414367588977050126015 200597121551383465575189023)
    ·
      refine ⟨300895682327075198362783535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200597121551383465575189023 300895682327075198362783535)
      ·
        refine ⟨451343523490612797544175303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300895682327075198362783535 451343523490612797544175303)
        ·
          refine ⟨677015285235919196316262955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451343523490612797544175303 677015285235919196316262955)
          ·
            refine ⟨1015522927853878794474394433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677015285235919196316262955 1015522927853878794474394433)
            ·
              refine ⟨761642195890409095855795825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015522927853878794474394433 761642195890409095855795825)
              ·
                refine ⟨571231646917806821891846869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761642195890409095855795825 571231646917806821891846869)
                ·
                  refine ⟨13388241724636097388090161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 571231646917806821891846869 13388241724636097388090161)
                  ·
                    refine ⟨10041181293477073041067621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13388241724636097388090161 10041181293477073041067621)
                    ·
                      refine ⟨1882721492526951195200179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10041181293477073041067621 1882721492526951195200179)
                      ·
                        rfl

theorem cell23_3666587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_3666587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666587 prefixEnd_3666587 := by exact prefixLift 3666587
  have htrace : WordTrace (prefixWord ++ tailWord_3666587) baseStart_3666587 baseEnd_3666587 := by
    simpa [prefixWord, tailWord_3666587, baseEnd_3666587] using wordTrace_append hprefix tailTrace_3666587
  have hstable : (prefixWord ++ tailWord_3666587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666587).length < 2 ^ (prefixWord ++ tailWord_3666587).sum := by decide
  have hdescent : baseEnd_3666587 < baseStart_3666587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666602 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3666602 : Nat := 118140960795 + 3666602 * 2 ^ 59
def prefixEnd_3666602 : Nat := 4983230072969 + 3 ^ 40 * 3666602 * 2
def baseEnd_3666602 : Nat := 1882729194736768636512611

theorem tailTrace_3666602 : CollatzResearch.WordTrace tailWord_3666602 prefixEnd_3666602 1882729194736768636512611 := by
  unfold tailWord_3666602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33432990365633658652980515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89154640975023089741281373 33432990365633658652980515)
  ·
    refine ⟨50149485548450487979470773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33432990365633658652980515 50149485548450487979470773)
    ·
      refine ⟨4701514270167233248075385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50149485548450487979470773 4701514270167233248075385)
      ·
        refine ⟨3526135702625424936056539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701514270167233248075385 3526135702625424936056539)
        ·
          refine ⟨5289203553938137404084809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526135702625424936056539 5289203553938137404084809)
          ·
            refine ⟨3966902665453603053063607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5289203553938137404084809 3966902665453603053063607)
            ·
              refine ⟨5950353998180404579595411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966902665453603053063607 5950353998180404579595411)
              ·
                refine ⟨8925530997270606869393117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950353998180404579595411 8925530997270606869393117)
                ·
                  refine ⟨3347074123976477576022419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8925530997270606869393117 3347074123976477576022419)
                  ·
                    refine ⟨5020611185964716364033629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347074123976477576022419 5020611185964716364033629)
                    ·
                      refine ⟨1882729194736768636512611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020611185964716364033629 1882729194736768636512611)
                      ·
                        rfl

theorem cell23_3666602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3666602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666602 prefixEnd_3666602 := by exact prefixLift 3666602
  have htrace : WordTrace (prefixWord ++ tailWord_3666602) baseStart_3666602 baseEnd_3666602 := by
    simpa [prefixWord, tailWord_3666602, baseEnd_3666602] using wordTrace_append hprefix tailTrace_3666602
  have hstable : (prefixWord ++ tailWord_3666602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666602).length < 2 ^ (prefixWord ++ tailWord_3666602).sum := by decide
  have hdescent : baseEnd_3666602 < baseStart_3666602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3666617 : Nat := 118140960795 + 3666617 * 2 ^ 59
def prefixEnd_3666617 : Nat := 4983230072969 + 3 ^ 40 * 3666617 * 2
def baseEnd_3666617 : Nat := 1882736896946586077825041

theorem tailTrace_3666617 : CollatzResearch.WordTrace tailWord_3666617 prefixEnd_3666617 1882736896946586077825041 := by
  unfold tailWord_3666617
  simp only [CollatzResearch.WordTrace]
  refine ⟨133732508557480292173718105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89155005704986861449145403 133732508557480292173718105)
  ·
    refine ⟨100299381418110219130288579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133732508557480292173718105 100299381418110219130288579)
    ·
      refine ⟨150449072127165328695432869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100299381418110219130288579 150449072127165328695432869)
      ·
        refine ⟨28209201023843499130393663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150449072127165328695432869 28209201023843499130393663)
        ·
          refine ⟨42313801535765248695590495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28209201023843499130393663 42313801535765248695590495)
          ·
            refine ⟨63470702303647873043385743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42313801535765248695590495 63470702303647873043385743)
            ·
              refine ⟨95206053455471809565078615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63470702303647873043385743 95206053455471809565078615)
              ·
                refine ⟨142809080183207714347617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95206053455471809565078615 142809080183207714347617923)
                ·
                  refine ⟨214213620274811571521426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142809080183207714347617923 214213620274811571521426885)
                  ·
                    refine ⟨40165053801527169660267541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214213620274811571521426885 40165053801527169660267541)
                    ·
                      refine ⟨1882736896946586077825041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40165053801527169660267541 1882736896946586077825041)
                      ·
                        rfl

theorem cell23_3666617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3666617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666617 prefixEnd_3666617 := by exact prefixLift 3666617
  have htrace : WordTrace (prefixWord ++ tailWord_3666617) baseStart_3666617 baseEnd_3666617 := by
    simpa [prefixWord, tailWord_3666617, baseEnd_3666617] using wordTrace_append hprefix tailTrace_3666617
  have hstable : (prefixWord ++ tailWord_3666617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666617).length < 2 ^ (prefixWord ++ tailWord_3666617).sum := by decide
  have hdescent : baseEnd_3666617 < baseStart_3666617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666628 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3666628 : Nat := 118140960795 + 3666628 * 2 ^ 59
def prefixEnd_3666628 : Nat := 4983230072969 + 3 ^ 40 * 3666628 * 2
def baseEnd_3666628 : Nat := 1882742545233785534787491

theorem tailTrace_3666628 : CollatzResearch.WordTrace tailWord_3666628 prefixEnd_3666628 1882742545233785534787491 := by
  unfold tailWord_3666628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66866454880220220526184269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89155273173626960701579025 66866454880220220526184269)
  ·
    refine ⟨25074920580082582697319101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66866454880220220526184269 25074920580082582697319101)
    ·
      refine ⟨9403095217530968511494663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25074920580082582697319101 9403095217530968511494663)
      ·
        refine ⟨14104642826296452767241995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403095217530968511494663 14104642826296452767241995)
        ·
          refine ⟨21156964239444679150862993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104642826296452767241995 21156964239444679150862993)
          ·
            refine ⟨15867723179583509363147245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21156964239444679150862993 15867723179583509363147245)
            ·
              refine ⟨5950396192343816011180217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15867723179583509363147245 5950396192343816011180217)
              ·
                refine ⟨4462797144257862008385163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950396192343816011180217 4462797144257862008385163)
                ·
                  refine ⟨6694195716386793012577745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462797144257862008385163 6694195716386793012577745)
                  ·
                    refine ⟨5020646787290094759433309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694195716386793012577745 5020646787290094759433309)
                    ·
                      refine ⟨1882742545233785534787491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020646787290094759433309 1882742545233785534787491)
                      ·
                        rfl

theorem cell23_3666628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3666628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666628 prefixEnd_3666628 := by exact prefixLift 3666628
  have htrace : WordTrace (prefixWord ++ tailWord_3666628) baseStart_3666628 baseEnd_3666628 := by
    simpa [prefixWord, tailWord_3666628, baseEnd_3666628] using wordTrace_append hprefix tailTrace_3666628
  have hstable : (prefixWord ++ tailWord_3666628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666628).length < 2 ^ (prefixWord ++ tailWord_3666628).sum := by decide
  have hdescent : baseEnd_3666628 < baseStart_3666628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666645 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3666645 : Nat := 118140960795 + 3666645 * 2 ^ 59
def prefixEnd_3666645 : Nat := 4983230072969 + 3 ^ 40 * 3666645 * 2
def baseEnd_3666645 : Nat := 1882751274404911968274913

theorem tailTrace_3666645 : CollatzResearch.WordTrace tailWord_3666645 prefixEnd_3666645 1882751274404911968274913 := by
  unfold tailWord_3666645
  simp only [CollatzResearch.WordTrace]
  refine ⟨133733529801378852955737389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89155686534252568637158259 133733529801378852955737389)
  ·
    refine ⟨50150073675517069858401521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133733529801378852955737389 50150073675517069858401521)
    ·
      refine ⟨37612555256637802393801141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50150073675517069858401521 37612555256637802393801141)
      ·
        refine ⟨3526177055309793974418857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37612555256637802393801141 3526177055309793974418857)
        ·
          refine ⟨2644632791482345480814143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526177055309793974418857 2644632791482345480814143)
          ·
            refine ⟨3966949187223518221221215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644632791482345480814143 3966949187223518221221215)
            ·
              refine ⟨5950423780835277331831823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966949187223518221221215 5950423780835277331831823)
              ·
                refine ⟨8925635671252915997747735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950423780835277331831823 8925635671252915997747735)
                ·
                  refine ⟨13388453506879373996621603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8925635671252915997747735 13388453506879373996621603)
                  ·
                    refine ⟨20082680260319060994932405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13388453506879373996621603 20082680260319060994932405)
                    ·
                      refine ⟨1882751274404911968274913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20082680260319060994932405 1882751274404911968274913)
                      ·
                        rfl

theorem cell23_3666645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3666645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666645 prefixEnd_3666645 := by exact prefixLift 3666645
  have htrace : WordTrace (prefixWord ++ tailWord_3666645) baseStart_3666645 baseEnd_3666645 := by
    simpa [prefixWord, tailWord_3666645, baseEnd_3666645] using wordTrace_append hprefix tailTrace_3666645
  have hstable : (prefixWord ++ tailWord_3666645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666645).length < 2 ^ (prefixWord ++ tailWord_3666645).sum := by decide
  have hdescent : baseEnd_3666645 < baseStart_3666645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666659 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3666659 : Nat := 118140960795 + 3666659 * 2 ^ 59
def prefixEnd_3666659 : Nat := 4983230072969 + 3 ^ 40 * 3666659 * 2
def baseEnd_3666659 : Nat := 1882758463134074913499849

theorem tailTrace_3666659 : CollatzResearch.WordTrace tailWord_3666659 prefixEnd_3666659 1882758463134074913499849 := by
  unfold tailWord_3666659
  simp only [CollatzResearch.WordTrace]
  refine ⟨133734040423328133346747031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89156026948885422231164687 133734040423328133346747031)
  ·
    refine ⟨200601060634992200020120547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133734040423328133346747031 200601060634992200020120547)
    ·
      refine ⟨300901590952488300030180821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200601060634992200020120547 300901590952488300030180821)
      ·
        refine ⟨7052381037948944531957363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 300901590952488300030180821 7052381037948944531957363)
        ·
          refine ⟨10578571556923416797936045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7052381037948944531957363 10578571556923416797936045)
          ·
            refine ⟨3966964333846281299226017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10578571556923416797936045 3966964333846281299226017)
            ·
              refine ⟨2975223250384710974419513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966964333846281299226017 2975223250384710974419513)
              ·
                refine ⟨2231417437788533230814635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975223250384710974419513 2231417437788533230814635)
                ·
                  refine ⟨3347126156682799846221953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231417437788533230814635 3347126156682799846221953)
                  ·
                    refine ⟨2510344617512099884666465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347126156682799846221953 2510344617512099884666465)
                    ·
                      refine ⟨1882758463134074913499849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510344617512099884666465 1882758463134074913499849)
                      ·
                        rfl

theorem cell23_3666659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3666659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666659 prefixEnd_3666659 := by exact prefixLift 3666659
  have htrace : WordTrace (prefixWord ++ tailWord_3666659) baseStart_3666659 baseEnd_3666659 := by
    simpa [prefixWord, tailWord_3666659, baseEnd_3666659] using wordTrace_append hprefix tailTrace_3666659
  have hstable : (prefixWord ++ tailWord_3666659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666659).length < 2 ^ (prefixWord ++ tailWord_3666659).sum := by decide
  have hdescent : baseEnd_3666659 < baseStart_3666659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666674 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3666674 : Nat := 118140960795 + 3666674 * 2 ^ 59
def prefixEnd_3666674 : Nat := 4983230072969 + 3 ^ 40 * 3666674 * 2
def baseEnd_3666674 : Nat := 627588721781297451604093

theorem tailTrace_3666674 : CollatzResearch.WordTrace tailWord_3666674 prefixEnd_3666674 627588721781297451604093 := by
  unfold tailWord_3666674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33433646879568447727135769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89156391678849193939028717 33433646879568447727135769)
  ·
    refine ⟨25075235159676335795351827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33433646879568447727135769 25075235159676335795351827)
    ·
      refine ⟨37612852739514503693027741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25075235159676335795351827 37612852739514503693027741)
      ·
        refine ⟨14104819777317938884885403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37612852739514503693027741 14104819777317938884885403)
        ·
          refine ⟨21157229665976908327328105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104819777317938884885403 21157229665976908327328105)
          ·
            refine ⟨15867922249482681245496079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21157229665976908327328105 15867922249482681245496079)
            ·
              refine ⟨23801883374224021868244119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15867922249482681245496079 23801883374224021868244119)
              ·
                refine ⟨35702825061336032802366179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23801883374224021868244119 35702825061336032802366179)
                ·
                  refine ⟨53554237592004049203549269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35702825061336032802366179 53554237592004049203549269)
                  ·
                    refine ⟨627588721781297451604093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53554237592004049203549269 627588721781297451604093)
                    ·
                      rfl

theorem cell23_3666674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3666674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666674 prefixEnd_3666674 := by exact prefixLift 3666674
  have htrace : WordTrace (prefixWord ++ tailWord_3666674) baseStart_3666674 baseEnd_3666674 := by
    simpa [prefixWord, tailWord_3666674, baseEnd_3666674] using wordTrace_append hprefix tailTrace_3666674
  have hstable : (prefixWord ++ tailWord_3666674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666674).length < 2 ^ (prefixWord ++ tailWord_3666674).sum := by decide
  have hdescent : baseEnd_3666674 < baseStart_3666674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666698 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_3666698 : Nat := 118140960795 + 3666698 * 2 ^ 59
def prefixEnd_3666698 : Nat := 4983230072969 + 3 ^ 40 * 3666698 * 2
def baseEnd_3666698 : Nat := 1882778488879600260912169

theorem tailTrace_3666698 : CollatzResearch.WordTrace tailWord_3666698 prefixEnd_3666698 1882778488879600260912169 := by
  unfold tailWord_3666698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33433865717546710751854187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89156975246791228671611165 33433865717546710751854187)
  ·
    refine ⟨50150798576320066127781281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33433865717546710751854187 50150798576320066127781281)
    ·
      refine ⟨37613098932240049595835961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50150798576320066127781281 37613098932240049595835961)
      ·
        refine ⟨28209824199180037196876971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37613098932240049595835961 28209824199180037196876971)
        ·
          refine ⟨42314736298770055795315457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28209824199180037196876971 42314736298770055795315457)
          ·
            refine ⟨31736052224077541846486593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42314736298770055795315457 31736052224077541846486593)
            ·
              refine ⟨23802039168058156384864945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31736052224077541846486593 23802039168058156384864945)
              ·
                refine ⟨17851529376043617288648709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23802039168058156384864945 17851529376043617288648709)
                ·
                  refine ⟨3347161758008178241621633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17851529376043617288648709 3347161758008178241621633)
                  ·
                    refine ⟨2510371318506133681216225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347161758008178241621633 2510371318506133681216225)
                    ·
                      refine ⟨1882778488879600260912169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510371318506133681216225 1882778488879600260912169)
                      ·
                        rfl

theorem cell23_3666698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_3666698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666698 prefixEnd_3666698 := by exact prefixLift 3666698
  have htrace : WordTrace (prefixWord ++ tailWord_3666698) baseStart_3666698 baseEnd_3666698 := by
    simpa [prefixWord, tailWord_3666698, baseEnd_3666698] using wordTrace_append hprefix tailTrace_3666698
  have hstable : (prefixWord ++ tailWord_3666698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666698).length < 2 ^ (prefixWord ++ tailWord_3666698).sum := by decide
  have hdescent : baseEnd_3666698 < baseStart_3666698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666721 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 5]
def baseStart_3666721 : Nat := 118140960795 + 3666721 * 2 ^ 59
def prefixEnd_3666721 : Nat := 4983230072969 + 3 ^ 40 * 3666721 * 2
def baseEnd_3666721 : Nat := 209198922103850407880507

theorem tailTrace_3666721 : CollatzResearch.WordTrace tailWord_3666721 prefixEnd_3666721 209198922103850407880507 := by
  unfold tailWord_3666721
  simp only [CollatzResearch.WordTrace]
  refine ⟨133736301749103517935504017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89157534499402345290336011 133736301749103517935504017)
  ·
    refine ⟨100302226311827638451628013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133736301749103517935504017 100302226311827638451628013)
    ·
      refine ⟨37613334866935364419360505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100302226311827638451628013 37613334866935364419360505)
      ·
        refine ⟨28210001150201523314520379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37613334866935364419360505 28210001150201523314520379)
        ·
          refine ⟨42315001725302284971780569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28210001150201523314520379 42315001725302284971780569)
          ·
            refine ⟨31736251293976713728835427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42315001725302284971780569 31736251293976713728835427)
            ·
              refine ⟨47604376940965070593253141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31736251293976713728835427 47604376940965070593253141)
              ·
                refine ⟨2231455169107737684058741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47604376940965070593253141 2231455169107737684058741)
                ·
                  refine ⟨209198922103850407880507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2231455169107737684058741 209198922103850407880507)
                  ·
                    rfl

theorem cell23_3666721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 5].length) (baseStart_3666721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666721 prefixEnd_3666721 := by exact prefixLift 3666721
  have htrace : WordTrace (prefixWord ++ tailWord_3666721) baseStart_3666721 baseEnd_3666721 := by
    simpa [prefixWord, tailWord_3666721, baseEnd_3666721] using wordTrace_append hprefix tailTrace_3666721
  have hstable : (prefixWord ++ tailWord_3666721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666721).length < 2 ^ (prefixWord ++ tailWord_3666721).sum := by decide
  have hdescent : baseEnd_3666721 < baseStart_3666721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 4, 2]
def baseStart_3666771 : Nat := 118140960795 + 3666771 * 2 ^ 59
def prefixEnd_3666771 : Nat := 4983230072969 + 3 ^ 40 * 3666771 * 2
def baseEnd_3666771 : Nat := 1882815972967378475299333

theorem tailTrace_3666771 : CollatzResearch.WordTrace tailWord_3666771 prefixEnd_3666771 1882815972967378475299333 := by
  unfold tailWord_3666771
  simp only [CollatzResearch.WordTrace]
  refine ⟨133738125398922376474824167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89158750265948250983216111 133738125398922376474824167)
  ·
    refine ⟨200607188098383564712236251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133738125398922376474824167 200607188098383564712236251)
    ·
      refine ⟨300910782147575347068354377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200607188098383564712236251 300910782147575347068354377)
      ·
        refine ⟨225683086610681510301265783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300910782147575347068354377 225683086610681510301265783)
        ·
          refine ⟨338524629916022265451898675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225683086610681510301265783 338524629916022265451898675)
          ·
            refine ⟨507786944874033398177848013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338524629916022265451898675 507786944874033398177848013)
            ·
              refine ⟨190420104327762524316693005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507786944874033398177848013 190420104327762524316693005)
              ·
                refine ⟨71407539122910946618759877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190420104327762524316693005 71407539122910946618759877)
                ·
                  refine ⟨13388913585545802491017477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71407539122910946618759877 13388913585545802491017477)
                  ·
                    refine ⟨2510421297289837967065777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13388913585545802491017477 2510421297289837967065777)
                    ·
                      refine ⟨1882815972967378475299333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510421297289837967065777 1882815972967378475299333)
                      ·
                        rfl

theorem cell23_3666771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4, 2].length) (baseStart_3666771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666771 prefixEnd_3666771 := by exact prefixLift 3666771
  have htrace : WordTrace (prefixWord ++ tailWord_3666771) baseStart_3666771 baseEnd_3666771 := by
    simpa [prefixWord, tailWord_3666771, baseEnd_3666771] using wordTrace_append hprefix tailTrace_3666771
  have hstable : (prefixWord ++ tailWord_3666771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666771).length < 2 ^ (prefixWord ++ tailWord_3666771).sum := by decide
  have hdescent : baseEnd_3666771 < baseStart_3666771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666848 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2]
def baseStart_3666848 : Nat := 118140960795 + 3666848 * 2 ^ 59
def prefixEnd_3666848 : Nat := 4983230072969 + 3 ^ 40 * 3666848 * 2
def baseEnd_3666848 : Nat := 1882855510977774674036479

theorem tailTrace_3666848 : CollatzResearch.WordTrace tailWord_3666848 prefixEnd_3666848 1882855510977774674036479 := by
  unfold tailWord_3666848
  simp only [CollatzResearch.WordTrace]
  refine ⟨66870466909821709312688599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89160622546428945750251465 66870466909821709312688599)
  ·
    refine ⟨100305700364732563969032899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66870466909821709312688599 100305700364732563969032899)
    ·
      refine ⟨150458550547098845953549349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100305700364732563969032899 150458550547098845953549349)
      ·
        refine ⟨28210978227581033616290503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150458550547098845953549349 28210978227581033616290503)
        ·
          refine ⟨42316467341371550424435755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28210978227581033616290503 42316467341371550424435755)
          ·
            refine ⟨63474701012057325636653633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42316467341371550424435755 63474701012057325636653633)
            ·
              refine ⟨47606025759042994227490225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63474701012057325636653633 47606025759042994227490225)
              ·
                refine ⟨35704519319282245670617669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47606025759042994227490225 35704519319282245670617669)
                ·
                  refine ⟨6694597372365421063240813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35704519319282245670617669 6694597372365421063240813)
                  ·
                    refine ⟨2510474014637032898715305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6694597372365421063240813 2510474014637032898715305)
                    ·
                      refine ⟨1882855510977774674036479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510474014637032898715305 1882855510977774674036479)
                      ·
                        rfl

theorem cell23_3666848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_3666848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666848 prefixEnd_3666848 := by exact prefixLift 3666848
  have htrace : WordTrace (prefixWord ++ tailWord_3666848) baseStart_3666848 baseEnd_3666848 := by
    simpa [prefixWord, tailWord_3666848, baseEnd_3666848] using wordTrace_append hprefix tailTrace_3666848
  have hstable : (prefixWord ++ tailWord_3666848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666848).length < 2 ^ (prefixWord ++ tailWord_3666848).sum := by decide
  have hdescent : baseEnd_3666848 < baseStart_3666848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666865 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3666865 : Nat := 118140960795 + 3666865 * 2 ^ 59
def prefixEnd_3666865 : Nat := 4983230072969 + 3 ^ 40 * 3666865 * 2
def baseEnd_3666865 : Nat := 1882864240148901107523901

theorem tailTrace_3666865 : CollatzResearch.WordTrace tailWord_3666865 prefixEnd_3666865 1882864240148901107523901 := by
  unfold tailWord_3666865
  simp only [CollatzResearch.WordTrace]
  refine ⟨133741553860581830528746049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89161035907054553685830699 133741553860581830528746049)
  ·
    refine ⟨100306165395436372896559537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133741553860581830528746049 100306165395436372896559537)
    ·
      refine ⟨75229624046577279672419653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100306165395436372896559537 75229624046577279672419653)
      ·
        refine ⟨14105554508733239938578685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75229624046577279672419653 14105554508733239938578685)
        ·
          refine ⟨5289582940774964976967007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14105554508733239938578685 5289582940774964976967007)
          ·
            refine ⟨7934374411162447465450511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289582940774964976967007 7934374411162447465450511)
            ·
              refine ⟨11901561616743671198175767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934374411162447465450511 11901561616743671198175767)
              ·
                refine ⟨17852342425115506797263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901561616743671198175767 17852342425115506797263651)
                ·
                  refine ⟨26778513637673260195895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17852342425115506797263651 26778513637673260195895477)
                  ·
                    refine ⟨2510485653531868143365201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26778513637673260195895477 2510485653531868143365201)
                    ·
                      refine ⟨1882864240148901107523901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510485653531868143365201 1882864240148901107523901)
                      ·
                        rfl

theorem cell23_3666865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3666865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666865 prefixEnd_3666865 := by exact prefixLift 3666865
  have htrace : WordTrace (prefixWord ++ tailWord_3666865) baseStart_3666865 baseEnd_3666865 := by
    simpa [prefixWord, tailWord_3666865, baseEnd_3666865] using wordTrace_append hprefix tailTrace_3666865
  have hstable : (prefixWord ++ tailWord_3666865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666865).length < 2 ^ (prefixWord ++ tailWord_3666865).sum := by decide
  have hdescent : baseEnd_3666865 < baseStart_3666865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666871 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 6]
def baseStart_3666871 : Nat := 118140960795 + 3666871 * 2 ^ 59
def prefixEnd_3666871 : Nat := 4983230072969 + 3 ^ 40 * 3666871 * 2
def baseEnd_3666871 : Nat := 627622440344276028016291

theorem tailTrace_3666871 : CollatzResearch.WordTrace tailWord_3666871 prefixEnd_3666871 627622440344276028016291 := by
  unfold tailWord_3666871
  simp only [CollatzResearch.WordTrace]
  refine ⟨133741772698560093553464467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89161181799040062368976311 133741772698560093553464467)
  ·
    refine ⟨200612659047840140330196701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133741772698560093553464467 200612659047840140330196701)
    ·
      refine ⟨75229747142940052623823763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200612659047840140330196701 75229747142940052623823763)
      ·
        refine ⟨112844620714410078935735645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75229747142940052623823763 112844620714410078935735645)
        ·
          refine ⟨42316732767903779600900867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112844620714410078935735645 42316732767903779600900867)
          ·
            refine ⟨63475099151855669401351301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42316732767903779600900867 63475099151855669401351301)
            ·
              refine ⟨11901581090972938012753369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63475099151855669401351301 11901581090972938012753369)
              ·
                refine ⟨8926185818229703509565027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11901581090972938012753369 8926185818229703509565027)
                ·
                  refine ⟨13389278727344555264347541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8926185818229703509565027 13389278727344555264347541)
                  ·
                    refine ⟨627622440344276028016291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13389278727344555264347541 627622440344276028016291)
                    ·
                      rfl

theorem cell23_3666871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_3666871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666871 prefixEnd_3666871 := by exact prefixLift 3666871
  have htrace : WordTrace (prefixWord ++ tailWord_3666871) baseStart_3666871 baseEnd_3666871 := by
    simpa [prefixWord, tailWord_3666871, baseEnd_3666871] using wordTrace_append hprefix tailTrace_3666871
  have hstable : (prefixWord ++ tailWord_3666871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666871).length < 2 ^ (prefixWord ++ tailWord_3666871).sum := by decide
  have hdescent : baseEnd_3666871 < baseStart_3666871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666872 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_3666872 : Nat := 118140960795 + 3666872 * 2 ^ 59
def prefixEnd_3666872 : Nat := 4983230072969 + 3 ^ 40 * 3666872 * 2
def baseEnd_3666872 : Nat := 1882867834513482580136369

theorem tailTrace_3666872 : CollatzResearch.WordTrace tailWord_3666872 prefixEnd_3666872 1882867834513482580136369 := by
  unfold tailWord_3666872
  simp only [CollatzResearch.WordTrace]
  refine ⟨66870904585778235362125435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89161206114370980482833913 66870904585778235362125435)
  ·
    refine ⟨100306356878667353043188153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66870904585778235362125435 100306356878667353043188153)
    ·
      refine ⟨75229767659000514782391115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100306356878667353043188153 75229767659000514782391115)
      ·
        refine ⟨112844651488500772173586673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75229767659000514782391115 112844651488500772173586673)
        ·
          refine ⟨84633488616375579130190005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112844651488500772173586673 84633488616375579130190005)
          ·
            refine ⟨7934389557785210543455313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84633488616375579130190005 7934389557785210543455313)
            ·
              refine ⟨5950792168338907907591485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934389557785210543455313 5950792168338907907591485)
              ·
                refine ⟨2231547063127090465346807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5950792168338907907591485 2231547063127090465346807)
                ·
                  refine ⟨3347320594690635698020211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231547063127090465346807 3347320594690635698020211)
                  ·
                    refine ⟨5020980892035953547030317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347320594690635698020211 5020980892035953547030317)
                    ·
                      refine ⟨1882867834513482580136369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020980892035953547030317 1882867834513482580136369)
                      ·
                        rfl

theorem cell23_3666872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_3666872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666872 prefixEnd_3666872 := by exact prefixLift 3666872
  have htrace : WordTrace (prefixWord ++ tailWord_3666872) baseStart_3666872 baseEnd_3666872 := by
    simpa [prefixWord, tailWord_3666872, baseEnd_3666872] using wordTrace_append hprefix tailTrace_3666872
  have hstable : (prefixWord ++ tailWord_3666872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666872).length < 2 ^ (prefixWord ++ tailWord_3666872).sum := by decide
  have hdescent : baseEnd_3666872 < baseStart_3666872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666895 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 3, 2, 2]
def baseStart_3666895 : Nat := 118140960795 + 3666895 * 2 ^ 59
def prefixEnd_3666895 : Nat := 4983230072969 + 3 ^ 40 * 3666895 * 2
def baseEnd_3666895 : Nat := 1882879644568535990148763

theorem tailTrace_3666895 : CollatzResearch.WordTrace tailWord_3666895 prefixEnd_3666895 1882879644568535990148763 := by
  unfold tailWord_3666895
  simp only [CollatzResearch.WordTrace]
  refine ⟨133742648050473145652338139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89161765366982097101558759 133742648050473145652338139)
  ·
    refine ⟨200613972075709718478507209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133742648050473145652338139 200613972075709718478507209)
    ·
      refine ⟨150460479056782288858880407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200613972075709718478507209 150460479056782288858880407)
      ·
        refine ⟨225690718585173433288320611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150460479056782288858880407 225690718585173433288320611)
        ·
          refine ⟨338536077877760149932480917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225690718585173433288320611 338536077877760149932480917)
          ·
            refine ⟨15868878650520007028085043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338536077877760149932480917 15868878650520007028085043)
            ·
              refine ⟨23803317975780010542127565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15868878650520007028085043 23803317975780010542127565)
              ·
                refine ⟨8926244240917503953297837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23803317975780010542127565 8926244240917503953297837)
                ·
                  refine ⟨3347341590344063982486689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8926244240917503953297837 3347341590344063982486689)
                  ·
                    refine ⟨2510506192758047986865017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347341590344063982486689 2510506192758047986865017)
                    ·
                      refine ⟨1882879644568535990148763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510506192758047986865017 1882879644568535990148763)
                      ·
                        rfl

theorem cell23_3666895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2, 2].length) (baseStart_3666895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666895 prefixEnd_3666895 := by exact prefixLift 3666895
  have htrace : WordTrace (prefixWord ++ tailWord_3666895) baseStart_3666895 baseEnd_3666895 := by
    simpa [prefixWord, tailWord_3666895, baseEnd_3666895] using wordTrace_append hprefix tailTrace_3666895
  have hstable : (prefixWord ++ tailWord_3666895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666895).length < 2 ^ (prefixWord ++ tailWord_3666895).sum := by decide
  have hdescent : baseEnd_3666895 < baseStart_3666895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666898 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3666898 : Nat := 118140960795 + 3666898 * 2 ^ 59
def prefixEnd_3666898 : Nat := 4983230072969 + 3 ^ 40 * 3666898 * 2
def baseEnd_3666898 : Nat := 1882881185010499478411249

theorem tailTrace_3666898 : CollatzResearch.WordTrace tailWord_3666898 prefixEnd_3666898 1882881185010499478411249 := by
  unfold tailWord_3666898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33435689367365569291174337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89161838312974851443131565 33435689367365569291174337)
  ·
    refine ⟨25076767025524176968380753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33435689367365569291174337 25076767025524176968380753)
    ·
      refine ⟨18807575269143132726285565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25076767025524176968380753 18807575269143132726285565)
      ·
        refine ⟨7052840725928674772357087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18807575269143132726285565 7052840725928674772357087)
        ·
          refine ⟨10579261088893012158535631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7052840725928674772357087 10579261088893012158535631)
          ·
            refine ⟨15868891633339518237803447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579261088893012158535631 15868891633339518237803447)
            ·
              refine ⟨23803337450009277356705171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15868891633339518237803447 23803337450009277356705171)
              ·
                refine ⟨35705006175013916035057757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23803337450009277356705171 35705006175013916035057757)
                ·
                  refine ⟨13389377315630218513146659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35705006175013916035057757 13389377315630218513146659)
                  ·
                    refine ⟨20084065973445327769719989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13389377315630218513146659 20084065973445327769719989)
                    ·
                      refine ⟨1882881185010499478411249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20084065973445327769719989 1882881185010499478411249)
                      ·
                        rfl

theorem cell23_3666898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3666898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666898 prefixEnd_3666898 := by exact prefixLift 3666898
  have htrace : WordTrace (prefixWord ++ tailWord_3666898) baseStart_3666898 baseEnd_3666898 := by
    simpa [prefixWord, tailWord_3666898, baseEnd_3666898] using wordTrace_append hprefix tailTrace_3666898
  have hstable : (prefixWord ++ tailWord_3666898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666898).length < 2 ^ (prefixWord ++ tailWord_3666898).sum := by decide
  have hdescent : baseEnd_3666898 < baseStart_3666898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666915 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3666915 : Nat := 118140960795 + 3666915 * 2 ^ 59
def prefixEnd_3666915 : Nat := 4983230072969 + 3 ^ 40 * 3666915 * 2
def baseEnd_3666915 : Nat := 1882889914181625911898671

theorem tailTrace_3666915 : CollatzResearch.WordTrace tailWord_3666915 prefixEnd_3666915 1882889914181625911898671 := by
  unfold tailWord_3666915
  simp only [CollatzResearch.WordTrace]
  refine ⟨133743377510400689068066199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89162251673600459378710799 133743377510400689068066199)
  ·
    refine ⟨200615066265601033602099299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133743377510400689068066199 200615066265601033602099299)
    ·
      refine ⟨300922599398401550403148949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200615066265601033602099299 300922599398401550403148949)
      ·
        refine ⟨14105746846800072675147607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300922599398401550403148949 14105746846800072675147607)
        ·
          refine ⟨21158620270200109012721411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105746846800072675147607 21158620270200109012721411)
          ·
            refine ⟨31737930405300163519082117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21158620270200109012721411 31737930405300163519082117)
            ·
              refine ⟨5950861950993780659827897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31737930405300163519082117 5950861950993780659827897)
              ·
                refine ⟨4463146463245335494870923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950861950993780659827897 4463146463245335494870923)
                ·
                  refine ⟨6694719694868003242306385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463146463245335494870923 6694719694868003242306385)
                  ·
                    refine ⟨5021039771151002431729789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694719694868003242306385 5021039771151002431729789)
                    ·
                      refine ⟨1882889914181625911898671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021039771151002431729789 1882889914181625911898671)
                      ·
                        rfl

theorem cell23_3666915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3666915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666915 prefixEnd_3666915 := by exact prefixLift 3666915
  have htrace : WordTrace (prefixWord ++ tailWord_3666915) baseStart_3666915 baseEnd_3666915 := by
    simpa [prefixWord, tailWord_3666915, baseEnd_3666915] using wordTrace_append hprefix tailTrace_3666915
  have hstable : (prefixWord ++ tailWord_3666915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666915).length < 2 ^ (prefixWord ++ tailWord_3666915).sum := by decide
  have hdescent : baseEnd_3666915 < baseStart_3666915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666929 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_3666929 : Nat := 118140960795 + 3666929 * 2 ^ 59
def prefixEnd_3666929 : Nat := 4983230072969 + 3 ^ 40 * 3666929 * 2
def baseEnd_3666929 : Nat := 1882897102910788857123607

theorem tailTrace_3666929 : CollatzResearch.WordTrace tailWord_3666929 prefixEnd_3666929 1882897102910788857123607 := by
  unfold tailWord_3666929
  simp only [CollatzResearch.WordTrace]
  refine ⟨133743888132349969459075841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89162592088233312972717227 133743888132349969459075841)
  ·
    refine ⟨100307916099262477094306881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133743888132349969459075841 100307916099262477094306881)
    ·
      refine ⟨75230937074446857820730161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100307916099262477094306881 75230937074446857820730161)
      ·
        refine ⟨56423202805835143365547621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75230937074446857820730161 56423202805835143365547621)
        ·
          refine ⟨10579350526094089381040179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56423202805835143365547621 10579350526094089381040179)
          ·
            refine ⟨15869025789141134071560269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579350526094089381040179 15869025789141134071560269)
            ·
              refine ⟨5950884670927925276835101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15869025789141134071560269 5950884670927925276835101)
              ·
                refine ⟨2231581751597971978813163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5950884670927925276835101 2231581751597971978813163)
                ·
                  refine ⟨3347372627396957968219745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231581751597971978813163 3347372627396957968219745)
                  ·
                    refine ⟨2510529470547718476164809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347372627396957968219745 2510529470547718476164809)
                    ·
                      refine ⟨1882897102910788857123607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510529470547718476164809 1882897102910788857123607)
                      ·
                        rfl

theorem cell23_3666929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_3666929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666929 prefixEnd_3666929 := by exact prefixLift 3666929
  have htrace : WordTrace (prefixWord ++ tailWord_3666929) baseStart_3666929 baseEnd_3666929 := by
    simpa [prefixWord, tailWord_3666929, baseEnd_3666929] using wordTrace_append hprefix tailTrace_3666929
  have hstable : (prefixWord ++ tailWord_3666929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666929).length < 2 ^ (prefixWord ++ tailWord_3666929).sum := by decide
  have hdescent : baseEnd_3666929 < baseStart_3666929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666941 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3666941 : Nat := 118140960795 + 3666941 * 2 ^ 59
def prefixEnd_3666941 : Nat := 4983230072969 + 3 ^ 40 * 3666941 * 2
def baseEnd_3666941 : Nat := 1882903264678642810173551

theorem tailTrace_3666941 : CollatzResearch.WordTrace tailWord_3666941 prefixEnd_3666941 1882903264678642810173551 := by
  unfold tailWord_3666941
  simp only [CollatzResearch.WordTrace]
  refine ⟨133744325808306495508512677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89162883872204330339008451 133744325808306495508512677)
  ·
    refine ⟨25077061089057467907846127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133744325808306495508512677 25077061089057467907846127)
    ·
      refine ⟨37615591633586201861769191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25077061089057467907846127 37615591633586201861769191)
      ·
        refine ⟨56423387450379302792653787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37615591633586201861769191 56423387450379302792653787)
        ·
          refine ⟨84635081175568954188980681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56423387450379302792653787 84635081175568954188980681)
          ·
            refine ⟨63476310881676715641735511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84635081175568954188980681 63476310881676715641735511)
            ·
              refine ⟨95214466322515073462603267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63476310881676715641735511 95214466322515073462603267)
              ·
                refine ⟨142821699483772610193904901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95214466322515073462603267 142821699483772610193904901)
                ·
                  refine ⟨26779068653207364411357169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142821699483772610193904901 26779068653207364411357169)
                  ·
                    refine ⟨20084301489905523308517877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26779068653207364411357169 20084301489905523308517877)
                    ·
                      refine ⟨1882903264678642810173551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20084301489905523308517877 1882903264678642810173551)
                      ·
                        rfl

theorem cell23_3666941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3666941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666941 prefixEnd_3666941 := by exact prefixLift 3666941
  have htrace : WordTrace (prefixWord ++ tailWord_3666941) baseStart_3666941 baseEnd_3666941 := by
    simpa [prefixWord, tailWord_3666941, baseEnd_3666941] using wordTrace_append hprefix tailTrace_3666941
  have hstable : (prefixWord ++ tailWord_3666941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666941).length < 2 ^ (prefixWord ++ tailWord_3666941).sum := by decide
  have hdescent : baseEnd_3666941 < baseStart_3666941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666945 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3666945 : Nat := 118140960795 + 3666945 * 2 ^ 59
def prefixEnd_3666945 : Nat := 4983230072969 + 3 ^ 40 * 3666945 * 2
def baseEnd_3666945 : Nat := 1882905318601260794523533

theorem tailTrace_3666945 : CollatzResearch.WordTrace tailWord_3666945 prefixEnd_3666945 1882905318601260794523533 := by
  unfold tailWord_3666945
  simp only [CollatzResearch.WordTrace]
  refine ⟨133744471700292004191658289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89162981133528002794438859 133744471700292004191658289)
  ·
    refine ⟨100308353775219003143743717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133744471700292004191658289 100308353775219003143743717)
    ·
      refine ⟨18807816332853563089451947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100308353775219003143743717 18807816332853563089451947)
      ·
        refine ⟨28211724499280344634177921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807816332853563089451947 28211724499280344634177921)
        ·
          refine ⟨21158793374460258475633441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28211724499280344634177921 21158793374460258475633441)
          ·
            refine ⟨15869095030845193856725081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21158793374460258475633441 15869095030845193856725081)
            ·
              refine ⟨11901821273133895392543811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15869095030845193856725081 11901821273133895392543811)
              ·
                refine ⟨17852731909700843088815717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901821273133895392543811 17852731909700843088815717)
                ·
                  refine ⟨3347387233068908079152947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17852731909700843088815717 3347387233068908079152947)
                  ·
                    refine ⟨5021080849603362118729421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347387233068908079152947 5021080849603362118729421)
                    ·
                      refine ⟨1882905318601260794523533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021080849603362118729421 1882905318601260794523533)
                      ·
                        rfl

theorem cell23_3666945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3666945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666945 prefixEnd_3666945 := by exact prefixLift 3666945
  have htrace : WordTrace (prefixWord ++ tailWord_3666945) baseStart_3666945 baseEnd_3666945 := by
    simpa [prefixWord, tailWord_3666945, baseEnd_3666945] using wordTrace_append hprefix tailTrace_3666945
  have hstable : (prefixWord ++ tailWord_3666945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666945).length < 2 ^ (prefixWord ++ tailWord_3666945).sum := by decide
  have hdescent : baseEnd_3666945 < baseStart_3666945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666961 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3666961 : Nat := 118140960795 + 3666961 * 2 ^ 59
def prefixEnd_3666961 : Nat := 4983230072969 + 3 ^ 40 * 3666961 * 2
def baseEnd_3666961 : Nat := 627637844763910910641153

theorem tailTrace_3666961 : CollatzResearch.WordTrace tailWord_3666961 prefixEnd_3666961 627637844763910910641153 := by
  unfold tailWord_3666961
  simp only [CollatzResearch.WordTrace]
  refine ⟨133745055268234038924240737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89163370178822692616160491 133745055268234038924240737)
  ·
    refine ⟨100308791451175529193180553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133745055268234038924240737 100308791451175529193180553)
    ·
      refine ⟨75231593588381646894885415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100308791451175529193180553 75231593588381646894885415)
      ·
        refine ⟨112847390382572470342328123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75231593588381646894885415 112847390382572470342328123)
        ·
          refine ⟨169271085573858705513492185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112847390382572470342328123 169271085573858705513492185)
          ·
            refine ⟨126953314180394029135119139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169271085573858705513492185 126953314180394029135119139)
            ·
              refine ⟨190429971270591043702678709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126953314180394029135119139 190429971270591043702678709)
              ·
                refine ⟨17852809806617910347126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190429971270591043702678709 17852809806617910347126129)
                ·
                  refine ⟨13389607354963432760344597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17852809806617910347126129 13389607354963432760344597)
                  ·
                    refine ⟨627637844763910910641153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13389607354963432760344597 627637844763910910641153)
                    ·
                      rfl

theorem cell23_3666961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3666961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666961 prefixEnd_3666961 := by exact prefixLift 3666961
  have htrace : WordTrace (prefixWord ++ tailWord_3666961) baseStart_3666961 baseEnd_3666961 := by
    simpa [prefixWord, tailWord_3666961, baseEnd_3666961] using wordTrace_append hprefix tailTrace_3666961
  have hstable : (prefixWord ++ tailWord_3666961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666961).length < 2 ^ (prefixWord ++ tailWord_3666961).sum := by decide
  have hdescent : baseEnd_3666961 < baseStart_3666961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666972 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3666972 : Nat := 118140960795 + 3666972 * 2 ^ 59
def prefixEnd_3666972 : Nat := 4983230072969 + 3 ^ 40 * 3666972 * 2
def baseEnd_3666972 : Nat := 1882919182578932188885909

theorem tailTrace_3666972 : CollatzResearch.WordTrace tailWord_3666972 prefixEnd_3666972 1882919182578932188885909 := by
  unfold tailWord_3666972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66872728235597093901445585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89163637647462791868594113 66872728235597093901445585)
  ·
    refine ⟨50154546176697820426084189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66872728235597093901445585 50154546176697820426084189)
    ·
      refine ⟨18807954816261682659781571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50154546176697820426084189 18807954816261682659781571)
      ·
        refine ⟨28211932224392523989672357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807954816261682659781571 28211932224392523989672357)
        ·
          refine ⟨5289737292073598248063567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28211932224392523989672357 5289737292073598248063567)
          ·
            refine ⟨7934605938110397372095351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289737292073598248063567 7934605938110397372095351)
            ·
              refine ⟨11901908907165596058143027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934605938110397372095351 11901908907165596058143027)
              ·
                refine ⟨17852863360748394087214541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901908907165596058143027 17852863360748394087214541)
                ·
                  refine ⟨6694823760280647782705453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17852863360748394087214541 6694823760280647782705453)
                  ·
                    refine ⟨2510558910105242918514545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6694823760280647782705453 2510558910105242918514545)
                    ·
                      refine ⟨1882919182578932188885909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510558910105242918514545 1882919182578932188885909)
                      ·
                        rfl

theorem cell23_3666972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3666972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666972 prefixEnd_3666972 := by exact prefixLift 3666972
  have htrace : WordTrace (prefixWord ++ tailWord_3666972) baseStart_3666972 baseEnd_3666972 := by
    simpa [prefixWord, tailWord_3666972, baseEnd_3666972] using wordTrace_append hprefix tailTrace_3666972
  have hstable : (prefixWord ++ tailWord_3666972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666972).length < 2 ^ (prefixWord ++ tailWord_3666972).sum := by decide
  have hdescent : baseEnd_3666972 < baseStart_3666972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667002 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_3667002 : Nat := 118140960795 + 3667002 * 2 ^ 59
def prefixEnd_3667002 : Nat := 4983230072969 + 3 ^ 40 * 3667002 * 2
def baseEnd_3667002 : Nat := 1882934586998567071510771

theorem tailTrace_3667002 : CollatzResearch.WordTrace tailWord_3667002 prefixEnd_3667002 1882934586998567071510771 := by
  unfold tailWord_3667002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436637665271375731620815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89164367107390335284322173 33436637665271375731620815)
  ·
    refine ⟨50154956497907063597431223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33436637665271375731620815 50154956497907063597431223)
    ·
      refine ⟨75232434746860595396146835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50154956497907063597431223 75232434746860595396146835)
      ·
        refine ⟨112848652120290893094220253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75232434746860595396146835 112848652120290893094220253)
        ·
          refine ⟨42318244545109084910332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112848652120290893094220253 42318244545109084910332595)
          ·
            refine ⟨63477366817663627365498893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42318244545109084910332595 63477366817663627365498893)
            ·
              refine ⟨23804012556623860262062085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63477366817663627365498893 23804012556623860262062085)
              ·
                refine ⟨4463252354366973799136641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23804012556623860262062085 4463252354366973799136641)
                ·
                  refine ⟨3347439265775230349352481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463252354366973799136641 3347439265775230349352481)
                  ·
                    refine ⟨2510579449331422762014361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347439265775230349352481 2510579449331422762014361)
                    ·
                      refine ⟨1882934586998567071510771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510579449331422762014361 1882934586998567071510771)
                      ·
                        rfl

theorem cell23_3667002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_3667002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667002 prefixEnd_3667002 := by exact prefixLift 3667002
  have htrace : WordTrace (prefixWord ++ tailWord_3667002) baseStart_3667002 baseEnd_3667002 := by
    simpa [prefixWord, tailWord_3667002, baseEnd_3667002] using wordTrace_append hprefix tailTrace_3667002
  have hstable : (prefixWord ++ tailWord_3667002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667002).length < 2 ^ (prefixWord ++ tailWord_3667002).sum := by decide
  have hdescent : baseEnd_3667002 < baseStart_3667002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667018 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_3667018 : Nat := 118140960795 + 3667018 * 2 ^ 59
def prefixEnd_3667018 : Nat := 4983230072969 + 3 ^ 40 * 3667018 * 2
def baseEnd_3667018 : Nat := 1882942802689039008910697

theorem tailTrace_3667018 : CollatzResearch.WordTrace tailWord_3667018 prefixEnd_3667018 1882942802689039008910697 := by
  unfold tailWord_3667018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436783557256884414766427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89164756152685025106043805 33436783557256884414766427)
  ·
    refine ⟨50155175335885326622149641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33436783557256884414766427 50155175335885326622149641)
    ·
      refine ⟨37616381501913994966612231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50155175335885326622149641 37616381501913994966612231)
      ·
        refine ⟨56424572252870992449918347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37616381501913994966612231 56424572252870992449918347)
        ·
          refine ⟨84636858379306488674877521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56424572252870992449918347 84636858379306488674877521)
          ·
            refine ⟨63477643784479866506158141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84636858379306488674877521 63477643784479866506158141)
            ·
              refine ⟨23804116419179949939809303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63477643784479866506158141 23804116419179949939809303)
              ·
                refine ⟨35706174628769924909713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23804116419179949939809303 35706174628769924909713955)
                ·
                  refine ⟨53559261943154887364570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35706174628769924909713955 53559261943154887364570933)
                  ·
                    refine ⟨5021180807170770690428525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53559261943154887364570933 5021180807170770690428525)
                    ·
                      refine ⟨1882942802689039008910697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021180807170770690428525 1882942802689039008910697)
                      ·
                        rfl

theorem cell23_3667018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_3667018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667018 prefixEnd_3667018 := by exact prefixLift 3667018
  have htrace : WordTrace (prefixWord ++ tailWord_3667018) baseStart_3667018 baseEnd_3667018 := by
    simpa [prefixWord, tailWord_3667018, baseEnd_3667018] using wordTrace_append hprefix tailTrace_3667018
  have hstable : (prefixWord ++ tailWord_3667018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667018).length < 2 ^ (prefixWord ++ tailWord_3667018).sum := by decide
  have hdescent : baseEnd_3667018 < baseStart_3667018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667042 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3667042 : Nat := 118140960795 + 3667042 * 2 ^ 59
def prefixEnd_3667042 : Nat := 4983230072969 + 3 ^ 40 * 3667042 * 2
def baseEnd_3667042 : Nat := 209217236247194101667843

theorem tailTrace_3667042 : CollatzResearch.WordTrace tailWord_3667042 prefixEnd_3667042 209217236247194101667843 := by
  unfold tailWord_3667042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33437002395235147439484845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89165339720627059838626253 33437002395235147439484845)
  ·
    refine ⟨12538875898213180289806817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33437002395235147439484845 12538875898213180289806817)
    ·
      refine ⟨9404156923659885217355113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12538875898213180289806817 9404156923659885217355113)
      ·
        refine ⟨7053117692744913913016335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9404156923659885217355113 7053117692744913913016335)
        ·
          refine ⟨10579676539117370869524503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053117692744913913016335 10579676539117370869524503)
          ·
            refine ⟨15869514808676056304286755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579676539117370869524503 15869514808676056304286755)
            ·
              refine ⟨23804272213014084456430133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15869514808676056304286755 23804272213014084456430133)
              ·
                refine ⟨2231650519970070417790325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23804272213014084456430133 2231650519970070417790325)
                ·
                  refine ⟨209217236247194101667843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2231650519970070417790325 209217236247194101667843)
                  ·
                    rfl

theorem cell23_3667042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3667042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667042 prefixEnd_3667042 := by exact prefixLift 3667042
  have htrace : WordTrace (prefixWord ++ tailWord_3667042) baseStart_3667042 baseEnd_3667042 := by
    simpa [prefixWord, tailWord_3667042, baseEnd_3667042] using wordTrace_append hprefix tailTrace_3667042
  have hstable : (prefixWord ++ tailWord_3667042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667042).length < 2 ^ (prefixWord ++ tailWord_3667042).sum := by decide
  have hdescent : baseEnd_3667042 < baseStart_3667042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667051 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 10]
def baseStart_3667051 : Nat := 118140960795 + 3667051 * 2 ^ 59
def prefixEnd_3667051 : Nat := 4983230072969 + 3 ^ 40 * 3667051 * 2
def baseEnd_3667051 : Nat := 627653249183545793266015

theorem tailTrace_3667051 : CollatzResearch.WordTrace tailWord_3667051 prefixEnd_3667051 627653249183545793266015 := by
  unfold tailWord_3667051
  simp only [CollatzResearch.WordTrace]
  refine ⟨133748337837907984295017007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89165558558605322863344671 133748337837907984295017007)
  ·
    refine ⟨200622506756861976442525511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133748337837907984295017007 200622506756861976442525511)
    ·
      refine ⟨300933760135292964663788267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200622506756861976442525511 300933760135292964663788267)
      ·
        refine ⟨451400640202939446995682401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300933760135292964663788267 451400640202939446995682401)
        ·
          refine ⟨338550480152204585246761801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451400640202939446995682401 338550480152204585246761801)
          ·
            refine ⟨253912860114153438935071351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338550480152204585246761801 253912860114153438935071351)
            ·
              refine ⟨380869290171230158402607027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253912860114153438935071351 380869290171230158402607027)
              ·
                refine ⟨571303935256845237603910541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380869290171230158402607027 571303935256845237603910541)
                ·
                  refine ⟨214238975721316964101466453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571303935256845237603910541 214238975721316964101466453)
                  ·
                    refine ⟨627653249183545793266015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 214238975721316964101466453 627653249183545793266015)
                    ·
                      rfl

theorem cell23_3667051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_3667051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667051 prefixEnd_3667051 := by exact prefixLift 3667051
  have htrace : WordTrace (prefixWord ++ tailWord_3667051) baseStart_3667051 baseEnd_3667051 := by
    simpa [prefixWord, tailWord_3667051, baseEnd_3667051] using wordTrace_append hprefix tailTrace_3667051
  have hstable : (prefixWord ++ tailWord_3667051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667051).length < 2 ^ (prefixWord ++ tailWord_3667051).sum := by decide
  have hdescent : baseEnd_3667051 < baseStart_3667051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667070 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3667070 : Nat := 118140960795 + 3667070 * 2 ^ 59
def prefixEnd_3667070 : Nat := 4983230072969 + 3 ^ 40 * 3667070 * 2
def baseEnd_3667070 : Nat := 1882969503683072805460459

theorem tailTrace_3667070 : CollatzResearch.WordTrace tailWord_3667070 prefixEnd_3667070 1882969503683072805460459 := by
  unfold tailWord_3667070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16718628853104893817494833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89166020549892767026639109 16718628853104893817494833)
  ·
    refine ⟨12538971639828670363121125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16718628853104893817494833 12538971639828670363121125)
    ·
      refine ⟨2351057182467875693085211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12538971639828670363121125 2351057182467875693085211)
      ·
        refine ⟨3526585773701813539627817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351057182467875693085211 3526585773701813539627817)
        ·
          refine ⟨2644939330276360154720863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526585773701813539627817 2644939330276360154720863)
          ·
            refine ⟨3967408995414540232081295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644939330276360154720863 3967408995414540232081295)
            ·
              refine ⟨5951113493121810348121943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967408995414540232081295 5951113493121810348121943)
              ·
                refine ⟨8926670239682715522182915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951113493121810348121943 8926670239682715522182915)
                ·
                  refine ⟨13390005359524073283274373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8926670239682715522182915 13390005359524073283274373)
                  ·
                    refine ⟨2510626004910763740613945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13390005359524073283274373 2510626004910763740613945)
                    ·
                      refine ⟨1882969503683072805460459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510626004910763740613945 1882969503683072805460459)
                      ·
                        rfl

theorem cell23_3667070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3667070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667070 prefixEnd_3667070 := by exact prefixLift 3667070
  have htrace : WordTrace (prefixWord ++ tailWord_3667070) baseStart_3667070 baseEnd_3667070 := by
    simpa [prefixWord, tailWord_3667070, baseEnd_3667070] using wordTrace_append hprefix tailTrace_3667070
  have hstable : (prefixWord ++ tailWord_3667070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667070).length < 2 ^ (prefixWord ++ tailWord_3667070).sum := by decide
  have hdescent : baseEnd_3667070 < baseStart_3667070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667075 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 4, 2]
def baseStart_3667075 : Nat := 118140960795 + 3667075 * 2 ^ 59
def prefixEnd_3667075 : Nat := 4983230072969 + 3 ^ 40 * 3667075 * 2
def baseEnd_3667075 : Nat := 1882972071086345285897935

theorem tailTrace_3667075 : CollatzResearch.WordTrace tailWord_3667075 prefixEnd_3667075 1882972071086345285897935 := by
  unfold tailWord_3667075
  simp only [CollatzResearch.WordTrace]
  refine ⟨133749213189821036393890679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89166142126547357595927119 133749213189821036393890679)
  ·
    refine ⟨200623819784731554590836019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133749213189821036393890679 200623819784731554590836019)
    ·
      refine ⟨300935729677097331886254029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200623819784731554590836019 300935729677097331886254029)
      ·
        refine ⟨112850898628911499457345261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300935729677097331886254029 112850898628911499457345261)
        ·
          refine ⟨42319086985841812296504473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112850898628911499457345261 42319086985841812296504473)
          ·
            refine ⟨31739315239381359222378355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42319086985841812296504473 31739315239381359222378355)
            ·
              refine ⟨47608972859072038833567533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31739315239381359222378355 47608972859072038833567533)
              ·
                refine ⟨17853364822152014562587825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47608972859072038833567533 17853364822152014562587825)
                ·
                  refine ⟨13390023616614010921940869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17853364822152014562587825 13390023616614010921940869)
                  ·
                    refine ⟨2510629428115127047863913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13390023616614010921940869 2510629428115127047863913)
                    ·
                      refine ⟨1882972071086345285897935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510629428115127047863913 1882972071086345285897935)
                      ·
                        rfl

theorem cell23_3667075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_3667075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667075 prefixEnd_3667075 := by exact prefixLift 3667075
  have htrace : WordTrace (prefixWord ++ tailWord_3667075) baseStart_3667075 baseEnd_3667075 := by
    simpa [prefixWord, tailWord_3667075, baseEnd_3667075] using wordTrace_append hprefix tailTrace_3667075
  have hstable : (prefixWord ++ tailWord_3667075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667075).length < 2 ^ (prefixWord ++ tailWord_3667075).sum := by decide
  have hdescent : baseEnd_3667075 < baseStart_3667075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667095 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3667095 : Nat := 118140960795 + 3667095 * 2 ^ 59
def prefixEnd_3667095 : Nat := 4983230072969 + 3 ^ 40 * 3667095 * 2
def baseEnd_3667095 : Nat := 1882982340699435207647843

theorem tailTrace_3667095 : CollatzResearch.WordTrace tailWord_3667095 prefixEnd_3667095 1882982340699435207647843 := by
  unfold tailWord_3667095
  simp only [CollatzResearch.WordTrace]
  refine ⟨133749942649748579809618739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89166628433165719873079159 133749942649748579809618739)
  ·
    refine ⟨200624913974622869714428109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133749942649748579809618739 200624913974622869714428109)
    ·
      refine ⟨75234342740483576142910541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200624913974622869714428109 75234342740483576142910541)
      ·
        refine ⟨28212878527681341053591453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75234342740483576142910541 28212878527681341053591453)
        ·
          refine ⟨10579829447880502895096795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28212878527681341053591453 10579829447880502895096795)
          ·
            refine ⟨15869744171820754342645193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579829447880502895096795 15869744171820754342645193)
            ·
              refine ⟨11902308128865565756983895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15869744171820754342645193 11902308128865565756983895)
              ·
                refine ⟨17853462193298348635475843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11902308128865565756983895 17853462193298348635475843)
                ·
                  refine ⟨26780193289947522953213765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17853462193298348635475843 26780193289947522953213765)
                  ·
                    refine ⟨5021286241865160553727581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26780193289947522953213765 5021286241865160553727581)
                    ·
                      refine ⟨1882982340699435207647843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021286241865160553727581 1882982340699435207647843)
                      ·
                        rfl

theorem cell23_3667095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3667095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667095 prefixEnd_3667095 := by exact prefixLift 3667095
  have htrace : WordTrace (prefixWord ++ tailWord_3667095) baseStart_3667095 baseEnd_3667095 := by
    simpa [prefixWord, tailWord_3667095, baseEnd_3667095] using wordTrace_append hprefix tailTrace_3667095
  have hstable : (prefixWord ++ tailWord_3667095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667095).length < 2 ^ (prefixWord ++ tailWord_3667095).sum := by decide
  have hdescent : baseEnd_3667095 < baseStart_3667095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667132 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 6]
def baseStart_3667132 : Nat := 118140960795 + 3667132 * 2 ^ 59
def prefixEnd_3667132 : Nat := 4983230072969 + 3 ^ 40 * 3667132 * 2
def baseEnd_3667132 : Nat := 209222371053739062542797

theorem tailTrace_3667132 : CollatzResearch.WordTrace tailWord_3667132 prefixEnd_3667132 209222371053739062542797 := by
  unfold tailWord_3667132
  simp only [CollatzResearch.WordTrace]
  refine ⟨66875646075307267564357825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89167528100409690085810433 66875646075307267564357825)
  ·
    refine ⟨50156734556480450673268369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66875646075307267564357825 50156734556480450673268369)
    ·
      refine ⟨37617550917360338004951277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50156734556480450673268369 37617550917360338004951277)
      ·
        refine ⟨14106581594010126751856729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37617550917360338004951277 14106581594010126751856729)
        ·
          refine ⟨10579936195507595063892547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14106581594010126751856729 10579936195507595063892547)
          ·
            refine ⟨15869904293261392595838821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579936195507595063892547 15869904293261392595838821)
            ·
              refine ⟨2975607054986511111719779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15869904293261392595838821 2975607054986511111719779)
              ·
                refine ⟨4463410582479766667579669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975607054986511111719779 4463410582479766667579669)
                ·
                  refine ⟨209222371053739062542797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4463410582479766667579669 209222371053739062542797)
                  ·
                    rfl

theorem cell23_3667132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_3667132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667132 prefixEnd_3667132 := by exact prefixLift 3667132
  have htrace : WordTrace (prefixWord ++ tailWord_3667132) baseStart_3667132 baseEnd_3667132 := by
    simpa [prefixWord, tailWord_3667132, baseEnd_3667132] using wordTrace_append hprefix tailTrace_3667132
  have hstable : (prefixWord ++ tailWord_3667132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667132).length < 2 ^ (prefixWord ++ tailWord_3667132).sum := by decide
  have hdescent : baseEnd_3667132 < baseStart_3667132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667135 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 5, 2]
def baseStart_3667135 : Nat := 118140960795 + 3667135 * 2 ^ 59
def prefixEnd_3667135 : Nat := 4983230072969 + 3 ^ 40 * 3667135 * 2
def baseEnd_3667135 : Nat := 1883002879925615051147659

theorem tailTrace_3667135 : CollatzResearch.WordTrace tailWord_3667135 prefixEnd_3667135 1883002879925615051147659 := by
  unfold tailWord_3667135
  simp only [CollatzResearch.WordTrace]
  refine ⟨133751401569603666641074859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89167601046402444427383239 133751401569603666641074859)
  ·
    refine ⟨200627102354405499961612289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133751401569603666641074859 200627102354405499961612289)
    ·
      refine ⟨150470326765804124971209217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200627102354405499961612289 150470326765804124971209217)
      ·
        refine ⟨112852745074353093728406913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150470326765804124971209217 112852745074353093728406913)
        ·
          refine ⟨84639558805764820296305185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112852745074353093728406913 84639558805764820296305185)
          ·
            refine ⟨63479669104323615222228889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84639558805764820296305185 63479669104323615222228889)
            ·
              refine ⟨47609751828242711416671667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63479669104323615222228889 47609751828242711416671667)
              ·
                refine ⟨71414627742364067125007501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47609751828242711416671667 71414627742364067125007501)
                ·
                  refine ⟨26780485403386525171877813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71414627742364067125007501 26780485403386525171877813)
                  ·
                    refine ⟨2510670506567486734863545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26780485403386525171877813 2510670506567486734863545)
                    ·
                      refine ⟨1883002879925615051147659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510670506567486734863545 1883002879925615051147659)
                      ·
                        rfl

theorem cell23_3667135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_3667135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667135 prefixEnd_3667135 := by exact prefixLift 3667135
  have htrace : WordTrace (prefixWord ++ tailWord_3667135) baseStart_3667135 baseEnd_3667135 := by
    simpa [prefixWord, tailWord_3667135, baseEnd_3667135] using wordTrace_append hprefix tailTrace_3667135
  have hstable : (prefixWord ++ tailWord_3667135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667135).length < 2 ^ (prefixWord ++ tailWord_3667135).sum := by decide
  have hdescent : baseEnd_3667135 < baseStart_3667135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667199 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 3, 2, 2]
def baseStart_3667199 : Nat := 118140960795 + 3667199 * 2 ^ 59
def prefixEnd_3667199 : Nat := 4983230072969 + 3 ^ 40 * 3667199 * 2
def baseEnd_3667199 : Nat := 1883035742687502800747365

theorem tailTrace_3667199 : CollatzResearch.WordTrace tailWord_3667199 prefixEnd_3667199 1883035742687502800747365 := by
  unfold tailWord_3667199
  simp only [CollatzResearch.WordTrace]
  refine ⟨133753735841371805571404651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89169157227581203714269767 133753735841371805571404651)
  ·
    refine ⟨200630603762057708357106977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133753735841371805571404651 200630603762057708357106977)
    ·
      refine ⟨150472952821543281267830233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200630603762057708357106977 150472952821543281267830233)
      ·
        refine ⟨112854714616157460950872675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150472952821543281267830233 112854714616157460950872675)
        ·
          refine ⟨169282071924236191426309013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112854714616157460950872675 169282071924236191426309013)
          ·
            refine ⟨7935097121448571473108235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169282071924236191426309013 7935097121448571473108235)
            ·
              refine ⟨11902645682172857209662353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935097121448571473108235 11902645682172857209662353)
              ·
                refine ⟨8926984261629642907246765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11902645682172857209662353 8926984261629642907246765)
                ·
                  refine ⟨3347619098111116090217537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8926984261629642907246765 3347619098111116090217537)
                  ·
                    refine ⟨2510714323583337067663153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347619098111116090217537 2510714323583337067663153)
                    ·
                      refine ⟨1883035742687502800747365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510714323583337067663153 1883035742687502800747365)
                      ·
                        rfl

theorem cell23_3667199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_3667199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667199 prefixEnd_3667199 := by exact prefixLift 3667199
  have htrace : WordTrace (prefixWord ++ tailWord_3667199) baseStart_3667199 baseEnd_3667199 := by
    simpa [prefixWord, tailWord_3667199, baseEnd_3667199] using wordTrace_append hprefix tailTrace_3667199
  have hstable : (prefixWord ++ tailWord_3667199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667199).length < 2 ^ (prefixWord ++ tailWord_3667199).sum := by decide
  have hdescent : baseEnd_3667199 < baseStart_3667199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667205 : List Nat := [1, 3, 1, 1, 2, 1, 7, 7]
def baseStart_3667205 : Nat := 118140960795 + 3667205 * 2 ^ 59
def prefixEnd_3667205 : Nat := 4983230072969 + 3 ^ 40 * 3667205 * 2
def baseEnd_3667205 : Nat := 69742178650793695454531

theorem tailTrace_3667205 : CollatzResearch.WordTrace tailWord_3667205 prefixEnd_3667205 69742178650793695454531 := by
  unfold tailWord_3667205
  simp only [CollatzResearch.WordTrace]
  refine ⟨133753954679350068596123069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89169303119566712397415379 133753954679350068596123069)
  ·
    refine ⟨50157733004756275723546151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133753954679350068596123069 50157733004756275723546151)
    ·
      refine ⟨75236599507134413585319227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50157733004756275723546151 75236599507134413585319227)
      ·
        refine ⟨112854899260701620377978841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75236599507134413585319227 112854899260701620377978841)
        ·
          refine ⟨84641174445526215283484131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112854899260701620377978841 84641174445526215283484131)
          ·
            refine ⟨126961761668289322925226197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84641174445526215283484131 126961761668289322925226197)
            ·
              refine ⟨2975666289100531006059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126961761668289322925226197 2975666289100531006059989)
              ·
                refine ⟨69742178650793695454531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2975666289100531006059989 69742178650793695454531)
                ·
                  rfl

theorem cell23_3667205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 7].length) (baseStart_3667205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667205 prefixEnd_3667205 := by exact prefixLift 3667205
  have htrace : WordTrace (prefixWord ++ tailWord_3667205) baseStart_3667205 baseEnd_3667205 := by
    simpa [prefixWord, tailWord_3667205, baseEnd_3667205] using wordTrace_append hprefix tailTrace_3667205
  have hstable : (prefixWord ++ tailWord_3667205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667205).length < 2 ^ (prefixWord ++ tailWord_3667205).sum := by decide
  have hdescent : baseEnd_3667205 < baseStart_3667205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667249 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3667249 : Nat := 118140960795 + 3667249 * 2 ^ 59
def prefixEnd_3667249 : Nat := 4983230072969 + 3 ^ 40 * 3667249 * 2
def baseEnd_3667249 : Nat := 1883061416720227605122135

theorem tailTrace_3667249 : CollatzResearch.WordTrace tailWord_3667249 prefixEnd_3667249 1883061416720227605122135 := by
  unfold tailWord_3667249
  simp only [CollatzResearch.WordTrace]
  refine ⟨133755559491190664110724801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89170372994127109407149867 133755559491190664110724801)
  ·
    refine ⟨100316669618392998083043601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133755559491190664110724801 100316669618392998083043601)
    ·
      refine ⟨75237502213794748562282701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100316669618392998083043601 75237502213794748562282701)
      ·
        refine ⟨28214063330173030710856013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75237502213794748562282701 28214063330173030710856013)
        ·
          refine ⟨10580273748814886516571005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28214063330173030710856013 10580273748814886516571005)
          ·
            refine ⟨3967602655805582443714127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10580273748814886516571005 3967602655805582443714127)
            ·
              refine ⟨5951403983708373665571191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967602655805582443714127 5951403983708373665571191)
              ·
                refine ⟨8927105975562560498356787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951403983708373665571191 8927105975562560498356787)
                ·
                  refine ⟨13390658963343840747535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927105975562560498356787 13390658963343840747535181)
                  ·
                    refine ⟨5021497111253940280325693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13390658963343840747535181 5021497111253940280325693)
                    ·
                      refine ⟨1883061416720227605122135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021497111253940280325693 1883061416720227605122135)
                      ·
                        rfl

theorem cell23_3667249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3667249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667249 prefixEnd_3667249 := by exact prefixLift 3667249
  have htrace : WordTrace (prefixWord ++ tailWord_3667249) baseStart_3667249 baseEnd_3667249 := by
    simpa [prefixWord, tailWord_3667249, baseEnd_3667249] using wordTrace_append hprefix tailTrace_3667249
  have hstable : (prefixWord ++ tailWord_3667249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667249).length < 2 ^ (prefixWord ++ tailWord_3667249).sum := by decide
  have hdescent : baseEnd_3667249 < baseStart_3667249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667272 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_3667272 : Nat := 118140960795 + 3667272 * 2 ^ 59
def prefixEnd_3667272 : Nat := 4983230072969 + 3 ^ 40 * 3667272 * 2
def baseEnd_3667272 : Nat := 1883073226775281015134529

theorem tailTrace_3667272 : CollatzResearch.WordTrace tailWord_3667272 prefixEnd_3667272 1883073226775281015134529 := by
  unfold tailWord_3667272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66878199185053669519406035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89170932246738226025874713 66878199185053669519406035)
  ·
    refine ⟨100317298777580504279109053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66878199185053669519406035 100317298777580504279109053)
    ·
      refine ⟨37618987041592689104665895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100317298777580504279109053 37618987041592689104665895)
      ·
        refine ⟨56428480562389033656998843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37618987041592689104665895 56428480562389033656998843)
        ·
          refine ⟨84642720843583550485498265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56428480562389033656998843 84642720843583550485498265)
          ·
            refine ⟨63482040632687662864123699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84642720843583550485498265 63482040632687662864123699)
            ·
              refine ⟨95223060949031494296185549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63482040632687662864123699 95223060949031494296185549)
              ·
                refine ⟨35708647855886810361069581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95223060949031494296185549 35708647855886810361069581)
                ·
                  refine ⟨13390742945957553885401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35708647855886810361069581 13390742945957553885401093)
                  ·
                    refine ⟨2510764302367041353512705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13390742945957553885401093 2510764302367041353512705)
                    ·
                      refine ⟨1883073226775281015134529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510764302367041353512705 1883073226775281015134529)
                      ·
                        rfl

theorem cell23_3667272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_3667272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667272 prefixEnd_3667272 := by exact prefixLift 3667272
  have htrace : WordTrace (prefixWord ++ tailWord_3667272) baseStart_3667272 baseEnd_3667272 := by
    simpa [prefixWord, tailWord_3667272, baseEnd_3667272] using wordTrace_append hprefix tailTrace_3667272
  have hstable : (prefixWord ++ tailWord_3667272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667272).length < 2 ^ (prefixWord ++ tailWord_3667272).sum := by decide
  have hdescent : baseEnd_3667272 < baseStart_3667272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667289 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 4, 2, 2]
def baseStart_3667289 : Nat := 118140960795 + 3667289 * 2 ^ 59
def prefixEnd_3667289 : Nat := 4983230072969 + 3 ^ 40 * 3667289 * 2
def baseEnd_3667289 : Nat := 1883081955946407448621951

theorem tailTrace_3667289 : CollatzResearch.WordTrace tailWord_3667289 prefixEnd_3667289 1883081955946407448621951 := by
  unfold tailWord_3667289
  simp only [CollatzResearch.WordTrace]
  refine ⟨133757018411045750942180921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89171345607363833961453947 133757018411045750942180921)
  ·
    refine ⟨100317763808284313206635691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133757018411045750942180921 100317763808284313206635691)
    ·
      refine ⟨150476645712426469809953537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100317763808284313206635691 150476645712426469809953537)
      ·
        refine ⟨112857484284319852357465153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150476645712426469809953537 112857484284319852357465153)
        ·
          refine ⟨84643113213239889268098865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112857484284319852357465153 84643113213239889268098865)
          ·
            refine ⟨63482334909929916951074149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84643113213239889268098865 63482334909929916951074149)
            ·
              refine ⟨11902937795611859428326403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63482334909929916951074149 11902937795611859428326403)
              ·
                refine ⟨17854406693417789142489605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11902937795611859428326403 17854406693417789142489605)
                ·
                  refine ⟨3347701255015835464216801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17854406693417789142489605 3347701255015835464216801)
                  ·
                    refine ⟨2510775941261876598162601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347701255015835464216801 2510775941261876598162601)
                    ·
                      refine ⟨1883081955946407448621951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510775941261876598162601 1883081955946407448621951)
                      ·
                        rfl

theorem cell23_3667289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_3667289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667289 prefixEnd_3667289 := by exact prefixLift 3667289
  have htrace : WordTrace (prefixWord ++ tailWord_3667289) baseStart_3667289 baseEnd_3667289 := by
    simpa [prefixWord, tailWord_3667289, baseEnd_3667289] using wordTrace_append hprefix tailTrace_3667289
  have hstable : (prefixWord ++ tailWord_3667289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667289).length < 2 ^ (prefixWord ++ tailWord_3667289).sum := by decide
  have hdescent : baseEnd_3667289 < baseStart_3667289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667310 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3667310 : Nat := 118140960795 + 3667310 * 2 ^ 59
def prefixEnd_3667310 : Nat := 4983230072969 + 3 ^ 40 * 3667310 * 2
def baseEnd_3667310 : Nat := 1883092739040151866459355

theorem tailTrace_3667310 : CollatzResearch.WordTrace tailWord_3667310 prefixEnd_3667310 1883092739040151866459355 := by
  unfold tailWord_3667310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16719723042996208941086923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89171856229313114352463589 16719723042996208941086923)
  ·
    refine ⟨25079584564494313411630385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16719723042996208941086923 25079584564494313411630385)
    ·
      refine ⟨18809688423370735058722789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25079584564494313411630385 18809688423370735058722789)
      ·
        refine ⟨3526816579382012823510523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18809688423370735058722789 3526816579382012823510523)
        ·
          refine ⟨5290224869073019235265785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526816579382012823510523 5290224869073019235265785)
          ·
            refine ⟨3967668651804764426449339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5290224869073019235265785 3967668651804764426449339)
            ·
              refine ⟨5951502977707146639674009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967668651804764426449339 5951502977707146639674009)
              ·
                refine ⟨4463627233280359979755507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951502977707146639674009 4463627233280359979755507)
                ·
                  refine ⟨6695440849920539969633261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463627233280359979755507 6695440849920539969633261)
                  ·
                    refine ⟨2510790318720202488612473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6695440849920539969633261 2510790318720202488612473)
                    ·
                      refine ⟨1883092739040151866459355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510790318720202488612473 1883092739040151866459355)
                      ·
                        rfl

theorem cell23_3667310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3667310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667310 prefixEnd_3667310 := by exact prefixLift 3667310
  have htrace : WordTrace (prefixWord ++ tailWord_3667310) baseStart_3667310 baseEnd_3667310 := by
    simpa [prefixWord, tailWord_3667310, baseEnd_3667310] using wordTrace_append hprefix tailTrace_3667310
  have hstable : (prefixWord ++ tailWord_3667310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667310).length < 2 ^ (prefixWord ++ tailWord_3667310).sum := by decide
  have hdescent : baseEnd_3667310 < baseStart_3667310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667356 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3667356 : Nat := 118140960795 + 3667356 * 2 ^ 59
def prefixEnd_3667356 : Nat := 4983230072969 + 3 ^ 40 * 3667356 * 2
def baseEnd_3667356 : Nat := 1883116359150258686484143

theorem tailTrace_3667356 : CollatzResearch.WordTrace tailWord_3667356 prefixEnd_3667356 1883116359150258686484143 := by
  unfold tailWord_3667356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66879731050901510692434961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89172974734535347589913281 66879731050901510692434961)
  ·
    refine ⟨50159798288176133019326221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66879731050901510692434961 50159798288176133019326221)
    ·
      refine ⟨18809924358066049882247333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50159798288176133019326221 18809924358066049882247333)
      ·
        refine ⟨3526860817137384352921375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18809924358066049882247333 3526860817137384352921375)
        ·
          refine ⟨5290291225706076529382063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526860817137384352921375 5290291225706076529382063)
          ·
            refine ⟨7935436838559114794073095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290291225706076529382063 7935436838559114794073095)
            ·
              refine ⟨11903155257838672191109643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935436838559114794073095 11903155257838672191109643)
              ·
                refine ⟨17854732886758008286664465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903155257838672191109643 17854732886758008286664465)
                ·
                  refine ⟨13391049665068506214998349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17854732886758008286664465 13391049665068506214998349)
                  ·
                    refine ⟨5021643624400689830624381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13391049665068506214998349 5021643624400689830624381)
                    ·
                      refine ⟨1883116359150258686484143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021643624400689830624381 1883116359150258686484143)
                      ·
                        rfl

theorem cell23_3667356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3667356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667356 prefixEnd_3667356 := by exact prefixLift 3667356
  have htrace : WordTrace (prefixWord ++ tailWord_3667356) baseStart_3667356 baseEnd_3667356 := by
    simpa [prefixWord, tailWord_3667356, baseEnd_3667356] using wordTrace_append hprefix tailTrace_3667356
  have hstable : (prefixWord ++ tailWord_3667356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667356).length < 2 ^ (prefixWord ++ tailWord_3667356).sum := by decide
  have hdescent : baseEnd_3667356 < baseStart_3667356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667372 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_3667372 : Nat := 118140960795 + 3667372 * 2 ^ 59
def prefixEnd_3667372 : Nat := 4983230072969 + 3 ^ 40 * 3667372 * 2
def baseEnd_3667372 : Nat := 627708191613576874628023

theorem tailTrace_3667372 : CollatzResearch.WordTrace tailWord_3667372 prefixEnd_3667372 627708191613576874628023 := by
  unfold tailWord_3667372
  simp only [CollatzResearch.WordTrace]
  refine ⟨66880022834872528058726185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89173363779830037411634913 66880022834872528058726185)
  ·
    refine ⟨50160017126154396044044639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66880022834872528058726185 50160017126154396044044639)
    ·
      refine ⟨75240025689231594066066959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50160017126154396044044639 75240025689231594066066959)
      ·
        refine ⟨112860038533847391099100439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75240025689231594066066959 112860038533847391099100439)
        ·
          refine ⟨169290057800771086648650659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112860038533847391099100439 169290057800771086648650659)
          ·
            refine ⟨253935086701156629972975989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169290057800771086648650659 253935086701156629972975989)
            ·
              refine ⟨23806414378233434059966499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253935086701156629972975989 23806414378233434059966499)
              ·
                refine ⟨35709621567350151089949749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23806414378233434059966499 35709621567350151089949749)
                ·
                  refine ⟨3347777021939076664682789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35709621567350151089949749 3347777021939076664682789)
                  ·
                    refine ⟨627708191613576874628023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3347777021939076664682789 627708191613576874628023)
                    ·
                      rfl

theorem cell23_3667372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_3667372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667372 prefixEnd_3667372 := by exact prefixLift 3667372
  have htrace : WordTrace (prefixWord ++ tailWord_3667372) baseStart_3667372 baseEnd_3667372 := by
    simpa [prefixWord, tailWord_3667372, baseEnd_3667372] using wordTrace_append hprefix tailTrace_3667372
  have hstable : (prefixWord ++ tailWord_3667372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667372).length < 2 ^ (prefixWord ++ tailWord_3667372).sum := by decide
  have hdescent : baseEnd_3667372 < baseStart_3667372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667375 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_3667375 : Nat := 118140960795 + 3667375 * 2 ^ 59
def prefixEnd_3667375 : Nat := 4983230072969 + 3 ^ 40 * 3667375 * 2
def baseEnd_3667375 : Nat := 1883126115282694112146555

theorem tailTrace_3667375 : CollatzResearch.WordTrace tailWord_3667375 prefixEnd_3667375 1883126115282694112146555 := by
  unfold tailWord_3667375
  simp only [CollatzResearch.WordTrace]
  refine ⟨133760155088734187629811579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89173436725822791753207719 133760155088734187629811579)
  ·
    refine ⟨200640232633101281444717369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133760155088734187629811579 200640232633101281444717369)
    ·
      refine ⟨150480174474825961083538027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200640232633101281444717369 150480174474825961083538027)
      ·
        refine ⟨225720261712238941625307041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150480174474825961083538027 225720261712238941625307041)
        ·
          refine ⟨169290196284179206218980281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225720261712238941625307041 169290196284179206218980281)
          ·
            refine ⟨126967647213134404664235211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169290196284179206218980281 126967647213134404664235211)
            ·
              refine ⟨190451470819701606996352817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126967647213134404664235211 190451470819701606996352817)
              ·
                refine ⟨142838603114776205247264613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190451470819701606996352817 142838603114776205247264613)
                ·
                  refine ⟨26782238084020538483862115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142838603114776205247264613 26782238084020538483862115)
                  ·
                    refine ⟨40173357126030807725793173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26782238084020538483862115 40173357126030807725793173)
                    ·
                      refine ⟨1883126115282694112146555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40173357126030807725793173 1883126115282694112146555)
                      ·
                        rfl

theorem cell23_3667375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_3667375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667375 prefixEnd_3667375 := by exact prefixLift 3667375
  have htrace : WordTrace (prefixWord ++ tailWord_3667375) baseStart_3667375 baseEnd_3667375 := by
    simpa [prefixWord, tailWord_3667375, baseEnd_3667375] using wordTrace_append hprefix tailTrace_3667375
  have hstable : (prefixWord ++ tailWord_3667375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667375).length < 2 ^ (prefixWord ++ tailWord_3667375).sum := by decide
  have hdescent : baseEnd_3667375 < baseStart_3667375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667396 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3667396 : Nat := 118140960795 + 3667396 * 2 ^ 59
def prefixEnd_3667396 : Nat := 4983230072969 + 3 ^ 40 * 3667396 * 2
def baseEnd_3667396 : Nat := 1883136898376438529983959

theorem tailTrace_3667396 : CollatzResearch.WordTrace tailWord_3667396 prefixEnd_3667396 1883136898376438529983959 := by
  unfold tailWord_3667396
  simp only [CollatzResearch.WordTrace]
  refine ⟨66880460510829054108163021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89173947347772072144217361 66880460510829054108163021)
  ·
    refine ⟨25080172691560895290561133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66880460510829054108163021 25080172691560895290561133)
    ·
      refine ⟨9405064759335335733960425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25080172691560895290561133 9405064759335335733960425)
      ·
        refine ⟨7053798569501501800470319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405064759335335733960425 7053798569501501800470319)
        ·
          refine ⟨10580697854252252700705479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053798569501501800470319 10580697854252252700705479)
          ·
            refine ⟨15871046781378379051058219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10580697854252252700705479 15871046781378379051058219)
            ·
              refine ⟨23806570172067568576587329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871046781378379051058219 23806570172067568576587329)
              ·
                refine ⟨17854927629050676432440497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23806570172067568576587329 17854927629050676432440497)
                ·
                  refine ⟨13391195721788007324330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17854927629050676432440497 13391195721788007324330373)
                  ·
                    refine ⟨2510849197835251373311945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13391195721788007324330373 2510849197835251373311945)
                    ·
                      refine ⟨1883136898376438529983959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510849197835251373311945 1883136898376438529983959)
                      ·
                        rfl

theorem cell23_3667396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3667396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667396 prefixEnd_3667396 := by exact prefixLift 3667396
  have htrace : WordTrace (prefixWord ++ tailWord_3667396) baseStart_3667396 baseEnd_3667396 := by
    simpa [prefixWord, tailWord_3667396, baseEnd_3667396] using wordTrace_append hprefix tailTrace_3667396
  have hstable : (prefixWord ++ tailWord_3667396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667396).length < 2 ^ (prefixWord ++ tailWord_3667396).sum := by decide
  have hdescent : baseEnd_3667396 < baseStart_3667396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667402 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_3667402 : Nat := 118140960795 + 3667402 * 2 ^ 59
def prefixEnd_3667402 : Nat := 4983230072969 + 3 ^ 40 * 3667402 * 2
def baseEnd_3667402 : Nat := 209237775473373945167659

theorem tailTrace_3667402 : CollatzResearch.WordTrace tailWord_3667402 prefixEnd_3667402 209237775473373945167659 := by
  unfold tailWord_3667402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440284964909092810261115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89174093239757580827362973 33440284964909092810261115)
  ·
    refine ⟨50160427447363639215391673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33440284964909092810261115 50160427447363639215391673)
    ·
      refine ⟨37620320585522729411543755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50160427447363639215391673 37620320585522729411543755)
      ·
        refine ⟨56430480878284094117315633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620320585522729411543755 56430480878284094117315633)
        ·
          refine ⟨42322860658713070587986725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56430480878284094117315633 42322860658713070587986725)
          ·
            refine ⟨7935536373508700735247511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42322860658713070587986725 7935536373508700735247511)
            ·
              refine ⟨11903304560263051102871267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935536373508700735247511 11903304560263051102871267)
              ·
                refine ⟨17854956840394576654306901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903304560263051102871267 17854956840394576654306901)
                ·
                  refine ⟨209237775473373945167659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17854956840394576654306901 209237775473373945167659)
                  ·
                    rfl

theorem cell23_3667402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_3667402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667402 prefixEnd_3667402 := by exact prefixLift 3667402
  have htrace : WordTrace (prefixWord ++ tailWord_3667402) baseStart_3667402 baseEnd_3667402 := by
    simpa [prefixWord, tailWord_3667402, baseEnd_3667402] using wordTrace_append hprefix tailTrace_3667402
  have hstable : (prefixWord ++ tailWord_3667402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667402).length < 2 ^ (prefixWord ++ tailWord_3667402).sum := by decide
  have hdescent : baseEnd_3667402 < baseStart_3667402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667406 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3667406 : Nat := 118140960795 + 3667406 * 2 ^ 59
def prefixEnd_3667406 : Nat := 4983230072969 + 3 ^ 40 * 3667406 * 2
def baseEnd_3667406 : Nat := 627714011060994496952971

theorem tailTrace_3667406 : CollatzResearch.WordTrace tailWord_3667406 prefixEnd_3667406 627714011060994496952971 := by
  unfold tailWord_3667406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720160718952734990523759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89174190501081253282793381 16720160718952734990523759)
  ·
    refine ⟨25080241078429102485785639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16720160718952734990523759 25080241078429102485785639)
    ·
      refine ⟨37620361617643653728678459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25080241078429102485785639 37620361617643653728678459)
      ·
        refine ⟨56430542426465480593017689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620361617643653728678459 56430542426465480593017689)
        ·
          refine ⟨42322906819849110444763267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56430542426465480593017689 42322906819849110444763267)
          ·
            refine ⟨63484360229773665667144901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42322906819849110444763267 63484360229773665667144901)
            ·
              refine ⟨11903317543082562312589669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63484360229773665667144901 11903317543082562312589669)
              ·
                refine ⟨2231872039327980433610563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11903317543082562312589669 2231872039327980433610563)
                ·
                  refine ⟨3347808058991970650415845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231872039327980433610563 3347808058991970650415845)
                  ·
                    refine ⟨627714011060994496952971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3347808058991970650415845 627714011060994496952971)
                    ·
                      rfl

theorem cell23_3667406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3667406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667406 prefixEnd_3667406 := by exact prefixLift 3667406
  have htrace : WordTrace (prefixWord ++ tailWord_3667406) baseStart_3667406 baseEnd_3667406 := by
    simpa [prefixWord, tailWord_3667406, baseEnd_3667406] using wordTrace_append hprefix tailTrace_3667406
  have hstable : (prefixWord ++ tailWord_3667406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667406).length < 2 ^ (prefixWord ++ tailWord_3667406).sum := by decide
  have hdescent : baseEnd_3667406 < baseStart_3667406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667439 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 5, 2]
def baseStart_3667439 : Nat := 118140960795 + 3667439 * 2 ^ 59
def prefixEnd_3667439 : Nat := 4983230072969 + 3 ^ 40 * 3667439 * 2
def baseEnd_3667439 : Nat := 1883158978044581861746261

theorem tailTrace_3667439 : CollatzResearch.WordTrace tailWord_3667439 prefixEnd_3667439 1883158978044581861746261 := by
  unfold tailWord_3667439
  simp only [CollatzResearch.WordTrace]
  refine ⟨133762489360502326560141371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89174992907001551040094247 133762489360502326560141371)
  ·
    refine ⟨200643734040753489840212057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133762489360502326560141371 200643734040753489840212057)
    ·
      refine ⟨150482800530565117380159043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200643734040753489840212057 150482800530565117380159043)
      ·
        refine ⟨225724200795847676070238565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150482800530565117380159043 225724200795847676070238565)
        ·
          refine ⟨42323287649221439263169731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225724200795847676070238565 42323287649221439263169731)
          ·
            refine ⟨63484931473832158894754597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42323287649221439263169731 63484931473832158894754597)
            ·
              refine ⟨11903424651343529792766487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63484931473832158894754597 11903424651343529792766487)
              ·
                refine ⟨17855136977015294689149731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903424651343529792766487 17855136977015294689149731)
                ·
                  refine ⟨26782705465522942033724597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17855136977015294689149731 26782705465522942033724597)
                  ·
                    refine ⟨2510878637392775815661681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26782705465522942033724597 2510878637392775815661681)
                    ·
                      refine ⟨1883158978044581861746261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510878637392775815661681 1883158978044581861746261)
                      ·
                        rfl

theorem cell23_3667439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5, 2].length) (baseStart_3667439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667439 prefixEnd_3667439 := by exact prefixLift 3667439
  have htrace : WordTrace (prefixWord ++ tailWord_3667439) baseStart_3667439 baseEnd_3667439 := by
    simpa [prefixWord, tailWord_3667439, baseEnd_3667439] using wordTrace_append hprefix tailTrace_3667439
  have hstable : (prefixWord ++ tailWord_3667439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667439).length < 2 ^ (prefixWord ++ tailWord_3667439).sum := by decide
  have hdescent : baseEnd_3667439 < baseStart_3667439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667463 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3667463 : Nat := 118140960795 + 3667463 * 2 ^ 59
def prefixEnd_3667463 : Nat := 4983230072969 + 3 ^ 40 * 3667463 * 2
def baseEnd_3667463 : Nat := 1883171301580289767846151

theorem tailTrace_3667463 : CollatzResearch.WordTrace tailWord_3667463 prefixEnd_3667463 1883171301580289767846151 := by
  unfold tailWord_3667463
  simp only [CollatzResearch.WordTrace]
  refine ⟨133763364712415378659015043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89175576474943585772676695 133763364712415378659015043)
  ·
    refine ⟨200645047068623067988522565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133763364712415378659015043 200645047068623067988522565)
    ·
      refine ⟨37620946325366825247847981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200645047068623067988522565 37620946325366825247847981)
      ·
        refine ⟨14107854872012559467942993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37620946325366825247847981 14107854872012559467942993)
        ·
          refine ⟨10580891154009419600957245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14107854872012559467942993 10580891154009419600957245)
          ·
            refine ⟨3967834182753532350358967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10580891154009419600957245 3967834182753532350358967)
            ·
              refine ⟨5951751274130298525538451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967834182753532350358967 5951751274130298525538451)
              ·
                refine ⟨8927626911195447788307677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951751274130298525538451 8927626911195447788307677)
                ·
                  refine ⟨3347860091698292920615379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8927626911195447788307677 3347860091698292920615379)
                  ·
                    refine ⟨5021790137547439380923069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347860091698292920615379 5021790137547439380923069)
                    ·
                      refine ⟨1883171301580289767846151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021790137547439380923069 1883171301580289767846151)
                      ·
                        rfl

theorem cell23_3667463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3667463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667463 prefixEnd_3667463 := by exact prefixLift 3667463
  have htrace : WordTrace (prefixWord ++ tailWord_3667463) baseStart_3667463 baseEnd_3667463 := by
    simpa [prefixWord, tailWord_3667463, baseEnd_3667463] using wordTrace_append hprefix tailTrace_3667463
  have hstable : (prefixWord ++ tailWord_3667463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667463).length < 2 ^ (prefixWord ++ tailWord_3667463).sum := by decide
  have hdescent : baseEnd_3667463 < baseStart_3667463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667496 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3667496 : Nat := 118140960795 + 3667496 * 2 ^ 59
def prefixEnd_3667496 : Nat := 4983230072969 + 3 ^ 40 * 3667496 * 2
def baseEnd_3667496 : Nat := 627729415480629379577833

theorem tailTrace_3667496 : CollatzResearch.WordTrace tailWord_3667496 prefixEnd_3667496 627729415480629379577833 := by
  unfold tailWord_3667496
  simp only [CollatzResearch.WordTrace]
  refine ⟨66882284160647912647483171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89176378880863883529977561 66882284160647912647483171)
  ·
    refine ⟨100323426240971868971224757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66882284160647912647483171 100323426240971868971224757)
    ·
      refine ⟨9405321210091112716052321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100323426240971868971224757 9405321210091112716052321)
      ·
        refine ⟨7053990907568334537039241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405321210091112716052321 7053990907568334537039241)
        ·
          refine ⟨5290493180676250902779431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7053990907568334537039241 5290493180676250902779431)
          ·
            refine ⟨7935739771014376354169147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290493180676250902779431 7935739771014376354169147)
            ·
              refine ⟨11903609656521564531253721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935739771014376354169147 11903609656521564531253721)
              ·
                refine ⟨8927707242391173398440291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903609656521564531253721 8927707242391173398440291)
                ·
                  refine ⟨13391560863586760097660437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927707242391173398440291 13391560863586760097660437)
                  ·
                    refine ⟨627729415480629379577833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13391560863586760097660437 627729415480629379577833)
                    ·
                      rfl

theorem cell23_3667496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3667496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667496 prefixEnd_3667496 := by exact prefixLift 3667496
  have htrace : WordTrace (prefixWord ++ tailWord_3667496) baseStart_3667496 baseEnd_3667496 := by
    simpa [prefixWord, tailWord_3667496, baseEnd_3667496] using wordTrace_append hprefix tailTrace_3667496
  have hstable : (prefixWord ++ tailWord_3667496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667496).length < 2 ^ (prefixWord ++ tailWord_3667496).sum := by decide
  have hdescent : baseEnd_3667496 < baseStart_3667496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667533 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3667533 : Nat := 118140960795 + 3667533 * 2 ^ 59
def prefixEnd_3667533 : Nat := 4983230072969 + 3 ^ 40 * 3667533 * 2
def baseEnd_3667533 : Nat := 1883207245226104493970829

theorem tailTrace_3667533 : CollatzResearch.WordTrace tailWord_3667533 prefixEnd_3667533 1883207245226104493970829 := by
  unfold tailWord_3667533
  simp only [CollatzResearch.WordTrace]
  refine ⟨133765917822161780614063253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89177278548107853742708835 133765917822161780614063253)
  ·
    refine ⟨6270277397913833466284215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133765917822161780614063253 6270277397913833466284215)
    ·
      refine ⟨9405416096870750199426323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270277397913833466284215 9405416096870750199426323)
      ·
        refine ⟨14108124145306125299139485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405416096870750199426323 14108124145306125299139485)
        ·
          refine ⟨5290546554489796987177307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14108124145306125299139485 5290546554489796987177307)
          ·
            refine ⟨7935819831734695480765961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290546554489796987177307 7935819831734695480765961)
            ·
              refine ⟨5951864873801021610574471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935819831734695480765961 5951864873801021610574471)
              ·
                refine ⟨8927797310701532415861707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951864873801021610574471 8927797310701532415861707)
                ·
                  refine ⟨13391695966052298623792561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927797310701532415861707 13391695966052298623792561)
                  ·
                    refine ⟨10043771974539223967844421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13391695966052298623792561 10043771974539223967844421)
                    ·
                      refine ⟨1883207245226104493970829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10043771974539223967844421 1883207245226104493970829)
                      ·
                        rfl

theorem cell23_3667533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3667533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667533 prefixEnd_3667533 := by exact prefixLift 3667533
  have htrace : WordTrace (prefixWord ++ tailWord_3667533) baseStart_3667533 baseEnd_3667533 := by
    simpa [prefixWord, tailWord_3667533, baseEnd_3667533] using wordTrace_append hprefix tailTrace_3667533
  have hstable : (prefixWord ++ tailWord_3667533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667533).length < 2 ^ (prefixWord ++ tailWord_3667533).sum := by decide
  have hdescent : baseEnd_3667533 < baseStart_3667533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667536 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_3667536 : Nat := 118140960795 + 3667536 * 2 ^ 59
def prefixEnd_3667536 : Nat := 4983230072969 + 3 ^ 40 * 3667536 * 2
def baseEnd_3667536 : Nat := 1883208785668067982233315

theorem tailTrace_3667536 : CollatzResearch.WordTrace tailWord_3667536 prefixEnd_3667536 1883208785668067982233315 := by
  unfold tailWord_3667536
  simp only [CollatzResearch.WordTrace]
  refine ⟨66883013620575456063211231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89177351494100608084281641 66883013620575456063211231)
  ·
    refine ⟨100324520430863184094816847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66883013620575456063211231 100324520430863184094816847)
    ·
      refine ⟨150486780646294776142225271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100324520430863184094816847 150486780646294776142225271)
      ·
        refine ⟨225730170969442164213337907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150486780646294776142225271 225730170969442164213337907)
        ·
          refine ⟨338595256454163246320006861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225730170969442164213337907 338595256454163246320006861)
          ·
            refine ⟨126973221170311217370002573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338595256454163246320006861 126973221170311217370002573)
            ·
              refine ⟨47614957938866706513750965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126973221170311217370002573 47614957938866706513750965)
              ·
                refine ⟨4463902306768753735664153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47614957938866706513750965 4463902306768753735664153)
                ·
                  refine ⟨3347926730076565301748115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463902306768753735664153 3347926730076565301748115)
                  ·
                    refine ⟨5021890095114847952622173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347926730076565301748115 5021890095114847952622173)
                    ·
                      refine ⟨1883208785668067982233315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021890095114847952622173 1883208785668067982233315)
                      ·
                        rfl

theorem cell23_3667536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_3667536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667536 prefixEnd_3667536 := by exact prefixLift 3667536
  have htrace : WordTrace (prefixWord ++ tailWord_3667536) baseStart_3667536 baseEnd_3667536 := by
    simpa [prefixWord, tailWord_3667536, baseEnd_3667536] using wordTrace_append hprefix tailTrace_3667536
  have hstable : (prefixWord ++ tailWord_3667536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667536).length < 2 ^ (prefixWord ++ tailWord_3667536).sum := by decide
  have hdescent : baseEnd_3667536 < baseStart_3667536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667552 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_3667552 : Nat := 118140960795 + 3667552 * 2 ^ 59
def prefixEnd_3667552 : Nat := 4983230072969 + 3 ^ 40 * 3667552 * 2
def baseEnd_3667552 : Nat := 627739000452846639877747

theorem tailTrace_3667552 : CollatzResearch.WordTrace tailWord_3667552 prefixEnd_3667552 627739000452846639877747 := by
  unfold tailWord_3667552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66883305404546473429502455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89177740539395297906003273 66883305404546473429502455)
  ·
    refine ⟨100324958106819710144253683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66883305404546473429502455 100324958106819710144253683)
    ·
      refine ⟨150487437160229565216380525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100324958106819710144253683 150487437160229565216380525)
      ·
        refine ⟨56432788935086086956142697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150487437160229565216380525 56432788935086086956142697)
        ·
          refine ⟨42324591701314565217107023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56432788935086086956142697 42324591701314565217107023)
          ·
            refine ⟨63486887551971847825660535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42324591701314565217107023 63486887551971847825660535)
            ·
              refine ⟨95230331327957771738490803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63486887551971847825660535 95230331327957771738490803)
              ·
                refine ⟨142845496991936657607736205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95230331327957771738490803 142845496991936657607736205)
                ·
                  refine ⟨53567061371976246602901077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142845496991936657607736205 53567061371976246602901077)
                  ·
                    refine ⟨627739000452846639877747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53567061371976246602901077 627739000452846639877747)
                    ·
                      rfl

theorem cell23_3667552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_3667552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667552 prefixEnd_3667552 := by exact prefixLift 3667552
  have htrace : WordTrace (prefixWord ++ tailWord_3667552) baseStart_3667552 baseEnd_3667552 := by
    simpa [prefixWord, tailWord_3667552, baseEnd_3667552] using wordTrace_append hprefix tailTrace_3667552
  have hstable : (prefixWord ++ tailWord_3667552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667552).length < 2 ^ (prefixWord ++ tailWord_3667552).sum := by decide
  have hdescent : baseEnd_3667552 < baseStart_3667552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667570 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3667570 : Nat := 118140960795 + 3667570 * 2 ^ 59
def prefixEnd_3667570 : Nat := 4983230072969 + 3 ^ 40 * 3667570 * 2
def baseEnd_3667570 : Nat := 1883226244010320849208159

theorem tailTrace_3667570 : CollatzResearch.WordTrace tailWord_3667570 prefixEnd_3667570 1883226244010320849208159 := by
  unfold tailWord_3667570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33441816830756933983290041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89178178215351823955440109 33441816830756933983290041)
  ·
    refine ⟨25081362623067700487467531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33441816830756933983290041 25081362623067700487467531)
    ·
      refine ⟨37622043934601550731201297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25081362623067700487467531 37622043934601550731201297)
      ·
        refine ⟨28216532950951163048400973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37622043934601550731201297 28216532950951163048400973)
        ·
          refine ⟨10581199856606686143150365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28216532950951163048400973 10581199856606686143150365)
          ·
            refine ⟨3967949946227507303681387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10581199856606686143150365 3967949946227507303681387)
            ·
              refine ⟨5951924919341260955522081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967949946227507303681387 5951924919341260955522081)
              ·
                refine ⟨4463943689505945716641561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951924919341260955522081 4463943689505945716641561)
                ·
                  refine ⟨3347957767129459287481171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463943689505945716641561 3347957767129459287481171)
                  ·
                    refine ⟨5021936650694188931221757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347957767129459287481171 5021936650694188931221757)
                    ·
                      refine ⟨1883226244010320849208159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021936650694188931221757 1883226244010320849208159)
                      ·
                        rfl

theorem cell23_3667570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3667570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667570 prefixEnd_3667570 := by exact prefixLift 3667570
  have htrace : WordTrace (prefixWord ++ tailWord_3667570) baseStart_3667570 baseEnd_3667570 := by
    simpa [prefixWord, tailWord_3667570, baseEnd_3667570] using wordTrace_append hprefix tailTrace_3667570
  have hstable : (prefixWord ++ tailWord_3667570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667570).length < 2 ^ (prefixWord ++ tailWord_3667570).sum := by decide
  have hdescent : baseEnd_3667570 < baseStart_3667570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667589 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3667589 : Nat := 118140960795 + 3667589 * 2 ^ 59
def prefixEnd_3667589 : Nat := 4983230072969 + 3 ^ 40 * 3667589 * 2
def baseEnd_3667589 : Nat := 1883236000142756274870571

theorem tailTrace_3667589 : CollatzResearch.WordTrace tailWord_3667589 prefixEnd_3667589 1883236000142756274870571 := by
  unfold tailWord_3667589
  simp only [CollatzResearch.WordTrace]
  refine ⟨133767960309958902178101821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89178640206639268118734547 133767960309958902178101821)
  ·
    refine ⟨50162985116234588316788183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133767960309958902178101821 50162985116234588316788183)
    ·
      refine ⟨75244477674351882475182275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50162985116234588316788183 75244477674351882475182275)
      ·
        refine ⟨112866716511527823712773413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75244477674351882475182275 112866716511527823712773413)
        ·
          refine ⟨21162509345911466946145015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112866716511527823712773413 21162509345911466946145015)
          ·
            refine ⟨31743764018867200419217523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21162509345911466946145015 31743764018867200419217523)
            ·
              refine ⟨47615646028300800628826285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31743764018867200419217523 47615646028300800628826285)
              ·
                refine ⟨17855867260612800235809857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47615646028300800628826285 17855867260612800235809857)
                ·
                  refine ⟨13391900445459600176857393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17855867260612800235809857 13391900445459600176857393)
                  ·
                    refine ⟨10043925334094700132643045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13391900445459600176857393 10043925334094700132643045)
                    ·
                      refine ⟨1883236000142756274870571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10043925334094700132643045 1883236000142756274870571)
                      ·
                        rfl

theorem cell23_3667589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3667589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667589 prefixEnd_3667589 := by exact prefixLift 3667589
  have htrace : WordTrace (prefixWord ++ tailWord_3667589) baseStart_3667589 baseEnd_3667589 := by
    simpa [prefixWord, tailWord_3667589, baseEnd_3667589] using wordTrace_append hprefix tailTrace_3667589
  have hstable : (prefixWord ++ tailWord_3667589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667589).length < 2 ^ (prefixWord ++ tailWord_3667589).sum := by decide
  have hdescent : baseEnd_3667589 < baseStart_3667589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667593 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 2, 2, 2]
def baseStart_3667593 : Nat := 118140960795 + 3667593 * 2 ^ 59
def prefixEnd_3667593 : Nat := 4983230072969 + 3 ^ 40 * 3667593 * 2
def baseEnd_3667593 : Nat := 1883238054065374259220553

theorem tailTrace_3667593 : CollatzResearch.WordTrace tailWord_3667593 prefixEnd_3667593 1883238054065374259220553 := by
  unfold tailWord_3667593
  simp only [CollatzResearch.WordTrace]
  refine ⟨133768106201944410861247433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89178737467962940574164955 133768106201944410861247433)
  ·
    refine ⟨100326079651458308145935575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133768106201944410861247433 100326079651458308145935575)
    ·
      refine ⟨150489119477187462218903363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100326079651458308145935575 150489119477187462218903363)
      ·
        refine ⟨225733679215781193328355045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150489119477187462218903363 225733679215781193328355045)
        ·
          refine ⟨42325064852958973749066571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225733679215781193328355045 42325064852958973749066571)
          ·
            refine ⟨63487597279438460623599857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42325064852958973749066571 63487597279438460623599857)
            ·
              refine ⟨47615697959578845467699893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63487597279438460623599857 47615697959578845467699893)
              ·
                refine ⟨4463971683710516762596865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47615697959578845467699893 4463971683710516762596865)
                ·
                  refine ⟨3347978762782887571947649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463971683710516762596865 3347978762782887571947649)
                  ·
                    refine ⟨2510984072087165678960737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347978762782887571947649 2510984072087165678960737)
                    ·
                      refine ⟨1883238054065374259220553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510984072087165678960737 1883238054065374259220553)
                      ·
                        rfl

theorem cell23_3667593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2, 2].length) (baseStart_3667593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667593 prefixEnd_3667593 := by exact prefixLift 3667593
  have htrace : WordTrace (prefixWord ++ tailWord_3667593) baseStart_3667593 baseEnd_3667593 := by
    simpa [prefixWord, tailWord_3667593, baseEnd_3667593] using wordTrace_append hprefix tailTrace_3667593
  have hstable : (prefixWord ++ tailWord_3667593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667593).length < 2 ^ (prefixWord ++ tailWord_3667593).sum := by decide
  have hdescent : baseEnd_3667593 < baseStart_3667593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667609 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_3667609 : Nat := 118140960795 + 3667609 * 2 ^ 59
def prefixEnd_3667609 : Nat := 4983230072969 + 3 ^ 40 * 3667609 * 2
def baseEnd_3667609 : Nat := 1883246269755846196620479

theorem tailTrace_3667609 : CollatzResearch.WordTrace tailWord_3667609 prefixEnd_3667609 1883246269755846196620479 := by
  unfold tailWord_3667609
  simp only [CollatzResearch.WordTrace]
  refine ⟨133768689769886445593829881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89179126513257630395886587 133768689769886445593829881)
  ·
    refine ⟨100326517327414834195372411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133768689769886445593829881 100326517327414834195372411)
    ·
      refine ⟨150489775991122251293058617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100326517327414834195372411 150489775991122251293058617)
      ·
        refine ⟨112867331993341688469793963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150489775991122251293058617 112867331993341688469793963)
        ·
          refine ⟨169300997990012532704690945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112867331993341688469793963 169300997990012532704690945)
          ·
            refine ⟨126975748492509399528518209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169300997990012532704690945 126975748492509399528518209)
            ·
              refine ⟨95231811369382049646388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126975748492509399528518209 95231811369382049646388657)
              ·
                refine ⟨71423858527036537234791493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95231811369382049646388657 71423858527036537234791493)
                ·
                  refine ⟨13391973473819350731523405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71423858527036537234791493 13391973473819350731523405)
                  ·
                    refine ⟨5021990052682256524321277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13391973473819350731523405 5021990052682256524321277)
                    ·
                      refine ⟨1883246269755846196620479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5021990052682256524321277 1883246269755846196620479)
                      ·
                        rfl

theorem cell23_3667609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_3667609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667609 prefixEnd_3667609 := by exact prefixLift 3667609
  have htrace : WordTrace (prefixWord ++ tailWord_3667609) baseStart_3667609 baseEnd_3667609 := by
    simpa [prefixWord, tailWord_3667609, baseEnd_3667609] using wordTrace_append hprefix tailTrace_3667609
  have hstable : (prefixWord ++ tailWord_3667609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667609).length < 2 ^ (prefixWord ++ tailWord_3667609).sum := by decide
  have hdescent : baseEnd_3667609 < baseStart_3667609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667639 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3667639 : Nat := 118140960795 + 3667639 * 2 ^ 59
def prefixEnd_3667639 : Nat := 4983230072969 + 3 ^ 40 * 3667639 * 2
def baseEnd_3667639 : Nat := 1883261674175481079245341

theorem tailTrace_3667639 : CollatzResearch.WordTrace tailWord_3667639 prefixEnd_3667639 1883261674175481079245341 := by
  unfold tailWord_3667639
  simp only [CollatzResearch.WordTrace]
  refine ⟨133769783959777760717421971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89179855973185173811614647 133769783959777760717421971)
  ·
    refine ⟨200654675939666641076132957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133769783959777760717421971 200654675939666641076132957)
    ·
      refine ⟨75245503477374990403549859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200654675939666641076132957 75245503477374990403549859)
      ·
        refine ⟨112868255216062485605324789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75245503477374990403549859 112868255216062485605324789)
        ·
          refine ⟨10581398926505858025499199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112868255216062485605324789 10581398926505858025499199)
          ·
            refine ⟨15872098389758787038248799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581398926505858025499199 15872098389758787038248799)
            ·
              refine ⟨23808147584638180557373199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15872098389758787038248799 23808147584638180557373199)
              ·
                refine ⟨35712221376957270836059799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23808147584638180557373199 35712221376957270836059799)
                ·
                  refine ⟨53568332065435906254089699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35712221376957270836059799 53568332065435906254089699)
                  ·
                    refine ⟨80352498098153859381134549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53568332065435906254089699 80352498098153859381134549)
                    ·
                      refine ⟨1883261674175481079245341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80352498098153859381134549 1883261674175481079245341)
                      ·
                        rfl

theorem cell23_3667639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3667639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667639 prefixEnd_3667639 := by exact prefixLift 3667639
  have htrace : WordTrace (prefixWord ++ tailWord_3667639) baseStart_3667639 baseEnd_3667639 := by
    simpa [prefixWord, tailWord_3667639, baseEnd_3667639] using wordTrace_append hprefix tailTrace_3667639
  have hstable : (prefixWord ++ tailWord_3667639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667639).length < 2 ^ (prefixWord ++ tailWord_3667639).sum := by decide
  have hdescent : baseEnd_3667639 < baseStart_3667639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667679 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3667679 : Nat := 118140960795 + 3667679 * 2 ^ 59
def prefixEnd_3667679 : Nat := 4983230072969 + 3 ^ 40 * 3667679 * 2
def baseEnd_3667679 : Nat := 1883282213401660922745157

theorem tailTrace_3667679 : CollatzResearch.WordTrace tailWord_3667679 prefixEnd_3667679 1883282213401660922745157 := by
  unfold tailWord_3667679
  simp only [CollatzResearch.WordTrace]
  refine ⟨133771242879632847548878091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89180828586421898365918727 133771242879632847548878091)
  ·
    refine ⟨200656864319449271323317137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133771242879632847548878091 200656864319449271323317137)
    ·
      refine ⟨150492648239586953492487853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200656864319449271323317137 150492648239586953492487853)
      ·
        refine ⟨56434743089845107559682945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150492648239586953492487853 56434743089845107559682945)
        ·
          refine ⟨42326057317383830669762209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56434743089845107559682945 42326057317383830669762209)
          ·
            refine ⟨31744542988037873002321657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42326057317383830669762209 31744542988037873002321657)
            ·
              refine ⟨23808407241028404751741243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31744542988037873002321657 23808407241028404751741243)
              ·
                refine ⟨35712610861542607127611865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23808407241028404751741243 35712610861542607127611865)
                ·
                  refine ⟨26784458146156955345708899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35712610861542607127611865 26784458146156955345708899)
                  ·
                    refine ⟨40176687219235433018563349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26784458146156955345708899 40176687219235433018563349)
                    ·
                      refine ⟨1883282213401660922745157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40176687219235433018563349 1883282213401660922745157)
                      ·
                        rfl

theorem cell23_3667679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3667679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667679 prefixEnd_3667679 := by exact prefixLift 3667679
  have htrace : WordTrace (prefixWord ++ tailWord_3667679) baseStart_3667679 baseEnd_3667679 := by
    simpa [prefixWord, tailWord_3667679, baseEnd_3667679] using wordTrace_append hprefix tailTrace_3667679
  have hstable : (prefixWord ++ tailWord_3667679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667679).length < 2 ^ (prefixWord ++ tailWord_3667679).sum := by decide
  have hdescent : baseEnd_3667679 < baseStart_3667679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3667709 : Nat := 118140960795 + 3667709 * 2 ^ 59
def prefixEnd_3667709 : Nat := 4983230072969 + 3 ^ 40 * 3667709 * 2
def baseEnd_3667709 : Nat := 1883297617821295805370019

theorem tailTrace_3667709 : CollatzResearch.WordTrace tailWord_3667709 prefixEnd_3667709 1883297617821295805370019 := by
  unfold tailWord_3667709
  simp only [CollatzResearch.WordTrace]
  refine ⟨133772337069524162672470181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89181558046349441781646787 133772337069524162672470181)
  ·
    refine ⟨25082313200535780501088159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133772337069524162672470181 25082313200535780501088159)
    ·
      refine ⟨37623469800803670751632239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082313200535780501088159 37623469800803670751632239)
      ·
        refine ⟨56435204701205506127448359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37623469800803670751632239 56435204701205506127448359)
        ·
          refine ⟨84652807051808259191172539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56435204701205506127448359 84652807051808259191172539)
          ·
            refine ⟨126979210577712388786758809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84652807051808259191172539 126979210577712388786758809)
            ·
              refine ⟨95234407933284291590069107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126979210577712388786758809 95234407933284291590069107)
              ·
                refine ⟨142851611899926437385103661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95234407933284291590069107 142851611899926437385103661)
                ·
                  refine ⟨53569354462472414019413873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142851611899926437385103661 53569354462472414019413873)
                  ·
                    refine ⟨40177015846854310514560405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53569354462472414019413873 40177015846854310514560405)
                    ·
                      refine ⟨1883297617821295805370019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40177015846854310514560405 1883297617821295805370019)
                      ·
                        rfl

theorem cell23_3667709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3667709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667709 prefixEnd_3667709 := by exact prefixLift 3667709
  have htrace : WordTrace (prefixWord ++ tailWord_3667709) baseStart_3667709 baseEnd_3667709 := by
    simpa [prefixWord, tailWord_3667709, baseEnd_3667709] using wordTrace_append hprefix tailTrace_3667709
  have hstable : (prefixWord ++ tailWord_3667709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667709).length < 2 ^ (prefixWord ++ tailWord_3667709).sum := by decide
  have hdescent : baseEnd_3667709 < baseStart_3667709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667710 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3667710 : Nat := 118140960795 + 3667710 * 2 ^ 59
def prefixEnd_3667710 : Nat := 4983230072969 + 3 ^ 40 * 3667710 * 2
def baseEnd_3667710 : Nat := 627766043767316767152505

theorem tailTrace_3667710 : CollatzResearch.WordTrace tailWord_3667710 prefixEnd_3667710 627766043767316767152505 := by
  unfold tailWord_3667710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721546692815067480407073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89181582361680359895504389 16721546692815067480407073)
  ·
    refine ⟨12541160019611300610305305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16721546692815067480407073 12541160019611300610305305)
    ·
      refine ⟨9405870014708475457728979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12541160019611300610305305 9405870014708475457728979)
      ·
        refine ⟨14108805022062713186593469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405870014708475457728979 14108805022062713186593469)
        ·
          refine ⟨5290801883273517444972551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14108805022062713186593469 5290801883273517444972551)
          ·
            refine ⟨7936202824910276167458827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290801883273517444972551 7936202824910276167458827)
            ·
              refine ⟨11904304237365414251188241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936202824910276167458827 11904304237365414251188241)
              ·
                refine ⟨8928228178024060688391181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904304237365414251188241 8928228178024060688391181)
                ·
                  refine ⟨3348085566759022758146693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8928228178024060688391181 3348085566759022758146693)
                  ·
                    refine ⟨627766043767316767152505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348085566759022758146693 627766043767316767152505)
                    ·
                      rfl

theorem cell23_3667710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3667710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667710 prefixEnd_3667710 := by exact prefixLift 3667710
  have htrace : WordTrace (prefixWord ++ tailWord_3667710) baseStart_3667710 baseEnd_3667710 := by
    simpa [prefixWord, tailWord_3667710, baseEnd_3667710] using wordTrace_append hprefix tailTrace_3667710
  have hstable : (prefixWord ++ tailWord_3667710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667710).length < 2 ^ (prefixWord ++ tailWord_3667710).sum := by decide
  have hdescent : baseEnd_3667710 < baseStart_3667710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667729 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3667729 : Nat := 118140960795 + 3667729 * 2 ^ 59
def prefixEnd_3667729 : Nat := 4983230072969 + 3 ^ 40 * 3667729 * 2
def baseEnd_3667729 : Nat := 1883307887434385727119927

theorem tailTrace_3667729 : CollatzResearch.WordTrace tailWord_3667729 prefixEnd_3667729 1883307887434385727119927 := by
  unfold tailWord_3667729
  simp only [CollatzResearch.WordTrace]
  refine ⟨133773066529451706088198241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89182044352967804058798827 133773066529451706088198241)
  ·
    refine ⟨100329799897088779566148681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133773066529451706088198241 100329799897088779566148681)
    ·
      refine ⟨75247349922816584674611511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100329799897088779566148681 75247349922816584674611511)
      ·
        refine ⟨112871024884224877011917267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75247349922816584674611511 112871024884224877011917267)
        ·
          refine ⟨169306537326337315517875901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112871024884224877011917267 169306537326337315517875901)
          ·
            refine ⟨63489951497376493319203463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169306537326337315517875901 63489951497376493319203463)
            ·
              refine ⟨95234927246064739978805195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63489951497376493319203463 95234927246064739978805195)
              ·
                refine ⟨142852390869097109968207793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95234927246064739978805195 142852390869097109968207793)
                ·
                  refine ⟨107139293151822832476155845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142852390869097109968207793 107139293151822832476155845)
                  ·
                    refine ⟨20088617465966781089279221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107139293151822832476155845 20088617465966781089279221)
                    ·
                      refine ⟨1883307887434385727119927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20088617465966781089279221 1883307887434385727119927)
                      ·
                        rfl

theorem cell23_3667729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3667729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667729 prefixEnd_3667729 := by exact prefixLift 3667729
  have htrace : WordTrace (prefixWord ++ tailWord_3667729) baseStart_3667729 baseEnd_3667729 := by
    simpa [prefixWord, tailWord_3667729, baseEnd_3667729] using wordTrace_append hprefix tailTrace_3667729
  have hstable : (prefixWord ++ tailWord_3667729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667729).length < 2 ^ (prefixWord ++ tailWord_3667729).sum := by decide
  have hdescent : baseEnd_3667729 < baseStart_3667729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667743 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 4, 3, 2]
def baseStart_3667743 : Nat := 118140960795 + 3667743 * 2 ^ 59
def prefixEnd_3667743 : Nat := 4983230072969 + 3 ^ 40 * 3667743 * 2
def baseEnd_3667743 : Nat := 1883315076163548672344863

theorem tailTrace_3667743 : CollatzResearch.WordTrace tailWord_3667743 prefixEnd_3667743 1883315076163548672344863 := by
  unfold tailWord_3667743
  simp only [CollatzResearch.WordTrace]
  refine ⟨133773577151400986479207883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89182384767600657652805255 133773577151400986479207883)
  ·
    refine ⟨200660365727101479718811825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133773577151400986479207883 200660365727101479718811825)
    ·
      refine ⟨150495274295326109789108869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200660365727101479718811825 150495274295326109789108869)
      ·
        refine ⟨28217863930373645585457913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150495274295326109789108869 28217863930373645585457913)
        ·
          refine ⟨21163397947780234189093435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28217863930373645585457913 21163397947780234189093435)
          ·
            refine ⟨31745096921670351283640153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21163397947780234189093435 31745096921670351283640153)
            ·
              refine ⟨23808822691252763462730115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31745096921670351283640153 23808822691252763462730115)
              ·
                refine ⟨35713234036879145194095173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23808822691252763462730115 35713234036879145194095173)
                ·
                  refine ⟨6696231381914839723892845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35713234036879145194095173 6696231381914839723892845)
                  ·
                    refine ⟨2511086768218064896459817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6696231381914839723892845 2511086768218064896459817)
                    ·
                      refine ⟨1883315076163548672344863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511086768218064896459817 1883315076163548672344863)
                      ·
                        rfl

theorem cell23_3667743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_3667743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667743 prefixEnd_3667743 := by exact prefixLift 3667743
  have htrace : WordTrace (prefixWord ++ tailWord_3667743) baseStart_3667743 baseEnd_3667743 := by
    simpa [prefixWord, tailWord_3667743, baseEnd_3667743] using wordTrace_append hprefix tailTrace_3667743
  have hstable : (prefixWord ++ tailWord_3667743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667743).length < 2 ^ (prefixWord ++ tailWord_3667743).sum := by decide
  have hdescent : baseEnd_3667743 < baseStart_3667743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667786 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3667786 : Nat := 118140960795 + 3667786 * 2 ^ 59
def prefixEnd_3667786 : Nat := 4983230072969 + 3 ^ 40 * 3667786 * 2
def baseEnd_3667786 : Nat := 1883337155831692004107165

theorem tailTrace_3667786 : CollatzResearch.WordTrace tailWord_3667786 prefixEnd_3667786 1883337155831692004107165 := by
  unfold tailWord_3667786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33443786372561301205755803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89183430326830136548682141 33443786372561301205755803)
  ·
    refine ⟨50165679558841951808633705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33443786372561301205755803 50165679558841951808633705)
    ·
      refine ⟨37624259669131463856475279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50165679558841951808633705 37624259669131463856475279)
      ·
        refine ⟨56436389503697195784712919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37624259669131463856475279 56436389503697195784712919)
        ·
          refine ⟨84654584255545793677069379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56436389503697195784712919 84654584255545793677069379)
          ·
            refine ⟨126981876383318690515604069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84654584255545793677069379 126981876383318690515604069)
            ·
              refine ⟨23809101821872254471675763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126981876383318690515604069 23809101821872254471675763)
              ·
                refine ⟨35713652732808381707513645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23809101821872254471675763 35713652732808381707513645)
                ·
                  refine ⟨13392619774803143140317617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35713652732808381707513645 13392619774803143140317617)
                  ·
                    refine ⟨10044464831102357355238213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13392619774803143140317617 10044464831102357355238213)
                    ·
                      refine ⟨1883337155831692004107165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10044464831102357355238213 1883337155831692004107165)
                      ·
                        rfl

theorem cell23_3667786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3667786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667786 prefixEnd_3667786 := by exact prefixLift 3667786
  have htrace : WordTrace (prefixWord ++ tailWord_3667786) baseStart_3667786 baseEnd_3667786 := by
    simpa [prefixWord, tailWord_3667786, baseEnd_3667786] using wordTrace_append hprefix tailTrace_3667786
  have hstable : (prefixWord ++ tailWord_3667786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667786).length < 2 ^ (prefixWord ++ tailWord_3667786).sum := by decide
  have hdescent : baseEnd_3667786 < baseStart_3667786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667793 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_3667793 : Nat := 118140960795 + 3667793 * 2 ^ 59
def prefixEnd_3667793 : Nat := 4983230072969 + 3 ^ 40 * 3667793 * 2
def baseEnd_3667793 : Nat := 1883340750196273476719633

theorem tailTrace_3667793 : CollatzResearch.WordTrace tailWord_3667793 prefixEnd_3667793 1883340750196273476719633 := by
  unfold tailWord_3667793
  simp only [CollatzResearch.WordTrace]
  refine ⟨133775400801219845018528033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89183600534146563345685355 133775400801219845018528033)
  ·
    refine ⟨100331550600914883763896025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133775400801219845018528033 100331550600914883763896025)
    ·
      refine ⟨75248662950686162822922019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100331550600914883763896025 75248662950686162822922019)
      ·
        refine ⟨112872994426029244234383029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75248662950686162822922019 112872994426029244234383029)
        ·
          refine ⟨10581843227440241646973409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112872994426029244234383029 10581843227440241646973409)
          ·
            refine ⟨7936382420580181235230057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581843227440241646973409 7936382420580181235230057)
            ·
              refine ⟨5952286815435135926422543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936382420580181235230057 5952286815435135926422543)
              ·
                refine ⟨8928430223152703889633815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952286815435135926422543 8928430223152703889633815)
                ·
                  refine ⟨13392645334729055834450723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8928430223152703889633815 13392645334729055834450723)
                  ·
                    refine ⟨20088968002093583751676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13392645334729055834450723 20088968002093583751676085)
                    ·
                      refine ⟨1883340750196273476719633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20088968002093583751676085 1883340750196273476719633)
                      ·
                        rfl

theorem cell23_3667793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_3667793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667793 prefixEnd_3667793 := by exact prefixLift 3667793
  have htrace : WordTrace (prefixWord ++ tailWord_3667793) baseStart_3667793 baseEnd_3667793 := by
    simpa [prefixWord, tailWord_3667793, baseEnd_3667793] using wordTrace_append hprefix tailTrace_3667793
  have hstable : (prefixWord ++ tailWord_3667793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667793).length < 2 ^ (prefixWord ++ tailWord_3667793).sum := by decide
  have hdescent : baseEnd_3667793 < baseStart_3667793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667796 : List Nat := [2, 4, 1, 1, 3, 1, 11]
def baseStart_3667796 : Nat := 118140960795 + 3667796 * 2 ^ 59
def prefixEnd_3667796 : Nat := 4983230072969 + 3 ^ 40 * 3667796 * 2
def baseEnd_3667796 : Nat := 23251139390595518086199

theorem tailTrace_3667796 : CollatzResearch.WordTrace tailWord_3667796 prefixEnd_3667796 23251139390595518086199 := by
  unfold tailWord_3667796
  simp only [CollatzResearch.WordTrace]
  refine ⟨66887755110104488265443621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89183673480139317687258161 66887755110104488265443621)
  ·
    refine ⟨12541454083144591549770679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66887755110104488265443621 12541454083144591549770679)
    ·
      refine ⟨18812181124716887324656019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12541454083144591549770679 18812181124716887324656019)
      ·
        refine ⟨28218271687075330986984029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18812181124716887324656019 28218271687075330986984029)
        ·
          refine ⟨10581851882653249120119011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28218271687075330986984029 10581851882653249120119011)
          ·
            refine ⟨15872777823979873680178517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581851882653249120119011 15872777823979873680178517)
            ·
              refine ⟨23251139390595518086199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15872777823979873680178517 23251139390595518086199)
              ·
                rfl

theorem cell23_3667796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 11].length) (baseStart_3667796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667796 prefixEnd_3667796 := by exact prefixLift 3667796
  have htrace : WordTrace (prefixWord ++ tailWord_3667796) baseStart_3667796 baseEnd_3667796 := by
    simpa [prefixWord, tailWord_3667796, baseEnd_3667796] using wordTrace_append hprefix tailTrace_3667796
  have hstable : (prefixWord ++ tailWord_3667796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667796).length < 2 ^ (prefixWord ++ tailWord_3667796).sum := by decide
  have hdescent : baseEnd_3667796 < baseStart_3667796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667807 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 3, 2, 2]
def baseStart_3667807 : Nat := 118140960795 + 3667807 * 2 ^ 59
def prefixEnd_3667807 : Nat := 4983230072969 + 3 ^ 40 * 3667807 * 2
def baseEnd_3667807 : Nat := 1883347938925436421944569

theorem tailTrace_3667807 : CollatzResearch.WordTrace tailWord_3667807 prefixEnd_3667807 1883347938925436421944569 := by
  unfold tailWord_3667807
  simp only [CollatzResearch.WordTrace]
  refine ⟨133775911423169125409537675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89183940948779416939691783 133775911423169125409537675)
  ·
    refine ⟨200663867134753688114306513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133775911423169125409537675 200663867134753688114306513)
    ·
      refine ⟨150497900351065266085729885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200663867134753688114306513 150497900351065266085729885)
      ·
        refine ⟨56436712631649474782148707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150497900351065266085729885 56436712631649474782148707)
        ·
          refine ⟨84655068947474212173223061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56436712631649474782148707 84655068947474212173223061)
          ·
            refine ⟨3968206356912853695619831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84655068947474212173223061 3968206356912853695619831)
            ·
              refine ⟨5952309535369280543429747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968206356912853695619831 5952309535369280543429747)
              ·
                refine ⟨8928464303053920815144621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952309535369280543429747 8928464303053920815144621)
                ·
                  refine ⟨3348174113645220305679233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8928464303053920815144621 3348174113645220305679233)
                  ·
                    refine ⟨2511130585233915229259425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348174113645220305679233 2511130585233915229259425)
                    ·
                      refine ⟨1883347938925436421944569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511130585233915229259425 1883347938925436421944569)
                      ·
                        rfl

theorem cell23_3667807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_3667807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667807 prefixEnd_3667807 := by exact prefixLift 3667807
  have htrace : WordTrace (prefixWord ++ tailWord_3667807) baseStart_3667807 baseEnd_3667807 := by
    simpa [prefixWord, tailWord_3667807, baseEnd_3667807] using wordTrace_append hprefix tailTrace_3667807
  have hstable : (prefixWord ++ tailWord_3667807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667807).length < 2 ^ (prefixWord ++ tailWord_3667807).sum := by decide
  have hdescent : baseEnd_3667807 < baseStart_3667807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667816 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3667816 : Nat := 118140960795 + 3667816 * 2 ^ 59
def prefixEnd_3667816 : Nat := 4983230072969 + 3 ^ 40 * 3667816 * 2
def baseEnd_3667816 : Nat := 1883352560251326886732027

theorem tailTrace_3667816 : CollatzResearch.WordTrace tailWord_3667816 prefixEnd_3667816 1883352560251326886732027 := by
  unfold tailWord_3667816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66888119840068259973307651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89184159786757679964410201 66888119840068259973307651)
  ·
    refine ⟨100332179760102389959961477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66888119840068259973307651 100332179760102389959961477)
    ·
      refine ⟨18812283705019198117492777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100332179760102389959961477 18812283705019198117492777)
      ·
        refine ⟨14109212778764398588119583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18812283705019198117492777 14109212778764398588119583)
        ·
          refine ⟨21163819168146597882179375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14109212778764398588119583 21163819168146597882179375)
          ·
            refine ⟨31745728752219896823269063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21163819168146597882179375 31745728752219896823269063)
            ·
              refine ⟨47618593128329845234903595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31745728752219896823269063 47618593128329845234903595)
              ·
                refine ⟨71427889692494767852355393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47618593128329845234903595 71427889692494767852355393)
                ·
                  refine ⟨53570917269371075889266545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71427889692494767852355393 53570917269371075889266545)
                  ·
                    refine ⟨40178187952028306916949909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53570917269371075889266545 40178187952028306916949909)
                    ·
                      refine ⟨1883352560251326886732027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40178187952028306916949909 1883352560251326886732027)
                      ·
                        rfl

theorem cell23_3667816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3667816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667816 prefixEnd_3667816 := by exact prefixLift 3667816
  have htrace : WordTrace (prefixWord ++ tailWord_3667816) baseStart_3667816 baseEnd_3667816 := by
    simpa [prefixWord, tailWord_3667816, baseEnd_3667816] using wordTrace_append hprefix tailTrace_3667816
  have hstable : (prefixWord ++ tailWord_3667816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667816).length < 2 ^ (prefixWord ++ tailWord_3667816).sum := by decide
  have hdescent : baseEnd_3667816 < baseStart_3667816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667858 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3667858 : Nat := 118140960795 + 3667858 * 2 ^ 59
def prefixEnd_3667858 : Nat := 4983230072969 + 3 ^ 40 * 3667858 * 2
def baseEnd_3667858 : Nat := 1883374126438815722406835

theorem tailTrace_3667858 : CollatzResearch.WordTrace tailWord_3667858 prefixEnd_3667858 1883374126438815722406835 := by
  unfold tailWord_3667858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33444442886496090279911057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89185181030656240746429485 33444442886496090279911057)
  ·
    refine ⟨25083332164872067709933293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33444442886496090279911057 25083332164872067709933293)
    ·
      refine ⟨9406249561827025391224985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25083332164872067709933293 9406249561827025391224985)
      ·
        refine ⟨7054687171370269043418739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9406249561827025391224985 7054687171370269043418739)
        ·
          refine ⟨10582030757055403565128109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054687171370269043418739 10582030757055403565128109)
          ·
            refine ⟨3968261533895776336923041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10582030757055403565128109 3968261533895776336923041)
            ·
              refine ⟨2976196150421832252692281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968261533895776336923041 2976196150421832252692281)
              ·
                refine ⟨2232147112816374189519211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976196150421832252692281 2232147112816374189519211)
                ·
                  refine ⟨3348220669224561284278817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232147112816374189519211 3348220669224561284278817)
                  ·
                    refine ⟨2511165501918420963209113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348220669224561284278817 2511165501918420963209113)
                    ·
                      refine ⟨1883374126438815722406835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511165501918420963209113 1883374126438815722406835)
                      ·
                        rfl

theorem cell23_3667858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3667858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667858 prefixEnd_3667858 := by exact prefixLift 3667858
  have htrace : WordTrace (prefixWord ++ tailWord_3667858) baseStart_3667858 baseEnd_3667858 := by
    simpa [prefixWord, tailWord_3667858, baseEnd_3667858] using wordTrace_append hprefix tailTrace_3667858
  have hstable : (prefixWord ++ tailWord_3667858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667858).length < 2 ^ (prefixWord ++ tailWord_3667858).sum := by decide
  have hdescent : baseEnd_3667858 < baseStart_3667858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667963 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 5, 4]
def baseStart_3667963 : Nat := 118140960795 + 3667963 * 2 ^ 59
def prefixEnd_3667963 : Nat := 4983230072969 + 3 ^ 40 * 3667963 * 2
def baseEnd_3667963 : Nat := 627809347302512603864617

theorem tailTrace_3667963 : CollatzResearch.WordTrace tailWord_3667963 prefixEnd_3667963 627809347302512603864617 := by
  unfold tailWord_3667963
  simp only [CollatzResearch.WordTrace]
  refine ⟨133781601210603964052216543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89187734140402642701477695 133781601210603964052216543)
  ·
    refine ⟨200672401815905946078324815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133781601210603964052216543 200672401815905946078324815)
    ·
      refine ⟨301008602723858919117487223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200672401815905946078324815 301008602723858919117487223)
      ·
        refine ⟨451512904085788378676230835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301008602723858919117487223 451512904085788378676230835)
        ·
          refine ⟨677269356128682568014346253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451512904085788378676230835 677269356128682568014346253)
          ·
            refine ⟨253976008548255963005379845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677269356128682568014346253 253976008548255963005379845)
            ·
              refine ⟨47620501602797993063508721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253976008548255963005379845 47620501602797993063508721)
              ·
                refine ⟨35715376202098494797631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47620501602797993063508721 35715376202098494797631541)
                ·
                  refine ⟨3348316518946733887277957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35715376202098494797631541 3348316518946733887277957)
                  ·
                    refine ⟨627809347302512603864617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348316518946733887277957 627809347302512603864617)
                    ·
                      rfl

theorem cell23_3667963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 4].length) (baseStart_3667963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3667963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3667963 prefixEnd_3667963 := by exact prefixLift 3667963
  have htrace : WordTrace (prefixWord ++ tailWord_3667963) baseStart_3667963 baseEnd_3667963 := by
    simpa [prefixWord, tailWord_3667963, baseEnd_3667963] using wordTrace_append hprefix tailTrace_3667963
  have hstable : (prefixWord ++ tailWord_3667963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667963).length < 2 ^ (prefixWord ++ tailWord_3667963).sum := by decide
  have hdescent : baseEnd_3667963 < baseStart_3667963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668063 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3668063 : Nat := 118140960795 + 3668063 * 2 ^ 59
def prefixEnd_3668063 : Nat := 4983230072969 + 3 ^ 40 * 3668063 * 2
def baseEnd_3668063 : Nat := 1883479389972987420343391

theorem tailTrace_3668063 : CollatzResearch.WordTrace tailWord_3668063 prefixEnd_3668063 1883479389972987420343391 := by
  unfold tailWord_3668063
  simp only [CollatzResearch.WordTrace]
  refine ⟨133785248510241681130856843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89190165673494454087237895 133785248510241681130856843)
  ·
    refine ⟨200677872765362521696285265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133785248510241681130856843 200677872765362521696285265)
    ·
      refine ⟨150508404574021891272213949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200677872765362521696285265 150508404574021891272213949)
      ·
        refine ⟨56440651715258209227080231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150508404574021891272213949 56440651715258209227080231)
        ·
          refine ⟨84660977572887313840620347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56440651715258209227080231 84660977572887313840620347)
          ·
            refine ⟨126991466359330970760930521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84660977572887313840620347 126991466359330970760930521)
            ·
              refine ⟨95243599769498228070697891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126991466359330970760930521 95243599769498228070697891)
              ·
                refine ⟨142865399654247342106046837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95243599769498228070697891 142865399654247342106046837)
                ·
                  refine ⟨13393631217585688322441891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142865399654247342106046837 13393631217585688322441891)
                  ·
                    refine ⟨20090446826378532483662837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13393631217585688322441891 20090446826378532483662837)
                    ·
                      refine ⟨1883479389972987420343391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20090446826378532483662837 1883479389972987420343391)
                      ·
                        rfl

theorem cell23_3668063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3668063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668063 prefixEnd_3668063 := by exact prefixLift 3668063
  have htrace : WordTrace (prefixWord ++ tailWord_3668063) baseStart_3668063 baseEnd_3668063 := by
    simpa [prefixWord, tailWord_3668063, baseEnd_3668063] using wordTrace_append hprefix tailTrace_3668063
  have hstable : (prefixWord ++ tailWord_3668063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668063).length < 2 ^ (prefixWord ++ tailWord_3668063).sum := by decide
  have hdescent : baseEnd_3668063 < baseStart_3668063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668064 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2]
def baseStart_3668064 : Nat := 118140960795 + 3668064 * 2 ^ 59
def prefixEnd_3668064 : Nat := 4983230072969 + 3 ^ 40 * 3668064 * 2
def baseEnd_3668064 : Nat := 1883479903453641916430887

theorem tailTrace_3668064 : CollatzResearch.WordTrace tailWord_3668064 prefixEnd_3668064 1883479903453641916430887 := by
  unfold tailWord_3668064
  simp only [CollatzResearch.WordTrace]
  refine ⟨66892642491619029150821623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89190189988825372201095497 66892642491619029150821623)
  ·
    refine ⟨100338963737428543726232435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66892642491619029150821623 100338963737428543726232435)
    ·
      refine ⟨150508445606142815589348653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100338963737428543726232435 150508445606142815589348653)
      ·
        refine ⟨56440667102303555846005745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150508445606142815589348653 56440667102303555846005745)
        ·
          refine ⟨42330500326727666884504309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56440667102303555846005745 42330500326727666884504309)
          ·
            refine ⟨3968484405630718770422279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42330500326727666884504309 3968484405630718770422279)
            ·
              refine ⟨5952726608446078155633419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968484405630718770422279 5952726608446078155633419)
              ·
                refine ⟨8929089912669117233450129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952726608446078155633419 8929089912669117233450129)
                ·
                  refine ⟨6696817434501837925087597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929089912669117233450129 6696817434501837925087597)
                  ·
                    refine ⟨2511306537938189221907849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6696817434501837925087597 2511306537938189221907849)
                    ·
                      refine ⟨1883479903453641916430887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511306537938189221907849 1883479903453641916430887)
                      ·
                        rfl

theorem cell23_3668064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_3668064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668064 prefixEnd_3668064 := by exact prefixLift 3668064
  have htrace : WordTrace (prefixWord ++ tailWord_3668064) baseStart_3668064 baseEnd_3668064 := by
    simpa [prefixWord, tailWord_3668064, baseEnd_3668064] using wordTrace_append hprefix tailTrace_3668064
  have hstable : (prefixWord ++ tailWord_3668064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668064).length < 2 ^ (prefixWord ++ tailWord_3668064).sum := by decide
  have hdescent : baseEnd_3668064 < baseStart_3668064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668077 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3668077 : Nat := 118140960795 + 3668077 * 2 ^ 59
def prefixEnd_3668077 : Nat := 4983230072969 + 3 ^ 40 * 3668077 * 2
def baseEnd_3668077 : Nat := 1883486578702150365568327

theorem tailTrace_3668077 : CollatzResearch.WordTrace tailWord_3668077 prefixEnd_3668077 1883486578702150365568327 := by
  unfold tailWord_3668077
  simp only [CollatzResearch.WordTrace]
  refine ⟨133785759132190961521866485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89190506088127307681244323 133785759132190961521866485)
  ·
    refine ⟨12542414918642902642674983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133785759132190961521866485 12542414918642902642674983)
    ·
      refine ⟨18813622377964353964012475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542414918642902642674983 18813622377964353964012475)
      ·
        refine ⟨28220433566946530946018713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18813622377964353964012475 28220433566946530946018713)
        ·
          refine ⟨21165325175209898209514035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28220433566946530946018713 21165325175209898209514035)
          ·
            refine ⟨31747987762814847314271053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165325175209898209514035 31747987762814847314271053)
            ·
              refine ⟨11905495411055567742851645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31747987762814847314271053 11905495411055567742851645)
              ·
                refine ⟨4464560779145837903569367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11905495411055567742851645 4464560779145837903569367)
                ·
                  refine ⟨6696841168718756855354051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464560779145837903569367 6696841168718756855354051)
                  ·
                    refine ⟨10045261753078135283031077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6696841168718756855354051 10045261753078135283031077)
                    ·
                      refine ⟨1883486578702150365568327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10045261753078135283031077 1883486578702150365568327)
                      ·
                        rfl

theorem cell23_3668077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3668077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668077 prefixEnd_3668077 := by exact prefixLift 3668077
  have htrace : WordTrace (prefixWord ++ tailWord_3668077) baseStart_3668077 baseEnd_3668077 := by
    simpa [prefixWord, tailWord_3668077, baseEnd_3668077] using wordTrace_append hprefix tailTrace_3668077
  have hstable : (prefixWord ++ tailWord_3668077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668077).length < 2 ^ (prefixWord ++ tailWord_3668077).sum := by decide
  have hdescent : baseEnd_3668077 < baseStart_3668077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668087 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 2, 4]
def baseStart_3668087 : Nat := 118140960795 + 3668087 * 2 ^ 59
def prefixEnd_3668087 : Nat := 4983230072969 + 3 ^ 40 * 3668087 * 2
def baseEnd_3668087 : Nat := 627830571169565108814427

theorem tailTrace_3668087 : CollatzResearch.WordTrace tailWord_3668087 prefixEnd_3668087 627830571169565108814427 := by
  unfold tailWord_3668087
  simp only [CollatzResearch.WordTrace]
  refine ⟨133786123862154733229730515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89190749241436488819820343 133786123862154733229730515)
  ·
    refine ⟨200679185793232099844595773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133786123862154733229730515 200679185793232099844595773)
    ·
      refine ⟨75254694672462037441723415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200679185793232099844595773 75254694672462037441723415)
      ·
        refine ⟨112882042008693056162585123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75254694672462037441723415 112882042008693056162585123)
        ·
          refine ⟨169323063013039584243877685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112882042008693056162585123 169323063013039584243877685)
          ·
            refine ⟨15874037157472461022863533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169323063013039584243877685 15874037157472461022863533)
            ·
              refine ⟨5952763934052172883573825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15874037157472461022863533 5952763934052172883573825)
              ·
                refine ⟨4464572950539129662680369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952763934052172883573825 4464572950539129662680369)
                ·
                  refine ⟨3348429712904347247010277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4464572950539129662680369 3348429712904347247010277)
                  ·
                    refine ⟨627830571169565108814427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348429712904347247010277 627830571169565108814427)
                    ·
                      rfl

theorem cell23_3668087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_3668087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668087 prefixEnd_3668087 := by exact prefixLift 3668087
  have htrace : WordTrace (prefixWord ++ tailWord_3668087) baseStart_3668087 baseEnd_3668087 := by
    simpa [prefixWord, tailWord_3668087, baseEnd_3668087] using wordTrace_append hprefix tailTrace_3668087
  have hstable : (prefixWord ++ tailWord_3668087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668087).length < 2 ^ (prefixWord ++ tailWord_3668087).sum := by decide
  have hdescent : baseEnd_3668087 < baseStart_3668087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668097 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3668097 : Nat := 118140960795 + 3668097 * 2 ^ 59
def prefixEnd_3668097 : Nat := 4983230072969 + 3 ^ 40 * 3668097 * 2
def baseEnd_3668097 : Nat := 1883496848315240287318235

theorem tailTrace_3668097 : CollatzResearch.WordTrace tailWord_3668097 prefixEnd_3668097 1883496848315240287318235 := by
  unfold tailWord_3668097
  simp only [CollatzResearch.WordTrace]
  refine ⟨133786488592118504937594545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89190992394745669958396363 133786488592118504937594545)
  ·
    refine ⟨100339866444088878703195909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133786488592118504937594545 100339866444088878703195909)
    ·
      refine ⟨18813724958266664756849233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100339866444088878703195909 18813724958266664756849233)
      ·
        refine ⟨14110293718699998567636925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18813724958266664756849233 14110293718699998567636925)
        ·
          refine ⟨5291360144512499462863847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14110293718699998567636925 5291360144512499462863847)
          ·
            refine ⟨7937040216768749194295771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291360144512499462863847 7937040216768749194295771)
            ·
              refine ⟨11905560325153123791443657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7937040216768749194295771 11905560325153123791443657)
              ·
                refine ⟨8929170243864842843582743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11905560325153123791443657 8929170243864842843582743)
                ·
                  refine ⟨13393755365797264265374115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929170243864842843582743 13393755365797264265374115)
                  ·
                    refine ⟨20090633048695896398061173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13393755365797264265374115 20090633048695896398061173)
                    ·
                      refine ⟨1883496848315240287318235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20090633048695896398061173 1883496848315240287318235)
                      ·
                        rfl

theorem cell23_3668097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3668097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668097 prefixEnd_3668097 := by exact prefixLift 3668097
  have htrace : WordTrace (prefixWord ++ tailWord_3668097) baseStart_3668097 baseEnd_3668097 := by
    simpa [prefixWord, tailWord_3668097, baseEnd_3668097] using wordTrace_append hprefix tailTrace_3668097
  have hstable : (prefixWord ++ tailWord_3668097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668097).length < 2 ^ (prefixWord ++ tailWord_3668097).sum := by decide
  have hdescent : baseEnd_3668097 < baseStart_3668097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668114 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3668114 : Nat := 118140960795 + 3668114 * 2 ^ 59
def prefixEnd_3668114 : Nat := 4983230072969 + 3 ^ 40 * 3668114 * 2
def baseEnd_3668114 : Nat := 1883505577486366720805657

theorem tailTrace_3668114 : CollatzResearch.WordTrace tailWord_3668114 prefixEnd_3668114 1883505577486366720805657 := by
  unfold tailWord_3668114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33446777158264229210240849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89191405755371277893975597 33446777158264229210240849)
  ·
    refine ⟨25085082868698171907680637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33446777158264229210240849 25085082868698171907680637)
    ·
      refine ⟨9406906075761814465380239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25085082868698171907680637 9406906075761814465380239)
      ·
        refine ⟨14110359113642721698070359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406906075761814465380239 14110359113642721698070359)
        ·
          refine ⟨21165538670464082547105539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14110359113642721698070359 21165538670464082547105539)
          ·
            refine ⟨31748308005696123820658309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165538670464082547105539 31748308005696123820658309)
            ·
              refine ⟨5952807751068023216373433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31748308005696123820658309 5952807751068023216373433)
              ·
                refine ⟨4464605813301017412280075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952807751068023216373433 4464605813301017412280075)
                ·
                  refine ⟨6696908719951526118420113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464605813301017412280075 6696908719951526118420113)
                  ·
                    refine ⟨5022681539963644588815085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6696908719951526118420113 5022681539963644588815085)
                    ·
                      refine ⟨1883505577486366720805657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5022681539963644588815085 1883505577486366720805657)
                      ·
                        rfl

theorem cell23_3668114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3668114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668114 prefixEnd_3668114 := by exact prefixLift 3668114
  have htrace : WordTrace (prefixWord ++ tailWord_3668114) baseStart_3668114 baseEnd_3668114 := by
    simpa [prefixWord, tailWord_3668114, baseEnd_3668114] using wordTrace_append hprefix tailTrace_3668114
  have hstable : (prefixWord ++ tailWord_3668114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668114).length < 2 ^ (prefixWord ++ tailWord_3668114).sum := by decide
  have hdescent : baseEnd_3668114 < baseStart_3668114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_3668123 : Nat := 118140960795 + 3668123 * 2 ^ 59
def prefixEnd_3668123 : Nat := 4983230072969 + 3 ^ 40 * 3668123 * 2
def baseEnd_3668123 : Nat := 1883510198812257185593115

theorem tailTrace_3668123 : CollatzResearch.WordTrace tailWord_3668123 prefixEnd_3668123 1883510198812257185593115 := by
  unfold tailWord_3668123
  simp only [CollatzResearch.WordTrace]
  refine ⟨133787436890024311378041023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89191624593349540918694015 133787436890024311378041023)
  ·
    refine ⟨200681155335036467067061535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133787436890024311378041023 200681155335036467067061535)
    ·
      refine ⟨301021733002554700600592303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200681155335036467067061535 301021733002554700600592303)
      ·
        refine ⟨451532599503832050900888455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301021733002554700600592303 451532599503832050900888455)
        ·
          refine ⟨677298899255748076351332683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451532599503832050900888455 677298899255748076351332683)
          ·
            refine ⟨1015948348883622114526999025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677298899255748076351332683 1015948348883622114526999025)
            ·
              refine ⟨761961261662716585895249269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015948348883622114526999025 761961261662716585895249269)
              ·
                refine ⟨71433868280879679927679619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 761961261662716585895249269 71433868280879679927679619)
                ·
                  refine ⟨107150802421319519891519429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71433868280879679927679619 107150802421319519891519429)
                  ·
                    refine ⟨20090775453997409979659893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107150802421319519891519429 20090775453997409979659893)
                    ·
                      refine ⟨1883510198812257185593115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20090775453997409979659893 1883510198812257185593115)
                      ·
                        rfl

theorem cell23_3668123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_3668123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668123 prefixEnd_3668123 := by exact prefixLift 3668123
  have htrace : WordTrace (prefixWord ++ tailWord_3668123) baseStart_3668123 baseEnd_3668123 := by
    simpa [prefixWord, tailWord_3668123, baseEnd_3668123] using wordTrace_append hprefix tailTrace_3668123
  have hstable : (prefixWord ++ tailWord_3668123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668123).length < 2 ^ (prefixWord ++ tailWord_3668123).sum := by decide
  have hdescent : baseEnd_3668123 < baseStart_3668123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668128 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 1, 2, 2]
def baseStart_3668128 : Nat := 118140960795 + 3668128 * 2 ^ 59
def prefixEnd_3668128 : Nat := 4983230072969 + 3 ^ 40 * 3668128 * 2
def baseEnd_3668128 : Nat := 1883512766215529666030593

theorem tailTrace_3668128 : CollatzResearch.WordTrace tailWord_3668128 prefixEnd_3668128 1883512766215529666030593 := by
  unfold tailWord_3668128
  simp only [CollatzResearch.WordTrace]
  refine ⟨66893809627503098615986519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89191746170004131487982025 66893809627503098615986519)
  ·
    refine ⟨100340714441254647923979779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66893809627503098615986519 100340714441254647923979779)
    ·
      refine ⟨150511071661881971885969669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100340714441254647923979779 150511071661881971885969669)
      ·
        refine ⟨28220825936602869728619313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150511071661881971885969669 28220825936602869728619313)
        ·
          refine ⟨21165619452452152296464485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28220825936602869728619313 21165619452452152296464485)
          ·
            refine ⟨3968553647334778555587091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21165619452452152296464485 3968553647334778555587091)
            ·
              refine ⟨5952830471002167833380637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968553647334778555587091 5952830471002167833380637)
              ·
                refine ⟨2232311426625812937517739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5952830471002167833380637 2232311426625812937517739)
                ·
                  refine ⟨3348467139938719406276609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232311426625812937517739 3348467139938719406276609)
                  ·
                    refine ⟨2511350354954039554707457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348467139938719406276609 2511350354954039554707457)
                    ·
                      refine ⟨1883512766215529666030593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511350354954039554707457 1883512766215529666030593)
                      ·
                        rfl

theorem cell23_3668128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_3668128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668128 prefixEnd_3668128 := by exact prefixLift 3668128
  have htrace : WordTrace (prefixWord ++ tailWord_3668128) baseStart_3668128 baseEnd_3668128 := by
    simpa [prefixWord, tailWord_3668128, baseEnd_3668128] using wordTrace_append hprefix tailTrace_3668128
  have hstable : (prefixWord ++ tailWord_3668128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668128).length < 2 ^ (prefixWord ++ tailWord_3668128).sum := by decide
  have hdescent : baseEnd_3668128 < baseStart_3668128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668145 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3668145 : Nat := 118140960795 + 3668145 * 2 ^ 59
def prefixEnd_3668145 : Nat := 4983230072969 + 3 ^ 40 * 3668145 * 2
def baseEnd_3668145 : Nat := 1883521495386656099518015

theorem tailTrace_3668145 : CollatzResearch.WordTrace tailWord_3668145 prefixEnd_3668145 1883521495386656099518015 := by
  unfold tailWord_3668145
  simp only [CollatzResearch.WordTrace]
  refine ⟨133788239295944609135341889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89192159530629739423561259 133788239295944609135341889)
  ·
    refine ⟨100341179471958456851506417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133788239295944609135341889 100341179471958456851506417)
    ·
      refine ⟨75255884603968842638629813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100341179471958456851506417 75255884603968842638629813)
      ·
        refine ⟨7055239181622078997371545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75255884603968842638629813 7055239181622078997371545)
        ·
          refine ⟨5291429386216559248028659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7055239181622078997371545 5291429386216559248028659)
          ·
            refine ⟨7937144079324838872042989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291429386216559248028659 7937144079324838872042989)
            ·
              refine ⟨2976429029746814577016121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7937144079324838872042989 2976429029746814577016121)
              ·
                refine ⟨2232321772310110932762091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976429029746814577016121 2232321772310110932762091)
                ·
                  refine ⟨3348482658465166399143137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232321772310110932762091 3348482658465166399143137)
                  ·
                    refine ⟨2511361993848874799357353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348482658465166399143137 2511361993848874799357353)
                    ·
                      refine ⟨1883521495386656099518015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511361993848874799357353 1883521495386656099518015)
                      ·
                        rfl

theorem cell23_3668145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3668145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668145 prefixEnd_3668145 := by exact prefixLift 3668145
  have htrace : WordTrace (prefixWord ++ tailWord_3668145) baseStart_3668145 baseEnd_3668145 := by
    simpa [prefixWord, tailWord_3668145, baseEnd_3668145] using wordTrace_append hprefix tailTrace_3668145
  have hstable : (prefixWord ++ tailWord_3668145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668145).length < 2 ^ (prefixWord ++ tailWord_3668145).sum := by decide
  have hdescent : baseEnd_3668145 < baseStart_3668145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668170 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3668170 : Nat := 118140960795 + 3668170 * 2 ^ 59
def prefixEnd_3668170 : Nat := 4983230072969 + 3 ^ 40 * 3668170 * 2
def baseEnd_3668170 : Nat := 1883534332403018501705399

theorem tailTrace_3668170 : CollatzResearch.WordTrace tailWord_3668170 prefixEnd_3668170 1883534332403018501705399 := by
  unfold tailWord_3668170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447287780213509601250491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89192767413902692270001309 33447287780213509601250491)
  ·
    refine ⟨50170931670320264401875737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33447287780213509601250491 50170931670320264401875737)
    ·
      refine ⟨37628198752740198301406803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50170931670320264401875737 37628198752740198301406803)
      ·
        refine ⟨56442298129110297452110205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37628198752740198301406803 56442298129110297452110205)
        ·
          refine ⟨21165861798416361544541327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56442298129110297452110205 21165861798416361544541327)
          ·
            refine ⟨31748792697624542316811991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165861798416361544541327 31748792697624542316811991)
            ·
              refine ⟨47623189046436813475217987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31748792697624542316811991 47623189046436813475217987)
              ·
                refine ⟨71434783569655220212826981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47623189046436813475217987 71434783569655220212826981)
                ·
                  refine ⟨13394021919310353789905059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71434783569655220212826981 13394021919310353789905059)
                  ·
                    refine ⟨20091032878965530684857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13394021919310353789905059 20091032878965530684857589)
                    ·
                      refine ⟨1883534332403018501705399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20091032878965530684857589 1883534332403018501705399)
                      ·
                        rfl

theorem cell23_3668170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3668170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668170 prefixEnd_3668170 := by exact prefixLift 3668170
  have htrace : WordTrace (prefixWord ++ tailWord_3668170) baseStart_3668170 baseEnd_3668170 := by
    simpa [prefixWord, tailWord_3668170, baseEnd_3668170] using wordTrace_append hprefix tailTrace_3668170
  have hstable : (prefixWord ++ tailWord_3668170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668170).length < 2 ^ (prefixWord ++ tailWord_3668170).sum := by decide
  have hdescent : baseEnd_3668170 < baseStart_3668170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668184 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_3668184 : Nat := 118140960795 + 3668184 * 2 ^ 59
def prefixEnd_3668184 : Nat := 4983230072969 + 3 ^ 40 * 3668184 * 2
def baseEnd_3668184 : Nat := 1883541521132181446930335

theorem tailTrace_3668184 : CollatzResearch.WordTrace tailWord_3668184 prefixEnd_3668184 1883541521132181446930335 := by
  unfold tailWord_3668184
  simp only [CollatzResearch.WordTrace]
  refine ⟨66894830871401659398005803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89193107828535545864007737 66894830871401659398005803)
  ·
    refine ⟨100342246307102489097008705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66894830871401659398005803 100342246307102489097008705)
    ·
      refine ⟨75256684730326866822756529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100342246307102489097008705 75256684730326866822756529)
      ·
        refine ⟨56442513547745150117067397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75256684730326866822756529 56442513547745150117067397)
        ·
          refine ⟨10582971290202215646950137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56442513547745150117067397 10582971290202215646950137)
          ·
            refine ⟨7937228467651661735212603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10582971290202215646950137 7937228467651661735212603)
            ·
              refine ⟨11905842701477492602818905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7937228467651661735212603 11905842701477492602818905)
              ·
                refine ⟨8929382026108119452114179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11905842701477492602818905 8929382026108119452114179)
                ·
                  refine ⟨13394073039162179178171269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929382026108119452114179 13394073039162179178171269)
                  ·
                    refine ⟨2511388694842908595907113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13394073039162179178171269 2511388694842908595907113)
                    ·
                      refine ⟨1883541521132181446930335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511388694842908595907113 1883541521132181446930335)
                      ·
                        rfl

theorem cell23_3668184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_3668184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668184 prefixEnd_3668184 := by exact prefixLift 3668184
  have htrace : WordTrace (prefixWord ++ tailWord_3668184) baseStart_3668184 baseEnd_3668184 := by
    simpa [prefixWord, tailWord_3668184, baseEnd_3668184] using wordTrace_append hprefix tailTrace_3668184
  have hstable : (prefixWord ++ tailWord_3668184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668184).length < 2 ^ (prefixWord ++ tailWord_3668184).sum := by decide
  have hdescent : baseEnd_3668184 < baseStart_3668184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668227 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 5, 2]
def baseStart_3668227 : Nat := 118140960795 + 3668227 * 2 ^ 59
def prefixEnd_3668227 : Nat := 4983230072969 + 3 ^ 40 * 3668227 * 2
def baseEnd_3668227 : Nat := 1883563600800324778692637

theorem tailTrace_3668227 : CollatzResearch.WordTrace tailWord_3668227 prefixEnd_3668227 1883563600800324778692637 := by
  unfold tailWord_3668227
  simp only [CollatzResearch.WordTrace]
  refine ⟨133791230081647537139826935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89194153387765024759884623 133791230081647537139826935)
  ·
    refine ⟨200686845122471305709740403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133791230081647537139826935 200686845122471305709740403)
    ·
      refine ⟨301030267683706958564610605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200686845122471305709740403 301030267683706958564610605)
      ·
        refine ⟨112886350381390109461728977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301030267683706958564610605 112886350381390109461728977)
        ·
          refine ⟨84664762786042582096296733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112886350381390109461728977 84664762786042582096296733)
          ·
            refine ⟨31749286044765968286111275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84664762786042582096296733 31749286044765968286111275)
            ·
              refine ⟨47623929067148952429166913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31749286044765968286111275 47623929067148952429166913)
              ·
                refine ⟨35717946800361714321875185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47623929067148952429166913 35717946800361714321875185)
                ·
                  refine ⟨26788460100271285741406389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35717946800361714321875185 26788460100271285741406389)
                  ·
                    refine ⟨2511418134400433038256849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26788460100271285741406389 2511418134400433038256849)
                    ·
                      refine ⟨1883563600800324778692637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511418134400433038256849 1883563600800324778692637)
                      ·
                        rfl

theorem cell23_3668227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_3668227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668227 prefixEnd_3668227 := by exact prefixLift 3668227
  have htrace : WordTrace (prefixWord ++ tailWord_3668227) baseStart_3668227 baseEnd_3668227 := by
    simpa [prefixWord, tailWord_3668227, baseEnd_3668227] using wordTrace_append hprefix tailTrace_3668227
  have hstable : (prefixWord ++ tailWord_3668227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668227).length < 2 ^ (prefixWord ++ tailWord_3668227).sum := by decide
  have hdescent : baseEnd_3668227 < baseStart_3668227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668257 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3668257 : Nat := 118140960795 + 3668257 * 2 ^ 59
def prefixEnd_3668257 : Nat := 4983230072969 + 3 ^ 40 * 3668257 * 2
def baseEnd_3668257 : Nat := 1883579005219959661317499

theorem tailTrace_3668257 : CollatzResearch.WordTrace tailWord_3668257 prefixEnd_3668257 1883579005219959661317499 := by
  unfold tailWord_3668257
  simp only [CollatzResearch.WordTrace]
  refine ⟨133792324271538852263419025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89194882847692568175612683 133792324271538852263419025)
  ·
    refine ⟨100344243203654139197564269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133792324271538852263419025 100344243203654139197564269)
    ·
      refine ⟨37629091201370302199086601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100344243203654139197564269 37629091201370302199086601)
      ·
        refine ⟨28221818401027726649314951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37629091201370302199086601 28221818401027726649314951)
        ·
          refine ⟨42332727601541589973972427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28221818401027726649314951 42332727601541589973972427)
          ·
            refine ⟨63499091402312384960958641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42332727601541589973972427 63499091402312384960958641)
            ·
              refine ⟨47624318551734288720718981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63499091402312384960958641 47624318551734288720718981)
              ·
                refine ⟨8929559728450179135134809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47624318551734288720718981 8929559728450179135134809)
                ·
                  refine ⟨6697169796337634351351107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929559728450179135134809 6697169796337634351351107)
                  ·
                    refine ⟨10045754694506451527026661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697169796337634351351107 10045754694506451527026661)
                    ·
                      refine ⟨1883579005219959661317499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10045754694506451527026661 1883579005219959661317499)
                      ·
                        rfl

theorem cell23_3668257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3668257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668257 prefixEnd_3668257 := by exact prefixLift 3668257
  have htrace : WordTrace (prefixWord ++ tailWord_3668257) baseStart_3668257 baseEnd_3668257 := by
    simpa [prefixWord, tailWord_3668257, baseEnd_3668257] using wordTrace_append hprefix tailTrace_3668257
  have hstable : (prefixWord ++ tailWord_3668257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668257).length < 2 ^ (prefixWord ++ tailWord_3668257).sum := by decide
  have hdescent : baseEnd_3668257 < baseStart_3668257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668277 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3668277 : Nat := 118140960795 + 3668277 * 2 ^ 59
def prefixEnd_3668277 : Nat := 4983230072969 + 3 ^ 40 * 3668277 * 2
def baseEnd_3668277 : Nat := 1883589274833049583067407

theorem tailTrace_3668277 : CollatzResearch.WordTrace tailWord_3668277 prefixEnd_3668277 1883589274833049583067407 := by
  unfold tailWord_3668277
  simp only [CollatzResearch.WordTrace]
  refine ⟨133793053731466395679147085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89195369154310930452764723 133793053731466395679147085)
  ·
    refine ⟨50172395149299898379680157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133793053731466395679147085 50172395149299898379680157)
    ·
      refine ⟨18814648180987461892380059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50172395149299898379680157 18814648180987461892380059)
      ·
        refine ⟨28221972271481192838570089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18814648180987461892380059 28221972271481192838570089)
        ·
          refine ⟨21166479203610894628927567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28221972271481192838570089 21166479203610894628927567)
          ·
            refine ⟨31749718805416341943391351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21166479203610894628927567 31749718805416341943391351)
            ·
              refine ⟨47624578208124512915087027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31749718805416341943391351 47624578208124512915087027)
              ·
                refine ⟨71436867312186769372630541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47624578208124512915087027 71436867312186769372630541)
                ·
                  refine ⟨26788825242070038514736453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71436867312186769372630541 26788825242070038514736453)
                  ·
                    refine ⟨5022904732888132221513085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26788825242070038514736453 5022904732888132221513085)
                    ·
                      refine ⟨1883589274833049583067407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5022904732888132221513085 1883589274833049583067407)
                      ·
                        rfl

theorem cell23_3668277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3668277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668277 prefixEnd_3668277 := by exact prefixLift 3668277
  have htrace : WordTrace (prefixWord ++ tailWord_3668277) baseStart_3668277 baseEnd_3668277 := by
    simpa [prefixWord, tailWord_3668277, baseEnd_3668277] using wordTrace_append hprefix tailTrace_3668277
  have hstable : (prefixWord ++ tailWord_3668277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668277).length < 2 ^ (prefixWord ++ tailWord_3668277).sum := by decide
  have hdescent : baseEnd_3668277 < baseStart_3668277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668361 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_3668361 : Nat := 118140960795 + 3668361 * 2 ^ 59
def prefixEnd_3668361 : Nat := 4983230072969 + 3 ^ 40 * 3668361 * 2
def baseEnd_3668361 : Nat := 627877469069342418139007

theorem tailTrace_3668361 : CollatzResearch.WordTrace tailWord_3668361 prefixEnd_3668361 627877469069342418139007 := by
  unfold tailWord_3668361
  simp only [CollatzResearch.WordTrace]
  refine ⟨133796117463162078025204937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89197411642108052016803291 133796117463162078025204937)
  ·
    refine ⟨100347088097371558518903703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133796117463162078025204937 100347088097371558518903703)
    ·
      refine ⟨150520632146057337778355555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100347088097371558518903703 150520632146057337778355555)
      ·
        refine ⟨225780948219086006667533333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150520632146057337778355555 225780948219086006667533333)
        ·
          refine ⟨10583481947769656562540625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225780948219086006667533333 10583481947769656562540625)
          ·
            refine ⟨7937611460827242421905469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10583481947769656562540625 7937611460827242421905469)
            ·
              refine ⟨2976604297810215908214551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7937611460827242421905469 2976604297810215908214551)
              ·
                refine ⟨4464906446715323862321827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976604297810215908214551 4464906446715323862321827)
                ·
                  refine ⟨6697359670072985793482741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464906446715323862321827 6697359670072985793482741)
                  ·
                    refine ⟨627877469069342418139007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6697359670072985793482741 627877469069342418139007)
                    ·
                      rfl

theorem cell23_3668361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_3668361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668361 prefixEnd_3668361 := by exact prefixLift 3668361
  have htrace : WordTrace (prefixWord ++ tailWord_3668361) baseStart_3668361 baseEnd_3668361 := by
    simpa [prefixWord, tailWord_3668361, baseEnd_3668361] using wordTrace_append hprefix tailTrace_3668361
  have hstable : (prefixWord ++ tailWord_3668361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668361).length < 2 ^ (prefixWord ++ tailWord_3668361).sum := by decide
  have hdescent : baseEnd_3668361 < baseStart_3668361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668377 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3668377 : Nat := 118140960795 + 3668377 * 2 ^ 59
def prefixEnd_3668377 : Nat := 4983230072969 + 3 ^ 40 * 3668377 * 2
def baseEnd_3668377 : Nat := 1883640622898499191816947

theorem tailTrace_3668377 : CollatzResearch.WordTrace tailWord_3668377 prefixEnd_3668377 1883640622898499191816947 := by
  unfold tailWord_3668377
  simp only [CollatzResearch.WordTrace]
  refine ⟨133796701031104112757787385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89197800687402741838524923 133796701031104112757787385)
  ·
    refine ⟨100347525773328084568340539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133796701031104112757787385 100347525773328084568340539)
    ·
      refine ⟨150521288659992126852510809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100347525773328084568340539 150521288659992126852510809)
      ·
        refine ⟨112890966494994095139383107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150521288659992126852510809 112890966494994095139383107)
        ·
          refine ⟨169336449742491142709074661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112890966494994095139383107 169336449742491142709074661)
          ·
            refine ⟨31750584326717089257951499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169336449742491142709074661 31750584326717089257951499)
            ·
              refine ⟨47625876490075633886927249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31750584326717089257951499 47625876490075633886927249)
              ·
                refine ⟨35719407367556725415195437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47625876490075633886927249 35719407367556725415195437)
                ·
                  refine ⟨13394777762833772030698289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35719407367556725415195437 13394777762833772030698289)
                  ·
                    refine ⟨10046083322125329023023717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13394777762833772030698289 10046083322125329023023717)
                    ·
                      refine ⟨1883640622898499191816947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10046083322125329023023717 1883640622898499191816947)
                      ·
                        rfl

theorem cell23_3668377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3668377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668377 prefixEnd_3668377 := by exact prefixLift 3668377
  have htrace : WordTrace (prefixWord ++ tailWord_3668377) baseStart_3668377 baseEnd_3668377 := by
    simpa [prefixWord, tailWord_3668377, baseEnd_3668377] using wordTrace_append hprefix tailTrace_3668377
  have hstable : (prefixWord ++ tailWord_3668377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668377).length < 2 ^ (prefixWord ++ tailWord_3668377).sum := by decide
  have hdescent : baseEnd_3668377 < baseStart_3668377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668384 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3668384 : Nat := 118140960795 + 3668384 * 2 ^ 59
def prefixEnd_3668384 : Nat := 4983230072969 + 3 ^ 40 * 3668384 * 2
def baseEnd_3668384 : Nat := 1883644217263080664429415

theorem tailTrace_3668384 : CollatzResearch.WordTrace tailWord_3668384 prefixEnd_3668384 1883644217263080664429415 := by
  unfold tailWord_3668384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66898478171039376476646103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89197970894719168635528137 66898478171039376476646103)
  ·
    refine ⟨100347717256559064714969155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66898478171039376476646103 100347717256559064714969155)
    ·
      refine ⟨150521575884838597072453733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100347717256559064714969155 150521575884838597072453733)
      ·
        refine ⟨28222795478407236951085075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150521575884838597072453733 28222795478407236951085075)
        ·
          refine ⟨42334193217610855426627613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28222795478407236951085075 42334193217610855426627613)
          ·
            refine ⟨15875322456604070784985355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42334193217610855426627613 15875322456604070784985355)
            ·
              refine ⟨23812983684906106177478033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15875322456604070784985355 23812983684906106177478033)
              ·
                refine ⟨17859737763679579633108525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23812983684906106177478033 17859737763679579633108525)
                ·
                  refine ⟨6697401661379842362415697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17859737763679579633108525 6697401661379842362415697)
                  ·
                    refine ⟨5023051246034881771811773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697401661379842362415697 5023051246034881771811773)
                    ·
                      refine ⟨1883644217263080664429415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5023051246034881771811773 1883644217263080664429415)
                      ·
                        rfl

theorem cell23_3668384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3668384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668384 prefixEnd_3668384 := by exact prefixLift 3668384
  have htrace : WordTrace (prefixWord ++ tailWord_3668384) baseStart_3668384 baseEnd_3668384 := by
    simpa [prefixWord, tailWord_3668384, baseEnd_3668384] using wordTrace_append hprefix tailTrace_3668384
  have hstable : (prefixWord ++ tailWord_3668384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668384).length < 2 ^ (prefixWord ++ tailWord_3668384).sum := by decide
  have hdescent : baseEnd_3668384 < baseStart_3668384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668387 : List Nat := [1, 1, 1, 4, 1, 4, 3, 8]
def baseStart_3668387 : Nat := 118140960795 + 3668387 * 2 ^ 59
def prefixEnd_3668387 : Nat := 4983230072969 + 3 ^ 40 * 3668387 * 2
def baseEnd_3668387 : Nat := 69764657692779413062663

theorem tailTrace_3668387 : CollatzResearch.WordTrace tailWord_3668387 prefixEnd_3668387 69764657692779413062663 := by
  unfold tailWord_3668387
  simp only [CollatzResearch.WordTrace]
  refine ⟨133797065761067884465651415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89198043840711922977100943 133797065761067884465651415)
  ·
    refine ⟨200695598641601826698477123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133797065761067884465651415 200695598641601826698477123)
    ·
      refine ⟨301043397962402740047715685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200695598641601826698477123 301043397962402740047715685)
      ·
        refine ⟨56445637117950513758946691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301043397962402740047715685 56445637117950513758946691)
        ·
          refine ⟨84668455676925770638420037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56445637117950513758946691 84668455676925770638420037)
          ·
            refine ⟨15875335439423581994703757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84668455676925770638420037 15875335439423581994703757)
            ·
              refine ⟨5953250789783843248013909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15875335439423581994703757 5953250789783843248013909)
              ·
                refine ⟨69764657692779413062663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5953250789783843248013909 69764657692779413062663)
                ·
                  rfl

theorem cell23_3668387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 8].length) (baseStart_3668387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668387 prefixEnd_3668387 := by exact prefixLift 3668387
  have htrace : WordTrace (prefixWord ++ tailWord_3668387) baseStart_3668387 baseEnd_3668387 := by
    simpa [prefixWord, tailWord_3668387, baseEnd_3668387] using wordTrace_append hprefix tailTrace_3668387
  have hstable : (prefixWord ++ tailWord_3668387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668387).length < 2 ^ (prefixWord ++ tailWord_3668387).sum := by decide
  have hdescent : baseEnd_3668387 < baseStart_3668387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668391 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3668391 : Nat := 118140960795 + 3668391 * 2 ^ 59
def prefixEnd_3668391 : Nat := 4983230072969 + 3 ^ 40 * 3668391 * 2
def baseEnd_3668391 : Nat := 627882603875887379013961

theorem tailTrace_3668391 : CollatzResearch.WordTrace tailWord_3668391 prefixEnd_3668391 627882603875887379013961 := by
  unfold tailWord_3668391
  simp only [CollatzResearch.WordTrace]
  refine ⟨133797211653053393148797027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89198141102035595432531351 133797211653053393148797027)
  ·
    refine ⟨200695817479580089723195541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133797211653053393148797027 200695817479580089723195541)
    ·
      refine ⟨9407616444355316705774791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200695817479580089723195541 9407616444355316705774791)
      ·
        refine ⟨14111424666532975058662187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9407616444355316705774791 14111424666532975058662187)
        ·
          refine ⟨21167136999799462587993281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14111424666532975058662187 21167136999799462587993281)
          ·
            refine ⟨15875352749849596940994961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21167136999799462587993281 15875352749849596940994961)
            ·
              refine ⟨11906514562387197705746221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15875352749849596940994961 11906514562387197705746221)
              ·
                refine ⟨4464942960895199139654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11906514562387197705746221 4464942960895199139654833)
                ·
                  refine ⟨3348707220671399354741125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4464942960895199139654833 3348707220671399354741125)
                  ·
                    refine ⟨627882603875887379013961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348707220671399354741125 627882603875887379013961)
                    ·
                      rfl

theorem cell23_3668391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3668391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668391 prefixEnd_3668391 := by exact prefixLift 3668391
  have htrace : WordTrace (prefixWord ++ tailWord_3668391) baseStart_3668391 baseEnd_3668391 := by
    simpa [prefixWord, tailWord_3668391, baseEnd_3668391] using wordTrace_append hprefix tailTrace_3668391
  have hstable : (prefixWord ++ tailWord_3668391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668391).length < 2 ^ (prefixWord ++ tailWord_3668391).sum := by decide
  have hdescent : baseEnd_3668391 < baseStart_3668391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668448 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3]
def baseStart_3668448 : Nat := 118140960795 + 3668448 * 2 ^ 59
def prefixEnd_3668448 : Nat := 4983230072969 + 3 ^ 40 * 3668448 * 2
def baseEnd_3668448 : Nat := 1883677080024968414029121

theorem tailTrace_3668448 : CollatzResearch.WordTrace tailWord_3668448 prefixEnd_3668448 1883677080024968414029121 := by
  unfold tailWord_3668448
  simp only [CollatzResearch.WordTrace]
  refine ⟨66899645306923445941810999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89199527075897927922414665 66899645306923445941810999)
  ·
    refine ⟨100349467960385168912716499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66899645306923445941810999 100349467960385168912716499)
    ·
      refine ⟨150524201940577753369074749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100349467960385168912716499 150524201940577753369074749)
      ·
        refine ⟨56446575727716657513403031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150524201940577753369074749 56446575727716657513403031)
        ·
          refine ⟨84669863591574986270104547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56446575727716657513403031 84669863591574986270104547)
          ·
            refine ⟨127004795387362479405156821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84669863591574986270104547 127004795387362479405156821)
            ·
              refine ⟨2976674891891308111058363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127004795387362479405156821 2976674891891308111058363)
              ·
                refine ⟨4465012337836962166587545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976674891891308111058363 4465012337836962166587545)
                ·
                  refine ⟨3348759253377721624940659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465012337836962166587545 3348759253377721624940659)
                  ·
                    refine ⟨5023138880066582437410989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3348759253377721624940659 5023138880066582437410989)
                    ·
                      refine ⟨1883677080024968414029121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5023138880066582437410989 1883677080024968414029121)
                      ·
                        rfl

theorem cell23_3668448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_3668448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668448 prefixEnd_3668448 := by exact prefixLift 3668448
  have htrace : WordTrace (prefixWord ++ tailWord_3668448) baseStart_3668448 baseEnd_3668448 := by
    simpa [prefixWord, tailWord_3668448, baseEnd_3668448] using wordTrace_append hprefix tailTrace_3668448
  have hstable : (prefixWord ++ tailWord_3668448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668448).length < 2 ^ (prefixWord ++ tailWord_3668448).sum := by decide
  have hdescent : baseEnd_3668448 < baseStart_3668448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668458 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_3668458 : Nat := 118140960795 + 3668458 * 2 ^ 59
def prefixEnd_3668458 : Nat := 4983230072969 + 3 ^ 40 * 3668458 * 2
def baseEnd_3668458 : Nat := 1883682214831513374904075

theorem tailTrace_3668458 : CollatzResearch.WordTrace tailWord_3668458 prefixEnd_3668458 1883682214831513374904075 := by
  unfold tailWord_3668458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449913835952665897871507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89199770229207109060990685 33449913835952665897871507)
  ·
    refine ⟨50174870753928998846807261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33449913835952665897871507 50174870753928998846807261)
    ·
      refine ⟨18815576532723374567552723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50174870753928998846807261 18815576532723374567552723)
      ·
        refine ⟨28223364799085061851329085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18815576532723374567552723 28223364799085061851329085)
        ·
          refine ⟨10583761799656898194248407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28223364799085061851329085 10583761799656898194248407)
          ·
            refine ⟨15875642699485347291372611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10583761799656898194248407 15875642699485347291372611)
            ·
              refine ⟨23813464049228020937058917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15875642699485347291372611 23813464049228020937058917)
              ·
                refine ⟨4465024509230253925698547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23813464049228020937058917 4465024509230253925698547)
                ·
                  refine ⟨6697536763845380888547821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465024509230253925698547 6697536763845380888547821)
                  ·
                    refine ⟨2511576286442017833205433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6697536763845380888547821 2511576286442017833205433)
                    ·
                      refine ⟨1883682214831513374904075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511576286442017833205433 1883682214831513374904075)
                      ·
                        rfl

theorem cell23_3668458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_3668458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668458 prefixEnd_3668458 := by exact prefixLift 3668458
  have htrace : WordTrace (prefixWord ++ tailWord_3668458) baseStart_3668458 baseEnd_3668458 := by
    simpa [prefixWord, tailWord_3668458, baseEnd_3668458] using wordTrace_append hprefix tailTrace_3668458
  have hstable : (prefixWord ++ tailWord_3668458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668458).length < 2 ^ (prefixWord ++ tailWord_3668458).sum := by decide
  have hdescent : baseEnd_3668458 < baseStart_3668458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668488 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_3668488 : Nat := 118140960795 + 3668488 * 2 ^ 59
def prefixEnd_3668488 : Nat := 4983230072969 + 3 ^ 40 * 3668488 * 2
def baseEnd_3668488 : Nat := 1883697619251148257528937

theorem tailTrace_3668488 : CollatzResearch.WordTrace tailWord_3668488 prefixEnd_3668488 1883697619251148257528937 := by
  unfold tailWord_3668488
  simp only [CollatzResearch.WordTrace]
  refine ⟨66900374766850989357539059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89200499689134652476718745 66900374766850989357539059)
  ·
    refine ⟨100350562150276484036308589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66900374766850989357539059 100350562150276484036308589)
    ·
      refine ⟨37631460806353681513615721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100350562150276484036308589 37631460806353681513615721)
      ·
        refine ⟨28223595604765261135211791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37631460806353681513615721 28223595604765261135211791)
        ·
          refine ⟨42335393407147891702817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28223595604765261135211791 42335393407147891702817687)
          ·
            refine ⟨63503090110721837554226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42335393407147891702817687 63503090110721837554226531)
            ·
              refine ⟨95254635166082756331339797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63503090110721837554226531 95254635166082756331339797)
              ·
                refine ⟨4465061023410129203031553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95254635166082756331339797 4465061023410129203031553)
                ·
                  refine ⟨3348795767557596902273665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465061023410129203031553 3348795767557596902273665)
                  ·
                    refine ⟨2511596825668197676705249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348795767557596902273665 2511596825668197676705249)
                    ·
                      refine ⟨1883697619251148257528937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511596825668197676705249 1883697619251148257528937)
                      ·
                        rfl

theorem cell23_3668488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_3668488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668488 prefixEnd_3668488 := by exact prefixLift 3668488
  have htrace : WordTrace (prefixWord ++ tailWord_3668488) baseStart_3668488 baseEnd_3668488 := by
    simpa [prefixWord, tailWord_3668488, baseEnd_3668488] using wordTrace_append hprefix tailTrace_3668488
  have hstable : (prefixWord ++ tailWord_3668488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668488).length < 2 ^ (prefixWord ++ tailWord_3668488).sum := by decide
  have hdescent : baseEnd_3668488 < baseStart_3668488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668497 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3668497 : Nat := 118140960795 + 3668497 * 2 ^ 59
def prefixEnd_3668497 : Nat := 4983230072969 + 3 ^ 40 * 3668497 * 2
def baseEnd_3668497 : Nat := 1883702240577038722316395

theorem tailTrace_3668497 : CollatzResearch.WordTrace tailWord_3668497 prefixEnd_3668497 1883702240577038722316395 := by
  unfold tailWord_3668497
  simp only [CollatzResearch.WordTrace]
  refine ⟨133801077790669373252155745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89200718527112915501437163 133801077790669373252155745)
  ·
    refine ⟨100350808343002029939116809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133801077790669373252155745 100350808343002029939116809)
    ·
      refine ⟨75263106257251522454337607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100350808343002029939116809 75263106257251522454337607)
      ·
        refine ⟨112894659385877283681506411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75263106257251522454337607 112894659385877283681506411)
        ·
          refine ⟨169341989078815925522259617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112894659385877283681506411 169341989078815925522259617)
          ·
            refine ⟨127006491809111944141694713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169341989078815925522259617 127006491809111944141694713)
            ·
              refine ⟨95254868856833958106271035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127006491809111944141694713 95254868856833958106271035)
              ·
                refine ⟨142882303285250937159406553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95254868856833958106271035 142882303285250937159406553)
                ·
                  refine ⟨107161727463938202869554915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142882303285250937159406553 107161727463938202869554915)
                  ·
                    refine ⟨160742591195907304304332373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107161727463938202869554915 160742591195907304304332373)
                    ·
                      refine ⟨1883702240577038722316395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160742591195907304304332373 1883702240577038722316395)
                      ·
                        rfl

theorem cell23_3668497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3668497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668497 prefixEnd_3668497 := by exact prefixLift 3668497
  have htrace : WordTrace (prefixWord ++ tailWord_3668497) baseStart_3668497 baseEnd_3668497 := by
    simpa [prefixWord, tailWord_3668497, baseEnd_3668497] using wordTrace_append hprefix tailTrace_3668497
  have hstable : (prefixWord ++ tailWord_3668497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668497).length < 2 ^ (prefixWord ++ tailWord_3668497).sum := by decide
  have hdescent : baseEnd_3668497 < baseStart_3668497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668541 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3668541 : Nat := 118140960795 + 3668541 * 2 ^ 59
def prefixEnd_3668541 : Nat := 4983230072969 + 3 ^ 40 * 3668541 * 2
def baseEnd_3668541 : Nat := 627908277908612183388731

theorem tailTrace_3668541 : CollatzResearch.WordTrace tailWord_3668541 prefixEnd_3668541 627908277908612183388731 := by
  unfold tailWord_3668541
  simp only [CollatzResearch.WordTrace]
  refine ⟨133802682602509968766757477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89201788401673312511171651 133802682602509968766757477)
  ·
    refine ⟨25088002987970619143767027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133802682602509968766757477 25088002987970619143767027)
    ·
      refine ⟨37632004481955928715650541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25088002987970619143767027 37632004481955928715650541)
      ·
        refine ⟨14112001680733473268368953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37632004481955928715650541 14112001680733473268368953)
        ·
          refine ⟨10584001260550104951276715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14112001680733473268368953 10584001260550104951276715)
          ·
            refine ⟨15876001890825157426915073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584001260550104951276715 15876001890825157426915073)
            ·
              refine ⟨11907001418118868070186305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15876001890825157426915073 11907001418118868070186305)
              ·
                refine ⟨8930251063589151052639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11907001418118868070186305 8930251063589151052639729)
                ·
                  refine ⟨6697688297691863289479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8930251063589151052639729 6697688297691863289479797)
                  ·
                    refine ⟨627908277908612183388731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6697688297691863289479797 627908277908612183388731)
                    ·
                      rfl

theorem cell23_3668541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3668541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668541 prefixEnd_3668541 := by exact prefixLift 3668541
  have htrace : WordTrace (prefixWord ++ tailWord_3668541) baseStart_3668541 baseEnd_3668541 := by
    simpa [prefixWord, tailWord_3668541, baseEnd_3668541] using wordTrace_append hprefix tailTrace_3668541
  have hstable : (prefixWord ++ tailWord_3668541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668541).length < 2 ^ (prefixWord ++ tailWord_3668541).sum := by decide
  have hdescent : baseEnd_3668541 < baseStart_3668541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668545 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 5]
def baseStart_3668545 : Nat := 118140960795 + 3668545 * 2 ^ 59
def prefixEnd_3668545 : Nat := 4983230072969 + 3 ^ 40 * 3668545 * 2
def baseEnd_3668545 : Nat := 209302987516494948279575

theorem tailTrace_3668545 : CollatzResearch.WordTrace tailWord_3668545 prefixEnd_3668545 209302987516494948279575 := by
  unfold tailWord_3668545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133802828494495477449903089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89201885662996984966602059 133802828494495477449903089)
  ·
    refine ⟨100352121370871608087427317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133802828494495477449903089 100352121370871608087427317)
    ·
      refine ⟨9408011378519213258196311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100352121370871608087427317 9408011378519213258196311)
      ·
        refine ⟨14112017067778819887294467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408011378519213258196311 14112017067778819887294467)
        ·
          refine ⟨21168025601668229830941701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14112017067778819887294467 21168025601668229830941701)
          ·
            refine ⟨3969004800312793093301569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21168025601668229830941701 3969004800312793093301569)
            ·
              refine ⟨2976753600234594819976177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969004800312793093301569 2976753600234594819976177)
              ·
                refine ⟨2232565200175946114982133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976753600234594819976177 2232565200175946114982133)
                ·
                  refine ⟨209302987516494948279575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2232565200175946114982133 209302987516494948279575)
                  ·
                    rfl

theorem cell23_3668545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 5].length) (baseStart_3668545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668545 prefixEnd_3668545 := by exact prefixLift 3668545
  have htrace : WordTrace (prefixWord ++ tailWord_3668545) baseStart_3668545 baseEnd_3668545 := by
    simpa [prefixWord, tailWord_3668545, baseEnd_3668545] using wordTrace_append hprefix tailTrace_3668545
  have hstable : (prefixWord ++ tailWord_3668545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668545).length < 2 ^ (prefixWord ++ tailWord_3668545).sum := by decide
  have hdescent : baseEnd_3668545 < baseStart_3668545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668561 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_3668561 : Nat := 118140960795 + 3668561 * 2 ^ 59
def prefixEnd_3668561 : Nat := 4983230072969 + 3 ^ 40 * 3668561 * 2
def baseEnd_3668561 : Nat := 1883735103338926471916101

theorem tailTrace_3668561 : CollatzResearch.WordTrace tailWord_3668561 prefixEnd_3668561 1883735103338926471916101 := by
  unfold tailWord_3668561
  simp only [CollatzResearch.WordTrace]
  refine ⟨133803412062437512182485537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89202274708291674788323691 133803412062437512182485537)
  ·
    refine ⟨100352559046828134136864153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133803412062437512182485537 100352559046828134136864153)
    ·
      refine ⟨75264419285121100602648115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100352559046828134136864153 75264419285121100602648115)
      ·
        refine ⟨112896628927681650903972173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75264419285121100602648115 112896628927681650903972173)
        ·
          refine ⟨42336235847880619088989565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112896628927681650903972173 42336235847880619088989565)
          ·
            refine ⟨15876088442955232158371087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42336235847880619088989565 15876088442955232158371087)
            ·
              refine ⟨23814132664432848237556631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876088442955232158371087 23814132664432848237556631)
              ·
                refine ⟨35721198996649272356334947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814132664432848237556631 35721198996649272356334947)
                ·
                  refine ⟨53581798494973908534502421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35721198996649272356334947 53581798494973908534502421)
                  ·
                    refine ⟨2511646804451901962554801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53581798494973908534502421 2511646804451901962554801)
                    ·
                      refine ⟨1883735103338926471916101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511646804451901962554801 1883735103338926471916101)
                      ·
                        rfl

theorem cell23_3668561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_3668561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668561 prefixEnd_3668561 := by exact prefixLift 3668561
  have htrace : WordTrace (prefixWord ++ tailWord_3668561) baseStart_3668561 baseEnd_3668561 := by
    simpa [prefixWord, tailWord_3668561, baseEnd_3668561] using wordTrace_append hprefix tailTrace_3668561
  have hstable : (prefixWord ++ tailWord_3668561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668561).length < 2 ^ (prefixWord ++ tailWord_3668561).sum := by decide
  have hdescent : baseEnd_3668561 < baseStart_3668561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668588 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_3668588 : Nat := 118140960795 + 3668588 * 2 ^ 59
def prefixEnd_3668588 : Nat := 4983230072969 + 3 ^ 40 * 3668588 * 2
def baseEnd_3668588 : Nat := 627916322438865955426159

theorem tailTrace_3668588 : CollatzResearch.WordTrace tailWord_3668588 prefixEnd_3668588 627916322438865955426159 := by
  unfold tailWord_3668588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66902198416669847896859209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89202931222226463862478945 66902198416669847896859209)
  ·
    refine ⟨50176648812502385922644407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66902198416669847896859209 50176648812502385922644407)
    ·
      refine ⟨75264973218753578883966611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50176648812502385922644407 75264973218753578883966611)
      ·
        refine ⟨112897459828130368325949917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75264973218753578883966611 112897459828130368325949917)
        ·
          refine ⟨42336547435548888122231219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112897459828130368325949917 42336547435548888122231219)
          ·
            refine ⟨63504821153323332183346829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42336547435548888122231219 63504821153323332183346829)
            ·
              refine ⟨23814307932496249568755061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63504821153323332183346829 23814307932496249568755061)
              ·
                refine ⟨2232591368671523397070787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23814307932496249568755061 2232591368671523397070787)
                ·
                  refine ⟨3348887053007285095606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232591368671523397070787 3348887053007285095606181)
                  ·
                    refine ⟨627916322438865955426159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348887053007285095606181 627916322438865955426159)
                    ·
                      rfl

theorem cell23_3668588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_3668588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668588 prefixEnd_3668588 := by exact prefixLift 3668588
  have htrace : WordTrace (prefixWord ++ tailWord_3668588) baseStart_3668588 baseEnd_3668588 := by
    simpa [prefixWord, tailWord_3668588, baseEnd_3668588] using wordTrace_append hprefix tailTrace_3668588
  have hstable : (prefixWord ++ tailWord_3668588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668588).length < 2 ^ (prefixWord ++ tailWord_3668588).sum := by decide
  have hdescent : baseEnd_3668588 < baseStart_3668588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668601 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 6]
def baseStart_3668601 : Nat := 118140960795 + 3668601 * 2 ^ 59
def prefixEnd_3668601 : Nat := 4983230072969 + 3 ^ 40 * 3668601 * 2
def baseEnd_3668601 : Nat := 209306182507234035046213

theorem tailTrace_3668601 : CollatzResearch.WordTrace tailWord_3668601 prefixEnd_3668601 209306182507234035046213 := by
  unfold tailWord_3668601
  simp only [CollatzResearch.WordTrace]
  refine ⟨133804870982292599013941657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89203247321528399342627771 133804870982292599013941657)
  ·
    refine ⟨100353653236719449260456243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133804870982292599013941657 100353653236719449260456243)
    ·
      refine ⟨150530479855079173890684365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100353653236719449260456243 150530479855079173890684365)
      ·
        refine ⟨56448929945654690209006637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150530479855079173890684365 56448929945654690209006637)
        ·
          refine ⟨21168348729620508828377489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56448929945654690209006637 21168348729620508828377489)
          ·
            refine ⟨15876261547215381621283117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21168348729620508828377489 15876261547215381621283117)
            ·
              refine ⟨5953598080205768107981169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15876261547215381621283117 5953598080205768107981169)
              ·
                refine ⟨4465198560154326080985877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953598080205768107981169 4465198560154326080985877)
                ·
                  refine ⟨209306182507234035046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4465198560154326080985877 209306182507234035046213)
                  ·
                    rfl

theorem cell23_3668601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_3668601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668601 prefixEnd_3668601 := by exact prefixLift 3668601
  have htrace : WordTrace (prefixWord ++ tailWord_3668601) baseStart_3668601 baseEnd_3668601 := by
    simpa [prefixWord, tailWord_3668601, baseEnd_3668601] using wordTrace_append hprefix tailTrace_3668601
  have hstable : (prefixWord ++ tailWord_3668601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668601).length < 2 ^ (prefixWord ++ tailWord_3668601).sum := by decide
  have hdescent : baseEnd_3668601 < baseStart_3668601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668604 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3668604 : Nat := 118140960795 + 3668604 * 2 ^ 59
def prefixEnd_3668604 : Nat := 4983230072969 + 3 ^ 40 * 3668604 * 2
def baseEnd_3668604 : Nat := 1883757183007069803678403

theorem tailTrace_3668604 : CollatzResearch.WordTrace tailWord_3668604 prefixEnd_3668604 1883757183007069803678403 := by
  unfold tailWord_3668604
  simp only [CollatzResearch.WordTrace]
  refine ⟨66902490200640865263150433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89203320267521153684200577 66902490200640865263150433)
  ·
    refine ⟨50176867650480648947362825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66902490200640865263150433 50176867650480648947362825)
    ·
      refine ⟨37632650737860486710522119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50176867650480648947362825 37632650737860486710522119)
      ·
        refine ⟨56448976106790730065783179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37632650737860486710522119 56448976106790730065783179)
        ·
          refine ⟨84673464160186095098674769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56448976106790730065783179 84673464160186095098674769)
          ·
            refine ⟨63505098120139571324006077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84673464160186095098674769 63505098120139571324006077)
            ·
              refine ⟨23814411795052339246502279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63505098120139571324006077 23814411795052339246502279)
              ·
                refine ⟨35721617692578508869753419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814411795052339246502279 35721617692578508869753419)
                ·
                  refine ⟨53582426538867763304630129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35721617692578508869753419 53582426538867763304630129)
                  ·
                    refine ⟨40186819904150822478472597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53582426538867763304630129 40186819904150822478472597)
                    ·
                      refine ⟨1883757183007069803678403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40186819904150822478472597 1883757183007069803678403)
                      ·
                        rfl

theorem cell23_3668604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3668604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668604 prefixEnd_3668604 := by exact prefixLift 3668604
  have htrace : WordTrace (prefixWord ++ tailWord_3668604) baseStart_3668604 baseEnd_3668604 := by
    simpa [prefixWord, tailWord_3668604, baseEnd_3668604] using wordTrace_append hprefix tailTrace_3668604
  have hstable : (prefixWord ++ tailWord_3668604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668604).length < 2 ^ (prefixWord ++ tailWord_3668604).sum := by decide
  have hdescent : baseEnd_3668604 < baseStart_3668604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668671 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_3668671 : Nat := 118140960795 + 3668671 * 2 ^ 59
def prefixEnd_3668671 : Nat := 4983230072969 + 3 ^ 40 * 3668671 * 2
def baseEnd_3668671 : Nat := 1883791586210921041540595

theorem tailTrace_3668671 : CollatzResearch.WordTrace tailWord_3668671 prefixEnd_3668671 1883791586210921041540595 := by
  unfold tailWord_3668671
  simp only [CollatzResearch.WordTrace]
  refine ⟨133807424092039000968989867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89204949394692667312659911 133807424092039000968989867)
  ·
    refine ⟨200711136138058501453484801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133807424092039000968989867 200711136138058501453484801)
    ·
      refine ⟨150533352103543876090113601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200711136138058501453484801 150533352103543876090113601)
      ·
        refine ⟨112900014077657907067585201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150533352103543876090113601 112900014077657907067585201)
        ·
          refine ⟨84675010558243430300688901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112900014077657907067585201 84675010558243430300688901)
          ·
            refine ⟨15876564479670643181379169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84675010558243430300688901 15876564479670643181379169)
            ·
              refine ⟨11907423359752982386034377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15876564479670643181379169 11907423359752982386034377)
              ·
                refine ⟨8930567519814736789525783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11907423359752982386034377 8930567519814736789525783)
                ·
                  refine ⟨13395851279722105184288675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930567519814736789525783 13395851279722105184288675)
                  ·
                    refine ⟨20093776919583157776433013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13395851279722105184288675 20093776919583157776433013)
                    ·
                      refine ⟨1883791586210921041540595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20093776919583157776433013 1883791586210921041540595)
                      ·
                        rfl

theorem cell23_3668671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_3668671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668671 prefixEnd_3668671 := by exact prefixLift 3668671
  have htrace : WordTrace (prefixWord ++ tailWord_3668671) baseStart_3668671 baseEnd_3668671 := by
    simpa [prefixWord, tailWord_3668671, baseEnd_3668671] using wordTrace_append hprefix tailTrace_3668671
  have hstable : (prefixWord ++ tailWord_3668671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668671).length < 2 ^ (prefixWord ++ tailWord_3668671).sum := by decide
  have hdescent : baseEnd_3668671 < baseStart_3668671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668719 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 1, 2, 2]
def baseStart_3668719 : Nat := 118140960795 + 3668719 * 2 ^ 59
def prefixEnd_3668719 : Nat := 4983230072969 + 3 ^ 40 * 3668719 * 2
def baseEnd_3668719 : Nat := 1883816233282336853740375

theorem tailTrace_3668719 : CollatzResearch.WordTrace tailWord_3668719 prefixEnd_3668719 1883816233282336853740375 := by
  unfold tailWord_3668719
  simp only [CollatzResearch.WordTrace]
  refine ⟨133809174795865105166737211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89206116530576736777824807 133809174795865105166737211)
  ·
    refine ⟨200713762193797657750105817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133809174795865105166737211 200713762193797657750105817)
    ·
      refine ⟨150535321645348243312579363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200713762193797657750105817 150535321645348243312579363)
      ·
        refine ⟨225802982468022364968869045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150535321645348243312579363 225802982468022364968869045)
        ·
          refine ⟨21169029606377096715831473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225802982468022364968869045 21169029606377096715831473)
          ·
            refine ⟨15876772204782822536873605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21169029606377096715831473 15876772204782822536873605)
            ·
              refine ⟨2976894788396779225663801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15876772204782822536873605 2976894788396779225663801)
              ·
                refine ⟨2232671091297584419247851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976894788396779225663801 2232671091297584419247851)
                ·
                  refine ⟨3349006636946376628871777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232671091297584419247851 3349006636946376628871777)
                  ·
                    refine ⟨2511754977709782471653833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349006636946376628871777 2511754977709782471653833)
                    ·
                      refine ⟨1883816233282336853740375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511754977709782471653833 1883816233282336853740375)
                      ·
                        rfl

theorem cell23_3668719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 2, 2].length) (baseStart_3668719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668719 prefixEnd_3668719 := by exact prefixLift 3668719
  have htrace : WordTrace (prefixWord ++ tailWord_3668719) baseStart_3668719 baseEnd_3668719 := by
    simpa [prefixWord, tailWord_3668719, baseEnd_3668719] using wordTrace_append hprefix tailTrace_3668719
  have hstable : (prefixWord ++ tailWord_3668719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668719).length < 2 ^ (prefixWord ++ tailWord_3668719).sum := by decide
  have hdescent : baseEnd_3668719 < baseStart_3668719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668728 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_3668728 : Nat := 118140960795 + 3668728 * 2 ^ 59
def prefixEnd_3668728 : Nat := 4983230072969 + 3 ^ 40 * 3668728 * 2
def baseEnd_3668728 : Nat := 1883820854608227318527833

theorem tailTrace_3668728 : CollatzResearch.WordTrace tailWord_3668728 prefixEnd_3668728 1883820854608227318527833 := by
  unfold tailWord_3668728
  simp only [CollatzResearch.WordTrace]
  refine ⟨66904751526416249851907419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89206335368554999802543225 66904751526416249851907419)
  ·
    refine ⟨100357127289624374777861129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66904751526416249851907419 100357127289624374777861129)
    ·
      refine ⟨75267845467218281083395847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100357127289624374777861129 75267845467218281083395847)
      ·
        refine ⟨112901768200827421625093771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75267845467218281083395847 112901768200827421625093771)
        ·
          refine ⟨169352652301241132437640657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112901768200827421625093771 169352652301241132437640657)
          ·
            refine ⟨127014489225930849328230493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169352652301241132437640657 127014489225930849328230493)
            ·
              refine ⟨47630433459724068498086435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127014489225930849328230493 47630433459724068498086435)
              ·
                refine ⟨71445650189586102747129653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47630433459724068498086435 71445650189586102747129653)
                ·
                  refine ⟨6698029705273697132543405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71445650189586102747129653 6698029705273697132543405)
                  ·
                    refine ⟨2511761139477636424703777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6698029705273697132543405 2511761139477636424703777)
                    ·
                      refine ⟨1883820854608227318527833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511761139477636424703777 1883820854608227318527833)
                      ·
                        rfl

theorem cell23_3668728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_3668728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668728 prefixEnd_3668728 := by exact prefixLift 3668728
  have htrace : WordTrace (prefixWord ++ tailWord_3668728) baseStart_3668728 baseEnd_3668728 := by
    simpa [prefixWord, tailWord_3668728, baseEnd_3668728] using wordTrace_append hprefix tailTrace_3668728
  have hstable : (prefixWord ++ tailWord_3668728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668728).length < 2 ^ (prefixWord ++ tailWord_3668728).sum := by decide
  have hdescent : baseEnd_3668728 < baseStart_3668728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668761 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_3668761 : Nat := 118140960795 + 3668761 * 2 ^ 59
def prefixEnd_3668761 : Nat := 4983230072969 + 3 ^ 40 * 3668761 * 2
def baseEnd_3668761 : Nat := 1883837799469825689415181

theorem tailTrace_3668761 : CollatzResearch.WordTrace tailWord_3668761 prefixEnd_3668761 1883837799469825689415181 := by
  unfold tailWord_3668761
  simp only [CollatzResearch.WordTrace]
  refine ⟨133810706661712946339766137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89207137774475297559844091 133810706661712946339766137)
  ·
    refine ⟨100358029996284709754824603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133810706661712946339766137 100358029996284709754824603)
    ·
      refine ⟨150537044994427064632236905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100358029996284709754824603 150537044994427064632236905)
      ·
        refine ⟨112902783745820298474177679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150537044994427064632236905 112902783745820298474177679)
        ·
          refine ⟨169354175618730447711266519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112902783745820298474177679 169354175618730447711266519)
          ·
            refine ⟨254031263428095671566899779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169354175618730447711266519 254031263428095671566899779)
            ·
              refine ⟨381046895142143507350349669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254031263428095671566899779 381046895142143507350349669)
              ·
                refine ⟨71446292839151907628190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381046895142143507350349669 71446292839151907628190563)
                ·
                  refine ⟨107169439258727861442285845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71446292839151907628190563 107169439258727861442285845)
                  ·
                    refine ⟨5023567465252868505107149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107169439258727861442285845 5023567465252868505107149)
                    ·
                      refine ⟨1883837799469825689415181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5023567465252868505107149 1883837799469825689415181)
                      ·
                        rfl

theorem cell23_3668761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_3668761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668761 prefixEnd_3668761 := by exact prefixLift 3668761
  have htrace : WordTrace (prefixWord ++ tailWord_3668761) baseStart_3668761 baseEnd_3668761 := by
    simpa [prefixWord, tailWord_3668761, baseEnd_3668761] using wordTrace_append hprefix tailTrace_3668761
  have hstable : (prefixWord ++ tailWord_3668761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668761).length < 2 ^ (prefixWord ++ tailWord_3668761).sum := by decide
  have hdescent : baseEnd_3668761 < baseStart_3668761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 8, 5]
def baseStart_3668811 : Nat := 118140960795 + 3668811 * 2 ^ 59
def prefixEnd_3668811 : Nat := 4983230072969 + 3 ^ 40 * 3668811 * 2
def baseEnd_3668811 : Nat := 627954491167516831263317

theorem tailTrace_3668811 : CollatzResearch.WordTrace tailWord_3668811 prefixEnd_3668811 627954491167516831263317 := by
  unfold tailWord_3668811
  simp only [CollatzResearch.WordTrace]
  refine ⟨133812530311531804879086287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89208353541021203252724191 133812530311531804879086287)
  ·
    refine ⟨200718795467297707318629431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133812530311531804879086287 200718795467297707318629431)
    ·
      refine ⟨301078193200946560977944147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200718795467297707318629431 301078193200946560977944147)
      ·
        refine ⟨451617289801419841466916221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301078193200946560977944147 451617289801419841466916221)
        ·
          refine ⟨169356483675532440550093583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451617289801419841466916221 169356483675532440550093583)
          ·
            refine ⟨254034725513298660825140375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169356483675532440550093583 254034725513298660825140375)
            ·
              refine ⟨381052088269947991237710563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254034725513298660825140375 381052088269947991237710563)
              ·
                refine ⟨571578132404921986856565845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381052088269947991237710563 571578132404921986856565845)
                ·
                  refine ⟨6698181239120179533475381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 571578132404921986856565845 6698181239120179533475381)
                  ·
                    refine ⟨627954491167516831263317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6698181239120179533475381 627954491167516831263317)
                    ·
                      rfl

theorem cell23_3668811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].length) (baseStart_3668811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668811 prefixEnd_3668811 := by exact prefixLift 3668811
  have htrace : WordTrace (prefixWord ++ tailWord_3668811) baseStart_3668811 baseEnd_3668811 := by
    simpa [prefixWord, tailWord_3668811, baseEnd_3668811] using wordTrace_append hprefix tailTrace_3668811
  have hstable : (prefixWord ++ tailWord_3668811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668811).length < 2 ^ (prefixWord ++ tailWord_3668811).sum := by decide
  have hdescent : baseEnd_3668811 < baseStart_3668811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668858 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_3668858 : Nat := 118140960795 + 3668858 * 2 ^ 59
def prefixEnd_3668858 : Nat := 4983230072969 + 3 ^ 40 * 3668858 * 2
def baseEnd_3668858 : Nat := 627962535697770603300745

theorem tailTrace_3668858 : CollatzResearch.WordTrace tailWord_3668858 prefixEnd_3668858 627962535697770603300745 := by
  unfold tailWord_3668858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453561135590382976511807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89209496361574354604031485 33453561135590382976511807)
  ·
    refine ⟨50180341703385574464767711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33453561135590382976511807 50180341703385574464767711)
    ·
      refine ⟨75270512555078361697151567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50180341703385574464767711 75270512555078361697151567)
      ·
        refine ⟨112905768832617542545727351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75270512555078361697151567 112905768832617542545727351)
        ·
          refine ⟨169358653248926313818591027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112905768832617542545727351 169358653248926313818591027)
          ·
            refine ⟨254037979873389470727886541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169358653248926313818591027 254037979873389470727886541)
            ·
              refine ⟨95264242452521051522957453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254037979873389470727886541 95264242452521051522957453)
              ·
                refine ⟨35724090919695394321109045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95264242452521051522957453 35724090919695394321109045)
                ·
                  refine ⟨3349133523721443217603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35724090919695394321109045 3349133523721443217603973)
                  ·
                    refine ⟨627962535697770603300745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349133523721443217603973 627962535697770603300745)
                    ·
                      rfl

theorem cell23_3668858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_3668858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668858 prefixEnd_3668858 := by exact prefixLift 3668858
  have htrace : WordTrace (prefixWord ++ tailWord_3668858) baseStart_3668858 baseEnd_3668858 := by
    simpa [prefixWord, tailWord_3668858, baseEnd_3668858] using wordTrace_append hprefix tailTrace_3668858
  have hstable : (prefixWord ++ tailWord_3668858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668858).length < 2 ^ (prefixWord ++ tailWord_3668858).sum := by decide
  have hdescent : baseEnd_3668858 < baseStart_3668858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668885 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3668885 : Nat := 118140960795 + 3668885 * 2 ^ 59
def prefixEnd_3668885 : Nat := 4983230072969 + 3 ^ 40 * 3668885 * 2
def baseEnd_3668885 : Nat := 1883901471070983204264611

theorem tailTrace_3668885 : CollatzResearch.WordTrace tailWord_3668885 prefixEnd_3668885 1883901471070983204264611 := by
  unfold tailWord_3668885
  simp only [CollatzResearch.WordTrace]
  refine ⟨133815229313263715517280109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89210152875509143678186739 133815229313263715517280109)
  ·
    refine ⟨50180710992473893318980041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133815229313263715517280109 50180710992473893318980041)
    ·
      refine ⟨37635533244355419989235031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50180710992473893318980041 37635533244355419989235031)
      ·
        refine ⟨56453299866533129983852547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37635533244355419989235031 56453299866533129983852547)
        ·
          refine ⟨84679949799799694975778821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56453299866533129983852547 84679949799799694975778821)
          ·
            refine ⟨15877490587462442807958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84679949799799694975778821 15877490587462442807958529)
            ·
              refine ⟨11908117940596832105968897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15877490587462442807958529 11908117940596832105968897)
              ·
                refine ⟨8931088455447624079476673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11908117940596832105968897 8931088455447624079476673)
                ·
                  refine ⟨6698316341585718059607505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931088455447624079476673 6698316341585718059607505)
                  ·
                    refine ⟨5023737256189288544705629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6698316341585718059607505 5023737256189288544705629)
                    ·
                      refine ⟨1883901471070983204264611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5023737256189288544705629 1883901471070983204264611)
                      ·
                        rfl

theorem cell23_3668885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3668885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668885 prefixEnd_3668885 := by exact prefixLift 3668885
  have htrace : WordTrace (prefixWord ++ tailWord_3668885) baseStart_3668885 baseEnd_3668885 := by
    simpa [prefixWord, tailWord_3668885, baseEnd_3668885] using wordTrace_append hprefix tailTrace_3668885
  have hstable : (prefixWord ++ tailWord_3668885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668885).length < 2 ^ (prefixWord ++ tailWord_3668885).sum := by decide
  have hdescent : baseEnd_3668885 < baseStart_3668885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668909 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3668909 : Nat := 118140960795 + 3668909 * 2 ^ 59
def prefixEnd_3668909 : Nat := 4983230072969 + 3 ^ 40 * 3668909 * 2
def baseEnd_3668909 : Nat := 627971264868897036788167

theorem tailTrace_3668909 : CollatzResearch.WordTrace tailWord_3668909 prefixEnd_3668909 627971264868897036788167 := by
  unfold tailWord_3668909
  simp only [CollatzResearch.WordTrace]
  refine ⟨133816104665176767616153781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89210736443451178410769187 133816104665176767616153781)
  ·
    refine ⟨12545259812360321964014417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133816104665176767616153781 12545259812360321964014417)
    ·
      refine ⟨9408944859270241473010813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12545259812360321964014417 9408944859270241473010813)
      ·
        refine ⟨3528354322226340552379055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9408944859270241473010813 3528354322226340552379055)
        ·
          refine ⟨5292531483339510828568583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528354322226340552379055 5292531483339510828568583)
          ·
            refine ⟨7938797225009266242852875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292531483339510828568583 7938797225009266242852875)
            ·
              refine ⟨11908195837513899364279313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938797225009266242852875 11908195837513899364279313)
              ·
                refine ⟨8931146878135424523209485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11908195837513899364279313 8931146878135424523209485)
                ·
                  refine ⟨3349180079300784196203557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8931146878135424523209485 3349180079300784196203557)
                  ·
                    refine ⟨627971264868897036788167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349180079300784196203557 627971264868897036788167)
                    ·
                      rfl

theorem cell23_3668909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3668909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668909 prefixEnd_3668909 := by exact prefixLift 3668909
  have htrace : WordTrace (prefixWord ++ tailWord_3668909) baseStart_3668909 baseEnd_3668909 := by
    simpa [prefixWord, tailWord_3668909, baseEnd_3668909] using wordTrace_append hprefix tailTrace_3668909
  have hstable : (prefixWord ++ tailWord_3668909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668909).length < 2 ^ (prefixWord ++ tailWord_3668909).sum := by decide
  have hdescent : baseEnd_3668909 < baseStart_3668909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668949 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3668949 : Nat := 118140960795 + 3668949 * 2 ^ 59
def prefixEnd_3668949 : Nat := 4983230072969 + 3 ^ 40 * 3668949 * 2
def baseEnd_3668949 : Nat := 1883934333832870953864317

theorem tailTrace_3668949 : CollatzResearch.WordTrace tailWord_3668949 prefixEnd_3668949 1883934333832870953864317 := by
  unfold tailWord_3668949
  simp only [CollatzResearch.WordTrace]
  refine ⟨133817563585031854447609901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89211709056687902965073267 133817563585031854447609901)
  ·
    refine ⟨50181586344386945417853713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133817563585031854447609901 50181586344386945417853713)
    ·
      refine ⟨37636189758290209063390285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50181586344386945417853713 37636189758290209063390285)
      ·
        refine ⟨14113571159358828398771357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37636189758290209063390285 14113571159358828398771357)
        ·
          refine ⟨5292589184759560649539259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14113571159358828398771357 5292589184759560649539259)
          ·
            refine ⟨7938883777139340974308889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292589184759560649539259 7938883777139340974308889)
            ·
              refine ⟨5954162832854505730731667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7938883777139340974308889 5954162832854505730731667)
              ·
                refine ⟨8931244249281758596097501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954162832854505730731667 8931244249281758596097501)
                ·
                  refine ⟨3349216593480659473536563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8931244249281758596097501 3349216593480659473536563)
                  ·
                    refine ⟨5023824890220989210304845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349216593480659473536563 5023824890220989210304845)
                    ·
                      refine ⟨1883934333832870953864317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5023824890220989210304845 1883934333832870953864317)
                      ·
                        rfl

theorem cell23_3668949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3668949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668949 prefixEnd_3668949 := by exact prefixLift 3668949
  have htrace : WordTrace (prefixWord ++ tailWord_3668949) baseStart_3668949 baseEnd_3668949 := by
    simpa [prefixWord, tailWord_3668949, baseEnd_3668949] using wordTrace_append hprefix tailTrace_3668949
  have hstable : (prefixWord ++ tailWord_3668949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668949).length < 2 ^ (prefixWord ++ tailWord_3668949).sum := by decide
  have hdescent : baseEnd_3668949 < baseStart_3668949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668982 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3668982 : Nat := 118140960795 + 3668982 * 2 ^ 59
def prefixEnd_3668982 : Nat := 4983230072969 + 3 ^ 40 * 3668982 * 2
def baseEnd_3668982 : Nat := 627983759564823108250555

theorem tailTrace_3668982 : CollatzResearch.WordTrace tailWord_3668982 prefixEnd_3668982 627983759564823108250555 := by
  unfold tailWord_3668982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363672949619518817722575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89212511462608200722374133 8363672949619518817722575)
  ·
    refine ⟨12545509424429278226583863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363672949619518817722575 12545509424429278226583863)
    ·
      refine ⟨18818264136643917339875795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545509424429278226583863 18818264136643917339875795)
      ·
        refine ⟨28227396204965876009813693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18818264136643917339875795 28227396204965876009813693)
        ·
          refine ⟨10585273576862203503680135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28227396204965876009813693 10585273576862203503680135)
          ·
            refine ⟨15877910365293305255520203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585273576862203503680135 15877910365293305255520203)
            ·
              refine ⟨23816865547939957883280305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15877910365293305255520203 23816865547939957883280305)
              ·
                refine ⟨17862649160954968412460229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23816865547939957883280305 17862649160954968412460229)
                ·
                  refine ⟨3349246717679056577336293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17862649160954968412460229 3349246717679056577336293)
                  ·
                    refine ⟨627983759564823108250555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349246717679056577336293 627983759564823108250555)
                    ·
                      rfl

theorem cell23_3668982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3668982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668982 prefixEnd_3668982 := by exact prefixLift 3668982
  have htrace : WordTrace (prefixWord ++ tailWord_3668982) baseStart_3668982 baseEnd_3668982 := by
    simpa [prefixWord, tailWord_3668982, baseEnd_3668982] using wordTrace_append hprefix tailTrace_3668982
  have hstable : (prefixWord ++ tailWord_3668982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668982).length < 2 ^ (prefixWord ++ tailWord_3668982).sum := by decide
  have hdescent : baseEnd_3668982 < baseStart_3668982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669006 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3669006 : Nat := 118140960795 + 3669006 * 2 ^ 59
def prefixEnd_3669006 : Nat := 4983230072969 + 3 ^ 40 * 3669006 * 2
def baseEnd_3669006 : Nat := 1883963602230177230851555

theorem tailTrace_3669006 : CollatzResearch.WordTrace tailWord_3669006 prefixEnd_3669006 1883963602230177230851555 := by
  unfold tailWord_3669006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727455318228169147804359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89213095030550235454956581 16727455318228169147804359)
  ·
    refine ⟨25091182977342253721706539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16727455318228169147804359 25091182977342253721706539)
    ·
      refine ⟨37636774466013380582559809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25091182977342253721706539 37636774466013380582559809)
      ·
        refine ⟨28227580849510035436919857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37636774466013380582559809 28227580849510035436919857)
        ·
          refine ⟨21170685637132526577689893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28227580849510035436919857 21170685637132526577689893)
          ·
            refine ⟨3969503556962348733316855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21170685637132526577689893 3969503556962348733316855)
            ·
              refine ⟨5954255335443523099975283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969503556962348733316855 5954255335443523099975283)
              ·
                refine ⟨8931383003165284649962925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954255335443523099975283 8931383003165284649962925)
                ·
                  refine ⟨3349268626186981743736097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8931383003165284649962925 3349268626186981743736097)
                  ·
                    refine ⟨2511951469640236307802073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349268626186981743736097 2511951469640236307802073)
                    ·
                      refine ⟨1883963602230177230851555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511951469640236307802073 1883963602230177230851555)
                      ·
                        rfl

theorem cell23_3669006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3669006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669006 prefixEnd_3669006 := by exact prefixLift 3669006
  have htrace : WordTrace (prefixWord ++ tailWord_3669006) baseStart_3669006 baseEnd_3669006 := by
    simpa [prefixWord, tailWord_3669006, baseEnd_3669006] using wordTrace_append hprefix tailTrace_3669006
  have hstable : (prefixWord ++ tailWord_3669006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669006).length < 2 ^ (prefixWord ++ tailWord_3669006).sum := by decide
  have hdescent : baseEnd_3669006 < baseStart_3669006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669057 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3669057 : Nat := 118140960795 + 3669057 * 2 ^ 59
def prefixEnd_3669057 : Nat := 4983230072969 + 3 ^ 40 * 3669057 * 2
def baseEnd_3669057 : Nat := 1883989789743556531313821

theorem tailTrace_3669057 : CollatzResearch.WordTrace tailWord_3669057 prefixEnd_3669057 1883989789743556531313821 := by
  unfold tailWord_3669057
  simp only [CollatzResearch.WordTrace]
  refine ⟨133821502668640588892541425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89214335112427059261694283 133821502668640588892541425)
  ·
    refine ⟨100366127001480441669406069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133821502668640588892541425 100366127001480441669406069)
    ·
      refine ⟨9409324406388791406506819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100366127001480441669406069 9409324406388791406506819)
      ·
        refine ⟨14113986609583187109760229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409324406388791406506819 14113986609583187109760229)
        ·
          refine ⟨2646372489296847583080043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14113986609583187109760229 2646372489296847583080043)
          ·
            refine ⟨3969558733945271374620065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646372489296847583080043 3969558733945271374620065)
            ·
              refine ⟨2977169050458953530965049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969558733945271374620065 2977169050458953530965049)
              ·
                refine ⟨2232876787844215148223787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977169050458953530965049 2232876787844215148223787)
                ·
                  refine ⟨3349315181766322722335681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232876787844215148223787 3349315181766322722335681)
                  ·
                    refine ⟨2511986386324742041751761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349315181766322722335681 2511986386324742041751761)
                    ·
                      refine ⟨1883989789743556531313821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2511986386324742041751761 1883989789743556531313821)
                      ·
                        rfl

theorem cell23_3669057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3669057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669057 prefixEnd_3669057 := by exact prefixLift 3669057
  have htrace : WordTrace (prefixWord ++ tailWord_3669057) baseStart_3669057 baseEnd_3669057 := by
    simpa [prefixWord, tailWord_3669057, baseEnd_3669057] using wordTrace_append hprefix tailTrace_3669057
  have hstable : (prefixWord ++ tailWord_3669057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669057).length < 2 ^ (prefixWord ++ tailWord_3669057).sum := by decide
  have hdescent : baseEnd_3669057 < baseStart_3669057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669113 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 2, 2, 2]
def baseStart_3669113 : Nat := 118140960795 + 3669113 * 2 ^ 59
def prefixEnd_3669113 : Nat := 4983230072969 + 3 ^ 40 * 3669113 * 2
def baseEnd_3669113 : Nat := 1884018544660208312213563

theorem tailTrace_3669113 : CollatzResearch.WordTrace tailWord_3669113 prefixEnd_3669113 1884018544660208312213563 := by
  unfold tailWord_3669113
  simp only [CollatzResearch.WordTrace]
  refine ⟨133823545156437710456579993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89215696770958473637719995 133823545156437710456579993)
  ·
    refine ⟨100367658867328282842434995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133823545156437710456579993 100367658867328282842434995)
    ·
      refine ⟨150551488300992424263652493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100367658867328282842434995 150551488300992424263652493)
      ·
        refine ⟨56456808112872159098869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150551488300992424263652493 56456808112872159098869685)
        ·
          refine ⟨5292825760581764915519033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56456808112872159098869685 5292825760581764915519033)
          ·
            refine ⟨3969619320436323686639275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292825760581764915519033 3969619320436323686639275)
            ·
              refine ⟨5954428980654485529958913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969619320436323686639275 5954428980654485529958913)
              ·
                refine ⟨4465821735490864147469185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954428980654485529958913 4465821735490864147469185)
                ·
                  refine ⟨3349366301618148110601889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465821735490864147469185 3349366301618148110601889)
                  ·
                    refine ⟨2512024726213611082951417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349366301618148110601889 2512024726213611082951417)
                    ·
                      refine ⟨1884018544660208312213563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512024726213611082951417 1884018544660208312213563)
                      ·
                        rfl

theorem cell23_3669113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_3669113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669113 prefixEnd_3669113 := by exact prefixLift 3669113
  have htrace : WordTrace (prefixWord ++ tailWord_3669113) baseStart_3669113 baseEnd_3669113 := by
    simpa [prefixWord, tailWord_3669113, baseEnd_3669113] using wordTrace_append hprefix tailTrace_3669113
  have hstable : (prefixWord ++ tailWord_3669113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669113).length < 2 ^ (prefixWord ++ tailWord_3669113).sum := by decide
  have hdescent : baseEnd_3669113 < baseStart_3669113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669115 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 2, 5]
def baseStart_3669115 : Nat := 118140960795 + 3669115 * 2 ^ 59
def prefixEnd_3669115 : Nat := 4983230072969 + 3 ^ 40 * 3669115 * 2
def baseEnd_3669115 : Nat := 628006523873839101462851

theorem tailTrace_3669115 : CollatzResearch.WordTrace tailWord_3669115 prefixEnd_3669115 628006523873839101462851 := by
  unfold tailWord_3669115
  simp only [CollatzResearch.WordTrace]
  refine ⟨133823618102430464798152799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89215745401620309865435199 133823618102430464798152799)
  ·
    refine ⟨200735427153645697197229199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133823618102430464798152799 200735427153645697197229199)
    ·
      refine ⟨301103140730468545795843799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200735427153645697197229199 301103140730468545795843799)
      ·
        refine ⟨451654711095702818693765699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301103140730468545795843799 451654711095702818693765699)
        ·
          refine ⟨677482066643554228040648549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451654711095702818693765699 677482066643554228040648549)
          ·
            refine ⟨127027887495666417757621603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 677482066643554228040648549 127027887495666417757621603)
            ·
              refine ⟨190541831243499626636432405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127027887495666417757621603 190541831243499626636432405)
              ·
                refine ⟨8931648339539044998582769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190541831243499626636432405 8931648339539044998582769)
                ·
                  refine ⟨6698736254654283748937077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931648339539044998582769 6698736254654283748937077)
                  ·
                    refine ⟨628006523873839101462851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6698736254654283748937077 628006523873839101462851)
                    ·
                      rfl

theorem cell23_3669115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].length) (baseStart_3669115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669115 prefixEnd_3669115 := by exact prefixLift 3669115
  have htrace : WordTrace (prefixWord ++ tailWord_3669115) baseStart_3669115 baseEnd_3669115 := by
    simpa [prefixWord, tailWord_3669115, baseEnd_3669115] using wordTrace_append hprefix tailTrace_3669115
  have hstable : (prefixWord ++ tailWord_3669115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669115).length < 2 ^ (prefixWord ++ tailWord_3669115).sum := by decide
  have hdescent : baseEnd_3669115 < baseStart_3669115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669152 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3669152 : Nat := 118140960795 + 3669152 * 2 ^ 59
def prefixEnd_3669152 : Nat := 4983230072969 + 3 ^ 40 * 3669152 * 2
def baseEnd_3669152 : Nat := 1884038570405733659625883

theorem tailTrace_3669152 : CollatzResearch.WordTrace tailWord_3669152 prefixEnd_3669152 1884038570405733659625883 := by
  unfold tailWord_3669152
  simp only [CollatzResearch.WordTrace]
  refine ⟨66912483801648210058624855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89216645068864280078166473 66912483801648210058624855)
  ·
    refine ⟨100368725702472315087937283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66912483801648210058624855 100368725702472315087937283)
    ·
      refine ⟨150553088553708472631905925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100368725702472315087937283 150553088553708472631905925)
      ·
        refine ⟨28228704103820338618482361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150553088553708472631905925 28228704103820338618482361)
        ·
          refine ⟨21171528077865253963861771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28228704103820338618482361 21171528077865253963861771)
          ·
            refine ⟨31757292116797880945792657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21171528077865253963861771 31757292116797880945792657)
            ·
              refine ⟨23817969087598410709344493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31757292116797880945792657 23817969087598410709344493)
              ·
                refine ⟨8931738407849404016004185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23817969087598410709344493 8931738407849404016004185)
                ·
                  refine ⟨6698803805887053012003139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931738407849404016004185 6698803805887053012003139)
                  ·
                    refine ⟨10048205708830579518004709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698803805887053012003139 10048205708830579518004709)
                    ·
                      refine ⟨1884038570405733659625883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10048205708830579518004709 1884038570405733659625883)
                      ·
                        rfl

theorem cell23_3669152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3669152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669152 prefixEnd_3669152 := by exact prefixLift 3669152
  have htrace : WordTrace (prefixWord ++ tailWord_3669152) baseStart_3669152 baseEnd_3669152 := by
    simpa [prefixWord, tailWord_3669152, baseEnd_3669152] using wordTrace_append hprefix tailTrace_3669152
  have hstable : (prefixWord ++ tailWord_3669152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669152).length < 2 ^ (prefixWord ++ tailWord_3669152).sum := by decide
  have hdescent : baseEnd_3669152 < baseStart_3669152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669169 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3669169 : Nat := 118140960795 + 3669169 * 2 ^ 59
def prefixEnd_3669169 : Nat := 4983230072969 + 3 ^ 40 * 3669169 * 2
def baseEnd_3669169 : Nat := 1884047299576860093113305

theorem tailTrace_3669169 : CollatzResearch.WordTrace tailWord_3669169 prefixEnd_3669169 1884047299576860093113305 := by
  unfold tailWord_3669169
  simp only [CollatzResearch.WordTrace]
  refine ⟨133825587644234832020618561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89217058429489888013745707 133825587644234832020618561)
  ·
    refine ⟨100369190733176124015463921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133825587644234832020618561 100369190733176124015463921)
    ·
      refine ⟨75276893049882093011597941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100369190733176124015463921 75276893049882093011597941)
      ·
        refine ⟨7057208723426446219837307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75276893049882093011597941 7057208723426446219837307)
        ·
          refine ⟨10585813085139669329755961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057208723426446219837307 10585813085139669329755961)
          ·
            refine ⟨7939359813854751997316971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10585813085139669329755961 7939359813854751997316971)
            ·
              refine ⟨11909039720782127995975457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939359813854751997316971 11909039720782127995975457)
              ·
                refine ⟨8931779790586595996981593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11909039720782127995975457 8931779790586595996981593)
                ·
                  refine ⟨6698834842939946997736195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931779790586595996981593 6698834842939946997736195)
                  ·
                    refine ⟨10048252264409920496604293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698834842939946997736195 10048252264409920496604293)
                    ·
                      refine ⟨1884047299576860093113305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10048252264409920496604293 1884047299576860093113305)
                      ·
                        rfl

theorem cell23_3669169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3669169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669169 prefixEnd_3669169 := by exact prefixLift 3669169
  have htrace : WordTrace (prefixWord ++ tailWord_3669169) baseStart_3669169 baseEnd_3669169 := by
    simpa [prefixWord, tailWord_3669169, baseEnd_3669169] using wordTrace_append hprefix tailTrace_3669169
  have hstable : (prefixWord ++ tailWord_3669169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669169).length < 2 ^ (prefixWord ++ tailWord_3669169).sum := by decide
  have hdescent : baseEnd_3669169 < baseStart_3669169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669175 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 8]
def baseStart_3669175 : Nat := 118140960795 + 3669175 * 2 ^ 59
def prefixEnd_3669175 : Nat := 4983230072969 + 3 ^ 40 * 3669175 * 2
def baseEnd_3669175 : Nat := 209338931162309674404253

theorem tailTrace_3669175 : CollatzResearch.WordTrace tailWord_3669175 prefixEnd_3669175 209338931162309674404253 := by
  unfold tailWord_3669175
  simp only [CollatzResearch.WordTrace]
  refine ⟨133825806482213095045336979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89217204321475396696891319 133825806482213095045336979)
  ·
    refine ⟨200738709723319642568005469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133825806482213095045336979 200738709723319642568005469)
    ·
      refine ⟨75277016146244865963002051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200738709723319642568005469 75277016146244865963002051)
      ·
        refine ⟨112915524219367298944503077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75277016146244865963002051 112915524219367298944503077)
        ·
          refine ⟨21171660791131368552094327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112915524219367298944503077 21171660791131368552094327)
          ·
            refine ⟨31757491186697052828141491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21171660791131368552094327 31757491186697052828141491)
            ·
              refine ⟨47636236780045579242212237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31757491186697052828141491 47636236780045579242212237)
              ·
                refine ⟨17863588792517092215829589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47636236780045579242212237 17863588792517092215829589)
                ·
                  refine ⟨209338931162309674404253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17863588792517092215829589 209338931162309674404253)
                  ·
                    rfl

theorem cell23_3669175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 8].length) (baseStart_3669175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669175 prefixEnd_3669175 := by exact prefixLift 3669175
  have htrace : WordTrace (prefixWord ++ tailWord_3669175) baseStart_3669175 baseEnd_3669175 := by
    simpa [prefixWord, tailWord_3669175, baseEnd_3669175] using wordTrace_append hprefix tailTrace_3669175
  have hstable : (prefixWord ++ tailWord_3669175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669175).length < 2 ^ (prefixWord ++ tailWord_3669175).sum := by decide
  have hdescent : baseEnd_3669175 < baseStart_3669175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669242 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_3669242 : Nat := 118140960795 + 3669242 * 2 ^ 59
def prefixEnd_3669242 : Nat := 4983230072969 + 3 ^ 40 * 3669242 * 2
def baseEnd_3669242 : Nat := 1884084783664638307500469

theorem tailTrace_3669242 : CollatzResearch.WordTrace tailWord_3669242 prefixEnd_3669242 1884084783664638307500469 := by
  unfold tailWord_3669242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33457062543242591372006495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89218833448646910325350653 33457062543242591372006495)
  ·
    refine ⟨50185593814863887058009743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33457062543242591372006495 50185593814863887058009743)
    ·
      refine ⟨75278390722295830587014615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50185593814863887058009743 75278390722295830587014615)
      ·
        refine ⟨112917586083443745880521923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75278390722295830587014615 112917586083443745880521923)
        ·
          refine ⟨169376379125165618820782885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112917586083443745880521923 169376379125165618820782885)
          ·
            refine ⟨31758071085968553528896791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169376379125165618820782885 31758071085968553528896791)
            ·
              refine ⟨47637106628952830293345187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31758071085968553528896791 47637106628952830293345187)
              ·
                refine ⟨71455659943429245440017781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47637106628952830293345187 71455659943429245440017781)
                ·
                  refine ⟨6698968119696491760001667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71455659943429245440017781 6698968119696491760001667)
                  ·
                    refine ⟨10048452179544737640002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698968119696491760001667 10048452179544737640002501)
                    ·
                      refine ⟨1884084783664638307500469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10048452179544737640002501 1884084783664638307500469)
                      ·
                        rfl

theorem cell23_3669242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_3669242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669242 prefixEnd_3669242 := by exact prefixLift 3669242
  have htrace : WordTrace (prefixWord ++ tailWord_3669242) baseStart_3669242 baseEnd_3669242 := by
    simpa [prefixWord, tailWord_3669242, baseEnd_3669242] using wordTrace_append hprefix tailTrace_3669242
  have hstable : (prefixWord ++ tailWord_3669242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669242).length < 2 ^ (prefixWord ++ tailWord_3669242).sum := by decide
  have hdescent : baseEnd_3669242 < baseStart_3669242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669276 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3669276 : Nat := 118140960795 + 3669276 * 2 ^ 59
def prefixEnd_3669276 : Nat := 4983230072969 + 3 ^ 40 * 3669276 * 2
def baseEnd_3669276 : Nat := 1884102242006891174475313

theorem tailTrace_3669276 : CollatzResearch.WordTrace tailWord_3669276 prefixEnd_3669276 1884102242006891174475313 := by
  unfold tailWord_3669276
  simp only [CollatzResearch.WordTrace]
  refine ⟨66914745127423594647381841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89219660169898126196509121 66914745127423594647381841)
  ·
    refine ⟨50186058845567695985536381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66914745127423594647381841 50186058845567695985536381)
    ·
      refine ⟨18819772067087885994576143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50186058845567695985536381 18819772067087885994576143)
      ·
        refine ⟨28229658100631828991864215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18819772067087885994576143 28229658100631828991864215)
        ·
          refine ⟨42344487150947743487796323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28229658100631828991864215 42344487150947743487796323)
          ·
            refine ⟨63516730726421615231694485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42344487150947743487796323 63516730726421615231694485)
            ·
              refine ⟨2977346752801013213985679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63516730726421615231694485 2977346752801013213985679)
              ·
                refine ⟨4466020129201519820978519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977346752801013213985679 4466020129201519820978519)
                ·
                  refine ⟨6699030193802279731467779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466020129201519820978519 6699030193802279731467779)
                  ·
                    refine ⟨10048545290703419597201669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699030193802279731467779 10048545290703419597201669)
                    ·
                      refine ⟨1884102242006891174475313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10048545290703419597201669 1884102242006891174475313)
                      ·
                        rfl

theorem cell23_3669276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3669276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669276 prefixEnd_3669276 := by exact prefixLift 3669276
  have htrace : WordTrace (prefixWord ++ tailWord_3669276) baseStart_3669276 baseEnd_3669276 := by
    simpa [prefixWord, tailWord_3669276, baseEnd_3669276] using wordTrace_append hprefix tailTrace_3669276
  have hstable : (prefixWord ++ tailWord_3669276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669276).length < 2 ^ (prefixWord ++ tailWord_3669276).sum := by decide
  have hdescent : baseEnd_3669276 < baseStart_3669276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669313 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3669313 : Nat := 118140960795 + 3669313 * 2 ^ 59
def prefixEnd_3669313 : Nat := 4983230072969 + 3 ^ 40 * 3669313 * 2
def baseEnd_3669313 : Nat := 1884121240791107529712643

theorem tailTrace_3669313 : CollatzResearch.WordTrace tailWord_3669313 prefixEnd_3669313 1884121240791107529712643 := by
  unfold tailWord_3669313
  simp only [CollatzResearch.WordTrace]
  refine ⟨133830839755713144613860593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89220559837142096409240395 133830839755713144613860593)
  ·
    refine ⟨100373129816784858460395445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133830839755713144613860593 100373129816784858460395445)
    ·
      refine ⟨9409980920323580480662073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100373129816784858460395445 9409980920323580480662073)
      ·
        refine ⟨7057485690242685360496555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9409980920323580480662073 7057485690242685360496555)
        ·
          refine ⟨10586228535364028040744833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057485690242685360496555 10586228535364028040744833)
          ·
            refine ⟨7939671401523021030558625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10586228535364028040744833 7939671401523021030558625)
            ·
              refine ⟨5954753551142265772918969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939671401523021030558625 5954753551142265772918969)
              ·
                refine ⟨4466065163356699329689227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954753551142265772918969 4466065163356699329689227)
                ·
                  refine ⟨6699097745035048994533841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466065163356699329689227 6699097745035048994533841)
                  ·
                    refine ⟨5024323308776286745900381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699097745035048994533841 5024323308776286745900381)
                    ·
                      refine ⟨1884121240791107529712643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5024323308776286745900381 1884121240791107529712643)
                      ·
                        rfl

theorem cell23_3669313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3669313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669313 prefixEnd_3669313 := by exact prefixLift 3669313
  have htrace : WordTrace (prefixWord ++ tailWord_3669313) baseStart_3669313 baseEnd_3669313 := by
    simpa [prefixWord, tailWord_3669313, baseEnd_3669313] using wordTrace_append hprefix tailTrace_3669313
  have hstable : (prefixWord ++ tailWord_3669313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669313).length < 2 ^ (prefixWord ++ tailWord_3669313).sum := by decide
  have hdescent : baseEnd_3669313 < baseStart_3669313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669316 : List Nat := [2, 3, 4, 1, 1, 1, 4, 7]
def baseStart_3669316 : Nat := 118140960795 + 3669316 * 2 ^ 59
def prefixEnd_3669316 : Nat := 4983230072969 + 3 ^ 40 * 3669316 * 2
def baseEnd_3669316 : Nat := 69782325230854482147227

theorem tailTrace_3669316 : CollatzResearch.WordTrace tailWord_3669316 prefixEnd_3669316 69782325230854482147227 := by
  unfold tailWord_3669316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66915474587351138063109901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89220632783134850750813201 66915474587351138063109901)
  ·
    refine ⟨25093302970256676773666213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66915474587351138063109901 25093302970256676773666213)
    ·
      refine ⟨4704994306923126895062415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25093302970256676773666213 4704994306923126895062415)
      ·
        refine ⟨7057491460384690342593623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704994306923126895062415 7057491460384690342593623)
        ·
          refine ⟨10586237190577035513890435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057491460384690342593623 10586237190577035513890435)
          ·
            refine ⟨15879355785865553270835653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586237190577035513890435 15879355785865553270835653)
            ·
              refine ⟨2977379209849791238281685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15879355785865553270835653 2977379209849791238281685)
              ·
                refine ⟨69782325230854482147227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2977379209849791238281685 69782325230854482147227)
                ·
                  rfl

theorem cell23_3669316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 7].length) (baseStart_3669316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669316 prefixEnd_3669316 := by exact prefixLift 3669316
  have htrace : WordTrace (prefixWord ++ tailWord_3669316) baseStart_3669316 baseEnd_3669316 := by
    simpa [prefixWord, tailWord_3669316, baseEnd_3669316] using wordTrace_append hprefix tailTrace_3669316
  have hstable : (prefixWord ++ tailWord_3669316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669316).length < 2 ^ (prefixWord ++ tailWord_3669316).sum := by decide
  have hdescent : baseEnd_3669316 < baseStart_3669316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669336 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_3669336 : Nat := 118140960795 + 3669336 * 2 ^ 59
def prefixEnd_3669336 : Nat := 4983230072969 + 3 ^ 40 * 3669336 * 2
def baseEnd_3669336 : Nat := 1884133050846160939725037

theorem tailTrace_3669336 : CollatzResearch.WordTrace tailWord_3669336 prefixEnd_3669336 1884133050846160939725037 := by
  unfold tailWord_3669336
  simp only [CollatzResearch.WordTrace]
  refine ⟨66915839317314909770973931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89221119089753213027965241 66915839317314909770973931)
  ·
    refine ⟨100373758975972364656460897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66915839317314909770973931 100373758975972364656460897)
    ·
      refine ⟨75280319231979273492345673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100373758975972364656460897 75280319231979273492345673)
      ·
        refine ⟨56460239423984455119259255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75280319231979273492345673 56460239423984455119259255)
        ·
          refine ⟨84690359135976682678888883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56460239423984455119259255 84690359135976682678888883)
          ·
            refine ⟨127035538703965024018333325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84690359135976682678888883 127035538703965024018333325)
            ·
              refine ⟨47638327013986884006874997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127035538703965024018333325 47638327013986884006874997)
              ·
                refine ⟨4466093157561270375644531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47638327013986884006874997 4466093157561270375644531)
                ·
                  refine ⟨6699139736341905563466797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466093157561270375644531 6699139736341905563466797)
                  ·
                    refine ⟨2512177401128214586300049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6699139736341905563466797 2512177401128214586300049)
                    ·
                      refine ⟨1884133050846160939725037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512177401128214586300049 1884133050846160939725037)
                      ·
                        rfl

theorem cell23_3669336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_3669336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669336 prefixEnd_3669336 := by exact prefixLift 3669336
  have htrace : WordTrace (prefixWord ++ tailWord_3669336) baseStart_3669336 baseEnd_3669336 := by
    simpa [prefixWord, tailWord_3669336, baseEnd_3669336] using wordTrace_append hprefix tailTrace_3669336
  have hstable : (prefixWord ++ tailWord_3669336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669336).length < 2 ^ (prefixWord ++ tailWord_3669336).sum := by decide
  have hdescent : baseEnd_3669336 < baseStart_3669336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669372 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 9]
def baseStart_3669372 : Nat := 118140960795 + 3669372 * 2 ^ 59
def prefixEnd_3669372 : Nat := 4983230072969 + 3 ^ 40 * 3669372 * 2
def baseEnd_3669372 : Nat := 209350170683302533208319

theorem tailTrace_3669372 : CollatzResearch.WordTrace tailWord_3669372 prefixEnd_3669372 209350170683302533208319 := by
  unfold tailWord_3669372
  simp only [CollatzResearch.WordTrace]
  refine ⟨66916495831249698845129185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89221994441666265126838913 66916495831249698845129185)
  ·
    refine ⟨50187371873437274133846889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66916495831249698845129185 50187371873437274133846889)
    ·
      refine ⟨37640528905077955600385167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50187371873437274133846889 37640528905077955600385167)
      ·
        refine ⟨56460793357616933400577751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37640528905077955600385167 56460793357616933400577751)
        ·
          refine ⟨84691190036425400100866627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56460793357616933400577751 84691190036425400100866627)
          ·
            refine ⟨127036785054638100151299941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84691190036425400100866627 127036785054638100151299941)
            ·
              refine ⟨23819397197744643778368739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127036785054638100151299941 23819397197744643778368739)
              ·
                refine ⟨35729095796616965667553109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23819397197744643778368739 35729095796616965667553109)
                ·
                  refine ⟨209350170683302533208319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35729095796616965667553109 209350170683302533208319)
                  ·
                    rfl

theorem cell23_3669372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_3669372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669372 prefixEnd_3669372 := by exact prefixLift 3669372
  have htrace : WordTrace (prefixWord ++ tailWord_3669372) baseStart_3669372 baseEnd_3669372 := by
    simpa [prefixWord, tailWord_3669372, baseEnd_3669372] using wordTrace_append hprefix tailTrace_3669372
  have hstable : (prefixWord ++ tailWord_3669372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669372).length < 2 ^ (prefixWord ++ tailWord_3669372).sum := by decide
  have hdescent : baseEnd_3669372 < baseStart_3669372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669399 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3669399 : Nat := 118140960795 + 3669399 * 2 ^ 59
def prefixEnd_3669399 : Nat := 4983230072969 + 3 ^ 40 * 3669399 * 2
def baseEnd_3669399 : Nat := 1884165400127394193237247

theorem tailTrace_3669399 : CollatzResearch.WordTrace tailWord_3669399 prefixEnd_3669399 1884165400127394193237247 := by
  unfold tailWord_3669399
  simp only [CollatzResearch.WordTrace]
  refine ⟨133833976433401581301491251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89222650955601054200994167 133833976433401581301491251)
  ·
    refine ⟨200750964650102371952236877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133833976433401581301491251 200750964650102371952236877)
    ·
      refine ⟨75281611743788389482088829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200750964650102371952236877 75281611743788389482088829)
      ·
        refine ⟨28230604403920646055783311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75281611743788389482088829 28230604403920646055783311)
        ·
          refine ⟨42345906605880969083674967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28230604403920646055783311 42345906605880969083674967)
          ·
            refine ⟨63518859908821453625512451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42345906605880969083674967 63518859908821453625512451)
            ·
              refine ⟨95278289863232180438268677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63518859908821453625512451 95278289863232180438268677)
              ·
                refine ⟨17864679349356033832175377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95278289863232180438268677 17864679349356033832175377)
                ·
                  refine ⟨13398509512017025374131533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17864679349356033832175377 13398509512017025374131533)
                  ·
                    refine ⟨5024441067006384515299325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13398509512017025374131533 5024441067006384515299325)
                    ·
                      refine ⟨1884165400127394193237247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5024441067006384515299325 1884165400127394193237247)
                      ·
                        rfl

theorem cell23_3669399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3669399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669399 prefixEnd_3669399 := by exact prefixLift 3669399
  have htrace : WordTrace (prefixWord ++ tailWord_3669399) baseStart_3669399 baseEnd_3669399 := by
    simpa [prefixWord, tailWord_3669399, baseEnd_3669399] using wordTrace_append hprefix tailTrace_3669399
  have hstable : (prefixWord ++ tailWord_3669399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669399).length < 2 ^ (prefixWord ++ tailWord_3669399).sum := by decide
  have hdescent : baseEnd_3669399 < baseStart_3669399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669436 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_3669436 : Nat := 118140960795 + 3669436 * 2 ^ 59
def prefixEnd_3669436 : Nat := 4983230072969 + 3 ^ 40 * 3669436 * 2
def baseEnd_3669436 : Nat := 628061466303870182824859

theorem tailTrace_3669436 : CollatzResearch.WordTrace tailWord_3669436 prefixEnd_3669436 628061466303870182824859 := by
  unfold tailWord_3669436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66917662967133768310294081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89223550622845024413725441 66917662967133768310294081)
  ·
    refine ⟨50188247225350326232720561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66917662967133768310294081 50188247225350326232720561)
    ·
      refine ⟨37641185419012744674540421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50188247225350326232720561 37641185419012744674540421)
      ·
        refine ⟨7057722266064889626476329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37641185419012744674540421 7057722266064889626476329)
        ·
          refine ⟨5293291699548667219857247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057722266064889626476329 5293291699548667219857247)
          ·
            refine ⟨7939937549323000829785871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293291699548667219857247 7939937549323000829785871)
            ·
              refine ⟨11909906323984501244678807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939937549323000829785871 11909906323984501244678807)
              ·
                refine ⟨17864859485976751867018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909906323984501244678807 17864859485976751867018211)
                ·
                  refine ⟨26797289228965127800527317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17864859485976751867018211 26797289228965127800527317)
                  ·
                    refine ⟨628061466303870182824859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26797289228965127800527317 628061466303870182824859)
                    ·
                      rfl

theorem cell23_3669436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_3669436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669436 prefixEnd_3669436 := by exact prefixLift 3669436
  have htrace : WordTrace (prefixWord ++ tailWord_3669436) baseStart_3669436 baseEnd_3669436 := by
    simpa [prefixWord, tailWord_3669436, baseEnd_3669436] using wordTrace_append hprefix tailTrace_3669436
  have hstable : (prefixWord ++ tailWord_3669436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669436).length < 2 ^ (prefixWord ++ tailWord_3669436).sum := by decide
  have hdescent : baseEnd_3669436 < baseStart_3669436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669449 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_3669449 : Nat := 118140960795 + 3669449 * 2 ^ 59
def prefixEnd_3669449 : Nat := 4983230072969 + 3 ^ 40 * 3669449 * 2
def baseEnd_3669449 : Nat := 628063691386706332537339

theorem tailTrace_3669449 : CollatzResearch.WordTrace tailWord_3669449 prefixEnd_3669449 628063691386706332537339 := by
  unfold tailWord_3669449
  simp only [CollatzResearch.WordTrace]
  refine ⟨133835800083220439840811401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89223866722146959893874267 133835800083220439840811401)
  ·
    refine ⟨100376850062415329880608551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133835800083220439840811401 100376850062415329880608551)
    ·
      refine ⟨150565275093622994820912827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100376850062415329880608551 150565275093622994820912827)
      ·
        refine ⟨225847912640434492231369241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150565275093622994820912827 225847912640434492231369241)
        ·
          refine ⟨169385934480325869173526931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225847912640434492231369241 169385934480325869173526931)
          ·
            refine ⟨254078901720488803760290397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169385934480325869173526931 254078901720488803760290397)
            ·
              refine ⟨95279588145183301410108899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254078901720488803760290397 95279588145183301410108899)
              ·
                refine ⟨142919382217774952115163349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95279588145183301410108899 142919382217774952115163349)
                ·
                  refine ⟨3349673020729100440199141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142919382217774952115163349 3349673020729100440199141)
                  ·
                    refine ⟨628063691386706332537339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349673020729100440199141 628063691386706332537339)
                    ·
                      rfl

theorem cell23_3669449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_3669449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669449 prefixEnd_3669449 := by exact prefixLift 3669449
  have htrace : WordTrace (prefixWord ++ tailWord_3669449) baseStart_3669449 baseEnd_3669449 := by
    simpa [prefixWord, tailWord_3669449, baseEnd_3669449] using wordTrace_append hprefix tailTrace_3669449
  have hstable : (prefixWord ++ tailWord_3669449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669449).length < 2 ^ (prefixWord ++ tailWord_3669449).sum := by decide
  have hdescent : baseEnd_3669449 < baseStart_3669449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669466 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_3669466 : Nat := 118140960795 + 3669466 * 2 ^ 59
def prefixEnd_3669466 : Nat := 4983230072969 + 3 ^ 40 * 3669466 * 2
def baseEnd_3669466 : Nat := 628066601110415143699813

theorem tailTrace_3669466 : CollatzResearch.WordTrace tailWord_3669466 prefixEnd_3669466 628066601110415143699813 := by
  unfold tailWord_3669466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459105031039712936045063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89224280082772567829453501 33459105031039712936045063)
  ·
    refine ⟨50188657546559569404067595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33459105031039712936045063 50188657546559569404067595)
    ·
      refine ⟨75282986319839354106101393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50188657546559569404067595 75282986319839354106101393)
      ·
        refine ⟨56462239739879515579576045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75282986319839354106101393 56462239739879515579576045)
        ·
          refine ⟨21173339902454818342341017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56462239739879515579576045 21173339902454818342341017)
          ·
            refine ⟨15880004926841113756755763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21173339902454818342341017 15880004926841113756755763)
            ·
              refine ⟨23820007390261670635133645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15880004926841113756755763 23820007390261670635133645)
              ·
                refine ⟨8932502771348126488175117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23820007390261670635133645 8932502771348126488175117)
                ·
                  refine ⟨3349688539255547433065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8932502771348126488175117 3349688539255547433065669)
                  ·
                    refine ⟨628066601110415143699813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349688539255547433065669 628066601110415143699813)
                    ·
                      rfl

theorem cell23_3669466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_3669466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669466 prefixEnd_3669466 := by exact prefixLift 3669466
  have htrace : WordTrace (prefixWord ++ tailWord_3669466) baseStart_3669466 baseEnd_3669466 := by
    simpa [prefixWord, tailWord_3669466, baseEnd_3669466] using wordTrace_append hprefix tailTrace_3669466
  have hstable : (prefixWord ++ tailWord_3669466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669466).length < 2 ^ (prefixWord ++ tailWord_3669466).sum := by decide
  have hdescent : baseEnd_3669466 < baseStart_3669466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669493 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3669493 : Nat := 118140960795 + 3669493 * 2 ^ 59
def prefixEnd_3669493 : Nat := 4983230072969 + 3 ^ 40 * 3669493 * 2
def baseEnd_3669493 : Nat := 1884213667308916825461815

theorem tailTrace_3669493 : CollatzResearch.WordTrace tailWord_3669493 prefixEnd_3669493 1884213667308916825461815 := by
  unfold tailWord_3669493
  simp only [CollatzResearch.WordTrace]
  refine ⟨133837404895061035355413133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89224936596707356903608755 133837404895061035355413133)
  ·
    refine ⟨50189026835647888258279925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133837404895061035355413133 50189026835647888258279925)
    ·
      refine ⟨4705221265841989524213743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50189026835647888258279925 4705221265841989524213743)
      ·
        refine ⟨7057831898762984286320615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705221265841989524213743 7057831898762984286320615)
        ·
          refine ⟨10586747848144476429480923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057831898762984286320615 10586747848144476429480923)
          ·
            refine ⟨15880121772216714644221385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586747848144476429480923 15880121772216714644221385)
            ·
              refine ⟨11910091329162535983166039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15880121772216714644221385 11910091329162535983166039)
              ·
                refine ⟨17865136993743803974749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11910091329162535983166039 17865136993743803974749059)
                ·
                  refine ⟨26797705490615705962123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17865136993743803974749059 26797705490615705962123589)
                  ·
                    refine ⟨5024569779490444867898173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26797705490615705962123589 5024569779490444867898173)
                    ·
                      refine ⟨1884213667308916825461815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5024569779490444867898173 1884213667308916825461815)
                      ·
                        rfl

theorem cell23_3669493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3669493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669493 prefixEnd_3669493 := by exact prefixLift 3669493
  have htrace : WordTrace (prefixWord ++ tailWord_3669493) baseStart_3669493 baseEnd_3669493 := by
    simpa [prefixWord, tailWord_3669493, baseEnd_3669493] using wordTrace_append hprefix tailTrace_3669493
  have hstable : (prefixWord ++ tailWord_3669493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669493).length < 2 ^ (prefixWord ++ tailWord_3669493).sum := by decide
  have hdescent : baseEnd_3669493 < baseStart_3669493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669509 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3669509 : Nat := 118140960795 + 3669509 * 2 ^ 59
def prefixEnd_3669509 : Nat := 4983230072969 + 3 ^ 40 * 3669509 * 2
def baseEnd_3669509 : Nat := 628073960999796254287247

theorem tailTrace_3669509 : CollatzResearch.WordTrace tailWord_3669509 prefixEnd_3669509 628073960999796254287247 := by
  unfold tailWord_3669509
  simp only [CollatzResearch.WordTrace]
  refine ⟨133837988463003070087995581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89225325642002046725330387 133837988463003070087995581)
  ·
    refine ⟨50189245673626151282998343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133837988463003070087995581 50189245673626151282998343)
    ·
      refine ⟨75283868510439226924497515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50189245673626151282998343 75283868510439226924497515)
      ·
        refine ⟨112925802765658840386746273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75283868510439226924497515 112925802765658840386746273)
        ·
          refine ⟨84694352074244130290059705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112925802765658840386746273 84694352074244130290059705)
          ·
            refine ⟨63520764055683097717544779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84694352074244130290059705 63520764055683097717544779)
            ·
              refine ⟨95281146083524646576317169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63520764055683097717544779 95281146083524646576317169)
              ·
                refine ⟨71460859562643484932237877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95281146083524646576317169 71460859562643484932237877)
                ·
                  refine ⟨6699455583997826712397301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71460859562643484932237877 6699455583997826712397301)
                  ·
                    refine ⟨628073960999796254287247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6699455583997826712397301 628073960999796254287247)
                    ·
                      rfl

theorem cell23_3669509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3669509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669509 prefixEnd_3669509 := by exact prefixLift 3669509
  have htrace : WordTrace (prefixWord ++ tailWord_3669509) baseStart_3669509 baseEnd_3669509 := by
    simpa [prefixWord, tailWord_3669509, baseEnd_3669509] using wordTrace_append hprefix tailTrace_3669509
  have hstable : (prefixWord ++ tailWord_3669509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669509).length < 2 ^ (prefixWord ++ tailWord_3669509).sum := by decide
  have hdescent : baseEnd_3669509 < baseStart_3669509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669523 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 3]
def baseStart_3669523 : Nat := 118140960795 + 3669523 * 2 ^ 59
def prefixEnd_3669523 : Nat := 4983230072969 + 3 ^ 40 * 3669523 * 2
def baseEnd_3669523 : Nat := 1884229071728551708086677

theorem tailTrace_3669523 : CollatzResearch.WordTrace tailWord_3669523 prefixEnd_3669523 1884229071728551708086677 := by
  unfold tailWord_3669523
  simp only [CollatzResearch.WordTrace]
  refine ⟨133838499084952350479005223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89225666056634900319336815 133838499084952350479005223)
  ·
    refine ⟨200757748627428525718507835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133838499084952350479005223 200757748627428525718507835)
    ·
      refine ⟨301136622941142788577761753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200757748627428525718507835 301136622941142788577761753)
      ·
        refine ⟨225852467205857091433321315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301136622941142788577761753 225852467205857091433321315)
        ·
          refine ⟨338778700808785637149981973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225852467205857091433321315 338778700808785637149981973)
          ·
            refine ⟨15880251600411826741405405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338778700808785637149981973 15880251600411826741405405)
            ·
              refine ⟨5955094350154435028027027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15880251600411826741405405 5955094350154435028027027)
              ·
                refine ⟨8932641525231652542040541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955094350154435028027027 8932641525231652542040541)
                ·
                  refine ⟨3349740571961869703265203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8932641525231652542040541 3349740571961869703265203)
                  ·
                    refine ⟨5024610857942804554897805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349740571961869703265203 5024610857942804554897805)
                    ·
                      refine ⟨1884229071728551708086677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5024610857942804554897805 1884229071728551708086677)
                      ·
                        rfl

theorem cell23_3669523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_3669523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669523 prefixEnd_3669523 := by exact prefixLift 3669523
  have htrace : WordTrace (prefixWord ++ tailWord_3669523) baseStart_3669523 baseEnd_3669523 := by
    simpa [prefixWord, tailWord_3669523, baseEnd_3669523] using wordTrace_append hprefix tailTrace_3669523
  have hstable : (prefixWord ++ tailWord_3669523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669523).length < 2 ^ (prefixWord ++ tailWord_3669523).sum := by decide
  have hdescent : baseEnd_3669523 < baseStart_3669523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669533 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_3669533 : Nat := 118140960795 + 3669533 * 2 ^ 59
def prefixEnd_3669533 : Nat := 4983230072969 + 3 ^ 40 * 3669533 * 2
def baseEnd_3669533 : Nat := 1884234206535096668961631

theorem tailTrace_3669533 : CollatzResearch.WordTrace tailWord_3669533 prefixEnd_3669533 1884234206535096668961631 := by
  unfold tailWord_3669533
  simp only [CollatzResearch.WordTrace]
  refine ⟨133838863814916122186869253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89225909209944081457912835 133838863814916122186869253)
  ·
    refine ⟨25094786965296772910037985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133838863814916122186869253 25094786965296772910037985)
    ·
      refine ⟨18821090223972579682528489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25094786965296772910037985 18821090223972579682528489)
      ·
        refine ⟨14115817667979434761896367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18821090223972579682528489 14115817667979434761896367)
        ·
          refine ⟨21173726501969152142844551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115817667979434761896367 21173726501969152142844551)
          ·
            refine ⟨31760589752953728214266827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21173726501969152142844551 31760589752953728214266827)
            ·
              refine ⟨47640884629430592321400241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31760589752953728214266827 47640884629430592321400241)
              ·
                refine ⟨35730663472072944241050181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47640884629430592321400241 35730663472072944241050181)
                ·
                  refine ⟨6699499401013677045196909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35730663472072944241050181 6699499401013677045196909)
                  ·
                    refine ⟨2512312275380128891948841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6699499401013677045196909 2512312275380128891948841)
                    ·
                      refine ⟨1884234206535096668961631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512312275380128891948841 1884234206535096668961631)
                      ·
                        rfl

theorem cell23_3669533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_3669533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669533 prefixEnd_3669533 := by exact prefixLift 3669533
  have htrace : WordTrace (prefixWord ++ tailWord_3669533) baseStart_3669533 baseEnd_3669533 := by
    simpa [prefixWord, tailWord_3669533, baseEnd_3669533] using wordTrace_append hprefix tailTrace_3669533
  have hstable : (prefixWord ++ tailWord_3669533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669533).length < 2 ^ (prefixWord ++ tailWord_3669533).sum := by decide
  have hdescent : baseEnd_3669533 < baseStart_3669533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669550 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3669550 : Nat := 118140960795 + 3669550 * 2 ^ 59
def prefixEnd_3669550 : Nat := 4983230072969 + 3 ^ 40 * 3669550 * 2
def baseEnd_3669550 : Nat := 1884242935706223102449053

theorem tailTrace_3669550 : CollatzResearch.WordTrace tailWord_3669550 prefixEnd_3669550 1884242935706223102449053 := by
  unfold tailWord_3669550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729935481981816761279763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89226322570569689393492069 16729935481981816761279763)
  ·
    refine ⟨25094903222972725141919645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16729935481981816761279763 25094903222972725141919645)
    ·
      refine ⟨9410588708614771928219867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25094903222972725141919645 9410588708614771928219867)
      ·
        refine ⟨14115883062922157892329801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9410588708614771928219867 14115883062922157892329801)
        ·
          refine ⟨10586912297191618419247351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14115883062922157892329801 10586912297191618419247351)
          ·
            refine ⟨15880368445787427628871027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586912297191618419247351 15880368445787427628871027)
            ·
              refine ⟨23820552668681141443306541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15880368445787427628871027 23820552668681141443306541)
              ·
                refine ⟨8932707250755428041239953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23820552668681141443306541 8932707250755428041239953)
                ·
                  refine ⟨6699530438066571030929965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932707250755428041239953 6699530438066571030929965)
                  ·
                    refine ⟨2512323914274964136598737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6699530438066571030929965 2512323914274964136598737)
                    ·
                      refine ⟨1884242935706223102449053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512323914274964136598737 1884242935706223102449053)
                      ·
                        rfl

theorem cell23_3669550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3669550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669550 prefixEnd_3669550 := by exact prefixLift 3669550
  have htrace : WordTrace (prefixWord ++ tailWord_3669550) baseStart_3669550 baseEnd_3669550 := by
    simpa [prefixWord, tailWord_3669550, baseEnd_3669550] using wordTrace_append hprefix tailTrace_3669550
  have hstable : (prefixWord ++ tailWord_3669550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669550).length < 2 ^ (prefixWord ++ tailWord_3669550).sum := by decide
  have hdescent : baseEnd_3669550 < baseStart_3669550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669573 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3669573 : Nat := 118140960795 + 3669573 * 2 ^ 59
def prefixEnd_3669573 : Nat := 4983230072969 + 3 ^ 40 * 3669573 * 2
def baseEnd_3669573 : Nat := 628084915253758837487149

theorem tailTrace_3669573 : CollatzResearch.WordTrace tailWord_3669573 prefixEnd_3669573 628084915253758837487149 := by
  unfold tailWord_3669573
  simp only [CollatzResearch.WordTrace]
  refine ⟨133840322734771209018325373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89226881823180806012216915 133840322734771209018325373)
  ·
    refine ⟨50190121025539203381872015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133840322734771209018325373 50190121025539203381872015)
    ·
      refine ⟨75285181538308805072808023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50190121025539203381872015 75285181538308805072808023)
      ·
        refine ⟨112927772307463207609212035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75285181538308805072808023 112927772307463207609212035)
        ·
          refine ⟨169391658461194811413818053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112927772307463207609212035 169391658461194811413818053)
          ·
            refine ⟨31760935961474027140090885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169391658461194811413818053 31760935961474027140090885)
            ·
              refine ⟨5955175492776380088767041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31760935961474027140090885 5955175492776380088767041)
              ·
                refine ⟨4466381619582285066575281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955175492776380088767041 4466381619582285066575281)
                ·
                  refine ⟨3349786214686713799931461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466381619582285066575281 3349786214686713799931461)
                  ·
                    refine ⟨628084915253758837487149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349786214686713799931461 628084915253758837487149)
                    ·
                      rfl

theorem cell23_3669573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3669573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669573 prefixEnd_3669573 := by exact prefixLift 3669573
  have htrace : WordTrace (prefixWord ++ tailWord_3669573) baseStart_3669573 baseEnd_3669573 := by
    simpa [prefixWord, tailWord_3669573, baseEnd_3669573] using wordTrace_append hprefix tailTrace_3669573
  have hstable : (prefixWord ++ tailWord_3669573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669573).length < 2 ^ (prefixWord ++ tailWord_3669573).sum := by decide
  have hdescent : baseEnd_3669573 < baseStart_3669573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669586 : List Nat := [3, 2, 2, 1, 2, 2, 3, 8]
def baseStart_3669586 : Nat := 118140960795 + 3669586 * 2 ^ 59
def prefixEnd_3669586 : Nat := 4983230072969 + 3 ^ 40 * 3669586 * 2
def baseEnd_3669586 : Nat := 69787460037399443022181

theorem tailTrace_3669586 : CollatzResearch.WordTrace tailWord_3669586 prefixEnd_3669586 69787460037399443022181 := by
  unfold tailWord_3669586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33460199220931028059637153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89227197922482741492365741 33460199220931028059637153)
  ·
    refine ⟨25095149415698271044727865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33460199220931028059637153 25095149415698271044727865)
    ·
      refine ⟨18821362061773703283545899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095149415698271044727865 18821362061773703283545899)
      ·
        refine ⟨28232043092660554925318849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821362061773703283545899 28232043092660554925318849)
        ·
          refine ⟨21174032319495416193989137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28232043092660554925318849 21174032319495416193989137)
          ·
            refine ⟨15880524239621562145491853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21174032319495416193989137 15880524239621562145491853)
            ·
              refine ⟨5955196589858085804559445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15880524239621562145491853 5955196589858085804559445)
              ·
                refine ⟨69787460037399443022181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5955196589858085804559445 69787460037399443022181)
                ·
                  rfl

theorem cell23_3669586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_3669586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669586 prefixEnd_3669586 := by exact prefixLift 3669586
  have htrace : WordTrace (prefixWord ++ tailWord_3669586) baseStart_3669586 baseEnd_3669586 := by
    simpa [prefixWord, tailWord_3669586, baseEnd_3669586] using wordTrace_append hprefix tailTrace_3669586
  have hstable : (prefixWord ++ tailWord_3669586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669586).length < 2 ^ (prefixWord ++ tailWord_3669586).sum := by decide
  have hdescent : baseEnd_3669586 < baseStart_3669586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669614 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3669614 : Nat := 118140960795 + 3669614 * 2 ^ 59
def prefixEnd_3669614 : Nat := 4983230072969 + 3 ^ 40 * 3669614 * 2
def baseEnd_3669614 : Nat := 1884275798468110852048759

theorem tailTrace_3669614 : CollatzResearch.WordTrace tailWord_3669614 prefixEnd_3669614 1884275798468110852048759 := by
  unfold tailWord_3669614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730227265952834127570987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89227878751748448680378597 16730227265952834127570987)
  ·
    refine ⟨25095340898929251191356481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16730227265952834127570987 25095340898929251191356481)
    ·
      refine ⟨18821505674196938393517361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095340898929251191356481 18821505674196938393517361)
      ·
        refine ⟨14116129255647703795138021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18821505674196938393517361 14116129255647703795138021)
        ·
          refine ⟨2646774235433944461588379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14116129255647703795138021 2646774235433944461588379)
          ·
            refine ⟨3970161353150916692382569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646774235433944461588379 3970161353150916692382569)
            ·
              refine ⟨2977621014863187519286927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970161353150916692382569 2977621014863187519286927)
              ·
                refine ⟨4466431522294781278930391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977621014863187519286927 4466431522294781278930391)
                ·
                  refine ⟨6699647283442171918395587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466431522294781278930391 6699647283442171918395587)
                  ·
                    refine ⟨10049470925163257877593381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699647283442171918395587 10049470925163257877593381)
                    ·
                      refine ⟨1884275798468110852048759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10049470925163257877593381 1884275798468110852048759)
                      ·
                        rfl

theorem cell23_3669614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3669614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669614 prefixEnd_3669614 := by exact prefixLift 3669614
  have htrace : WordTrace (prefixWord ++ tailWord_3669614) baseStart_3669614 baseEnd_3669614 := by
    simpa [prefixWord, tailWord_3669614, baseEnd_3669614] using wordTrace_append hprefix tailTrace_3669614
  have hstable : (prefixWord ++ tailWord_3669614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669614).length < 2 ^ (prefixWord ++ tailWord_3669614).sum := by decide
  have hdescent : baseEnd_3669614 < baseStart_3669614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669743 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_3669743 : Nat := 118140960795 + 3669743 * 2 ^ 59
def prefixEnd_3669743 : Nat := 4983230072969 + 3 ^ 40 * 3669743 * 2
def baseEnd_3669743 : Nat := 1884342037472540847335665

theorem tailTrace_3669743 : CollatzResearch.WordTrace tailWord_3669743 prefixEnd_3669743 1884342037472540847335665 := by
  unfold tailWord_3669743
  simp only [CollatzResearch.WordTrace]
  refine ⟨133846523144155328052013883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89231015429436885368009255 133846523144155328052013883)
  ·
    refine ⟨200769784716232992078020825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133846523144155328052013883 200769784716232992078020825)
    ·
      refine ⟨150577338537174744058515619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200769784716232992078020825 150577338537174744058515619)
      ·
        refine ⟨225866007805762116087773429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150577338537174744058515619 225866007805762116087773429)
        ·
          refine ⟨21174938231790198383228759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225866007805762116087773429 21174938231790198383228759)
          ·
            refine ⟨31762407347685297574843139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21174938231790198383228759 31762407347685297574843139)
            ·
              refine ⟨47643611021527946362264709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31762407347685297574843139 47643611021527946362264709)
              ·
                refine ⟨8933177066536489942924633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47643611021527946362264709 8933177066536489942924633)
                ·
                  refine ⟨6699882799902367457193475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8933177066536489942924633 6699882799902367457193475)
                  ·
                    refine ⟨10049824199853551185790213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699882799902367457193475 10049824199853551185790213)
                    ·
                      refine ⟨1884342037472540847335665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10049824199853551185790213 1884342037472540847335665)
                      ·
                        rfl

theorem cell23_3669743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_3669743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669743 prefixEnd_3669743 := by exact prefixLift 3669743
  have htrace : WordTrace (prefixWord ++ tailWord_3669743) baseStart_3669743 baseEnd_3669743 := by
    simpa [prefixWord, tailWord_3669743, baseEnd_3669743] using wordTrace_append hprefix tailTrace_3669743
  have hstable : (prefixWord ++ tailWord_3669743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669743).length < 2 ^ (prefixWord ++ tailWord_3669743).sum := by decide
  have hdescent : baseEnd_3669743 < baseStart_3669743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669763 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3]
def baseStart_3669763 : Nat := 118140960795 + 3669763 * 2 ^ 59
def prefixEnd_3669763 : Nat := 4983230072969 + 3 ^ 40 * 3669763 * 2
def baseEnd_3669763 : Nat := 1884352307085630769085573

theorem tailTrace_3669763 : CollatzResearch.WordTrace tailWord_3669763 prefixEnd_3669763 1884352307085630769085573 := by
  unfold tailWord_3669763
  simp only [CollatzResearch.WordTrace]
  refine ⟨133847252604082871467741943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89231501736055247645161295 133847252604082871467741943)
  ·
    refine ⟨200770878906124307201612915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133847252604082871467741943 200770878906124307201612915)
    ·
      refine ⟨301156318359186460802419373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200770878906124307201612915 301156318359186460802419373)
      ·
        refine ⟨112933619384694922800907265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301156318359186460802419373 112933619384694922800907265)
        ·
          refine ⟨84700214538521192100680449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112933619384694922800907265 84700214538521192100680449)
          ·
            refine ⟨63525160903890894075510337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84700214538521192100680449 63525160903890894075510337)
            ·
              refine ⟨47643870677918170556632753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63525160903890894075510337 47643870677918170556632753)
              ·
                refine ⟨35732903008438627917474565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47643870677918170556632753 35732903008438627917474565)
                ·
                  refine ⟨6699919314082242734526481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35732903008438627917474565 6699919314082242734526481)
                  ·
                    refine ⟨5024939485561682050894861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699919314082242734526481 5024939485561682050894861)
                    ·
                      refine ⟨1884352307085630769085573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5024939485561682050894861 1884352307085630769085573)
                      ·
                        rfl

theorem cell23_3669763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_3669763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669763 prefixEnd_3669763 := by exact prefixLift 3669763
  have htrace : WordTrace (prefixWord ++ tailWord_3669763) baseStart_3669763 baseEnd_3669763 := by
    simpa [prefixWord, tailWord_3669763, baseEnd_3669763] using wordTrace_append hprefix tailTrace_3669763
  have hstable : (prefixWord ++ tailWord_3669763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669763).length < 2 ^ (prefixWord ++ tailWord_3669763).sum := by decide
  have hdescent : baseEnd_3669763 < baseStart_3669763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669770 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_3669770 : Nat := 118140960795 + 3669770 * 2 ^ 59
def prefixEnd_3669770 : Nat := 4983230072969 + 3 ^ 40 * 3669770 * 2
def baseEnd_3669770 : Nat := 628118633816737413899347

theorem tailTrace_3669770 : CollatzResearch.WordTrace tailWord_3669770 prefixEnd_3669770 628118633816737413899347 := by
  unfold tailWord_3669770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33461876978764377915811691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89231671943371674442164509 33461876978764377915811691)
  ·
    refine ⟨50192815468146566873717537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33461876978764377915811691 50192815468146566873717537)
    ·
      refine ⟨37644611601109925155288153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50192815468146566873717537 37644611601109925155288153)
      ·
        refine ⟨28233458700832443866466115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37644611601109925155288153 28233458700832443866466115)
        ·
          refine ⟨42350188051248665799699173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28233458700832443866466115 42350188051248665799699173)
          ·
            refine ⟨7940660259609124837443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42350188051248665799699173 7940660259609124837443595)
            ·
              refine ⟨11910990389413687256165393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7940660259609124837443595 11910990389413687256165393)
              ·
                refine ⟨8933242792060265442124045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11910990389413687256165393 8933242792060265442124045)
                ·
                  refine ⟨3349966047022599540796517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8933242792060265442124045 3349966047022599540796517)
                  ·
                    refine ⟨628118633816737413899347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349966047022599540796517 628118633816737413899347)
                    ·
                      rfl

theorem cell23_3669770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_3669770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669770 prefixEnd_3669770 := by exact prefixLift 3669770
  have htrace : WordTrace (prefixWord ++ tailWord_3669770) baseStart_3669770 baseEnd_3669770 := by
    simpa [prefixWord, tailWord_3669770, baseEnd_3669770] using wordTrace_append hprefix tailTrace_3669770
  have hstable : (prefixWord ++ tailWord_3669770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669770).length < 2 ^ (prefixWord ++ tailWord_3669770).sum := by decide
  have hdescent : baseEnd_3669770 < baseStart_3669770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669800 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 6]
def baseStart_3669800 : Nat := 118140960795 + 3669800 * 2 ^ 59
def prefixEnd_3669800 : Nat := 4983230072969 + 3 ^ 40 * 3669800 * 2
def baseEnd_3669800 : Nat := 209374589541094124924767

theorem tailTrace_3669800 : CollatzResearch.WordTrace tailWord_3669800 prefixEnd_3669800 209374589541094124924767 := by
  unfold tailWord_3669800
  simp only [CollatzResearch.WordTrace]
  refine ⟨66924301052474413393419427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89232401403299217857892569 66924301052474413393419427)
  ·
    refine ⟨100386451578711620090129141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66924301052474413393419427 100386451578711620090129141)
    ·
      refine ⟨9411229835504214383449607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100386451578711620090129141 9411229835504214383449607)
      ·
        refine ⟨14116844753256321575174411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411229835504214383449607 14116844753256321575174411)
        ·
          refine ⟨21175267129884482362761617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14116844753256321575174411 21175267129884482362761617)
          ·
            refine ⟨15881450347413361772071213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21175267129884482362761617 15881450347413361772071213)
            ·
              refine ⟨5955543880280010664526705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15881450347413361772071213 5955543880280010664526705)
              ·
                refine ⟨4466657910210007998395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955543880280010664526705 4466657910210007998395029)
                ·
                  refine ⟨209374589541094124924767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4466657910210007998395029 209374589541094124924767)
                  ·
                    rfl

theorem cell23_3669800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_3669800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669800 prefixEnd_3669800 := by exact prefixLift 3669800
  have htrace : WordTrace (prefixWord ++ tailWord_3669800) baseStart_3669800 baseEnd_3669800 := by
    simpa [prefixWord, tailWord_3669800, baseEnd_3669800] using wordTrace_append hprefix tailTrace_3669800
  have hstable : (prefixWord ++ tailWord_3669800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669800).length < 2 ^ (prefixWord ++ tailWord_3669800).sum := by decide
  have hdescent : baseEnd_3669800 < baseStart_3669800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669820 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_3669820 : Nat := 118140960795 + 3669820 * 2 ^ 59
def prefixEnd_3669820 : Nat := 4983230072969 + 3 ^ 40 * 3669820 * 2
def baseEnd_3669820 : Nat := 1884381575482937046072811

theorem tailTrace_3669820 : CollatzResearch.WordTrace tailWord_3669820 prefixEnd_3669820 1884381575482937046072811 := by
  unfold tailWord_3669820
  simp only [CollatzResearch.WordTrace]
  refine ⟨66924665782438185101283457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89232887709917580135044609 66924665782438185101283457)
  ·
    refine ⟨50193499336828638825962593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66924665782438185101283457 50193499336828638825962593)
    ·
      refine ⟨37645124502621479119471945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50193499336828638825962593 37645124502621479119471945)
      ·
        refine ⟨28233843376966109339603959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37645124502621479119471945 28233843376966109339603959)
        ·
          refine ⟨42350765065449164009405939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28233843376966109339603959 42350765065449164009405939)
          ·
            refine ⟨63526147598173746014108909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42350765065449164009405939 63526147598173746014108909)
            ·
              refine ⟨23822305349315154755290841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63526147598173746014108909 23822305349315154755290841)
              ·
                refine ⟨17866729011986366066468131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23822305349315154755290841 17866729011986366066468131)
                ·
                  refine ⟨26800093517979549099702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17866729011986366066468131 26800093517979549099702197)
                  ·
                    refine ⟨2512508767310582728097081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26800093517979549099702197 2512508767310582728097081)
                    ·
                      refine ⟨1884381575482937046072811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512508767310582728097081 1884381575482937046072811)
                      ·
                        rfl

theorem cell23_3669820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_3669820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669820 prefixEnd_3669820 := by exact prefixLift 3669820
  have htrace : WordTrace (prefixWord ++ tailWord_3669820) baseStart_3669820 baseEnd_3669820 := by
    simpa [prefixWord, tailWord_3669820, baseEnd_3669820] using wordTrace_append hprefix tailTrace_3669820
  have hstable : (prefixWord ++ tailWord_3669820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669820).length < 2 ^ (prefixWord ++ tailWord_3669820).sum := by decide
  have hdescent : baseEnd_3669820 < baseStart_3669820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669850 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_3669850 : Nat := 118140960795 + 3669850 * 2 ^ 59
def prefixEnd_3669850 : Nat := 4983230072969 + 3 ^ 40 * 3669850 * 2
def baseEnd_3669850 : Nat := 1884396979902571928697673

theorem tailTrace_3669850 : CollatzResearch.WordTrace tailWord_3669850 prefixEnd_3669850 1884396979902571928697673 := by
  unfold tailWord_3669850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462606438691921331539751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89233617169845123550772669 33462606438691921331539751)
  ·
    refine ⟨50193909658037881997309627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462606438691921331539751 50193909658037881997309627)
    ·
      refine ⟨75290864487056822995964441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193909658037881997309627 75290864487056822995964441)
      ·
        refine ⟨56468148365292617246973331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75290864487056822995964441 56468148365292617246973331)
        ·
          refine ⟨84702222547938925870459997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56468148365292617246973331 84702222547938925870459997)
          ·
            refine ⟨31763333455477097201422499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84702222547938925870459997 31763333455477097201422499)
            ·
              refine ⟨47645000183215645802133749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763333455477097201422499 47645000183215645802133749)
              ·
                refine ⟨4466718767176466793950039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47645000183215645802133749 4466718767176466793950039)
                ·
                  refine ⟨6700078150764700190925059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466718767176466793950039 6700078150764700190925059)
                  ·
                    refine ⟨10050117226147050286387589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6700078150764700190925059 10050117226147050286387589)
                    ·
                      refine ⟨1884396979902571928697673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10050117226147050286387589 1884396979902571928697673)
                      ·
                        rfl

theorem cell23_3669850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_3669850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669850 prefixEnd_3669850 := by exact prefixLift 3669850
  have htrace : WordTrace (prefixWord ++ tailWord_3669850) baseStart_3669850 baseEnd_3669850 := by
    simpa [prefixWord, tailWord_3669850, baseEnd_3669850] using wordTrace_append hprefix tailTrace_3669850
  have hstable : (prefixWord ++ tailWord_3669850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669850).length < 2 ^ (prefixWord ++ tailWord_3669850).sum := by decide
  have hdescent : baseEnd_3669850 < baseStart_3669850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669863 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3669863 : Nat := 118140960795 + 3669863 * 2 ^ 59
def prefixEnd_3669863 : Nat := 4983230072969 + 3 ^ 40 * 3669863 * 2
def baseEnd_3669863 : Nat := 1884403655151080377835113

theorem tailTrace_3669863 : CollatzResearch.WordTrace tailWord_3669863 prefixEnd_3669863 1884403655151080377835113 := by
  unfold tailWord_3669863
  simp only [CollatzResearch.WordTrace]
  refine ⟨133850899903720588546382243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89233933269147059030921495 133850899903720588546382243)
  ·
    refine ⟨200776349855580882819573365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133850899903720588546382243 200776349855580882819573365)
    ·
      refine ⟨18822782798960707764335003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200776349855580882819573365 18822782798960707764335003)
      ·
        refine ⟨28234174198441061646502505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18822782798960707764335003 28234174198441061646502505)
        ·
          refine ⟨21175630648830796234876879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28234174198441061646502505 21175630648830796234876879)
          ·
            refine ⟨31763445973246194352315319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175630648830796234876879 31763445973246194352315319)
            ·
              refine ⟨47645168959869291528472979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763445973246194352315319 47645168959869291528472979)
              ·
                refine ⟨71467753439803937292709469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47645168959869291528472979 71467753439803937292709469)
                ·
                  refine ⟨26800407539926476484766051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71467753439803937292709469 26800407539926476484766051)
                  ·
                    refine ⟨40200611309889714727149077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26800407539926476484766051 40200611309889714727149077)
                    ·
                      refine ⟨1884403655151080377835113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40200611309889714727149077 1884403655151080377835113)
                      ·
                        rfl

theorem cell23_3669863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3669863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669863 prefixEnd_3669863 := by exact prefixLift 3669863
  have htrace : WordTrace (prefixWord ++ tailWord_3669863) baseStart_3669863 baseEnd_3669863 := by
    simpa [prefixWord, tailWord_3669863, baseEnd_3669863] using wordTrace_append hprefix tailTrace_3669863
  have hstable : (prefixWord ++ tailWord_3669863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669863).length < 2 ^ (prefixWord ++ tailWord_3669863).sum := by decide
  have hdescent : baseEnd_3669863 < baseStart_3669863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669873 : List Nat := [1, 2, 2, 2, 1, 3, 4, 8]
def baseStart_3669873 : Nat := 118140960795 + 3669873 * 2 ^ 59
def prefixEnd_3669873 : Nat := 4983230072969 + 3 ^ 40 * 3669873 * 2
def baseEnd_3669873 : Nat := 69792918146578716248521

theorem tailTrace_3669873 : CollatzResearch.WordTrace tailWord_3669873 prefixEnd_3669873 69792918146578716248521 := by
  unfold tailWord_3669873
  simp only [CollatzResearch.WordTrace]
  refine ⟨133851264633684360254246273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89234176422456240169497515 133851264633684360254246273)
  ·
    refine ⟨100388448475263270190684705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133851264633684360254246273 100388448475263270190684705)
    ·
      refine ⟨75291336356447452643013529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100388448475263270190684705 75291336356447452643013529)
      ·
        refine ⟨56468502267335589482260147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75291336356447452643013529 56468502267335589482260147)
        ·
          refine ⟨84702753401003384223390221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56468502267335589482260147 84702753401003384223390221)
          ·
            refine ⟨31763532525376269083771333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84702753401003384223390221 31763532525376269083771333)
            ·
              refine ⟨5955662348508050453207125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31763532525376269083771333 5955662348508050453207125)
              ·
                refine ⟨69792918146578716248521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5955662348508050453207125 69792918146578716248521)
                ·
                  rfl

theorem cell23_3669873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 8].length) (baseStart_3669873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669873 prefixEnd_3669873 := by exact prefixLift 3669873
  have htrace : WordTrace (prefixWord ++ tailWord_3669873) baseStart_3669873 baseEnd_3669873 := by
    simpa [prefixWord, tailWord_3669873, baseEnd_3669873] using wordTrace_append hprefix tailTrace_3669873
  have hstable : (prefixWord ++ tailWord_3669873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669873).length < 2 ^ (prefixWord ++ tailWord_3669873).sum := by decide
  have hdescent : baseEnd_3669873 < baseStart_3669873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669877 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3669877 : Nat := 118140960795 + 3669877 * 2 ^ 59
def prefixEnd_3669877 : Nat := 4983230072969 + 3 ^ 40 * 3669877 * 2
def baseEnd_3669877 : Nat := 628136947960081107686683

theorem tailTrace_3669877 : CollatzResearch.WordTrace tailWord_3669877 prefixEnd_3669877 628136947960081107686683 := by
  unfold tailWord_3669877
  simp only [CollatzResearch.WordTrace]
  refine ⟨133851410525669868937391885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89234273683779912624927923 133851410525669868937391885)
  ·
    refine ⟨50194278947126200851521957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133851410525669868937391885 50194278947126200851521957)
    ·
      refine ⟨9411427302586162659660367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50194278947126200851521957 9411427302586162659660367)
      ·
        refine ⟨14117140953879243989490551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411427302586162659660367 14117140953879243989490551)
        ·
          refine ⟨21175711430818865984235827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14117140953879243989490551 21175711430818865984235827)
          ·
            refine ⟨31763567146228298976353741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175711430818865984235827 31763567146228298976353741)
            ·
              refine ⟨11911337679835612116132653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31763567146228298976353741 11911337679835612116132653)
              ·
                refine ⟨4466751629938354543549745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11911337679835612116132653 4466751629938354543549745)
                ·
                  refine ⟨3350063722453765907662309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466751629938354543549745 3350063722453765907662309)
                  ·
                    refine ⟨628136947960081107686683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350063722453765907662309 628136947960081107686683)
                    ·
                      rfl

theorem cell23_3669877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3669877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669877 prefixEnd_3669877 := by exact prefixLift 3669877
  have htrace : WordTrace (prefixWord ++ tailWord_3669877) baseStart_3669877 baseEnd_3669877 := by
    simpa [prefixWord, tailWord_3669877, baseEnd_3669877] using wordTrace_append hprefix tailTrace_3669877
  have hstable : (prefixWord ++ tailWord_3669877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669877).length < 2 ^ (prefixWord ++ tailWord_3669877).sum := by decide
  have hdescent : baseEnd_3669877 < baseStart_3669877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669913 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3669913 : Nat := 118140960795 + 3669913 * 2 ^ 59
def prefixEnd_3669913 : Nat := 4983230072969 + 3 ^ 40 * 3669913 * 2
def baseEnd_3669913 : Nat := 1884429329183805182209883

theorem tailTrace_3669913 : CollatzResearch.WordTrace tailWord_3669913 prefixEnd_3669913 1884429329183805182209883 := by
  unfold tailWord_3669913
  simp only [CollatzResearch.WordTrace]
  refine ⟨133852723553539447085702393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89235149035692964723801595 133852723553539447085702393)
  ·
    refine ⟨100389542665154585314276795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133852723553539447085702393 100389542665154585314276795)
    ·
      refine ⟨150584313997731877971415193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100389542665154585314276795 150584313997731877971415193)
      ·
        refine ⟨112938235498298908478561395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150584313997731877971415193 112938235498298908478561395)
        ·
          refine ⟨169407353247448362717842093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112938235498298908478561395 169407353247448362717842093)
          ·
            refine ⟨63527757467793136019190785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169407353247448362717842093 63527757467793136019190785)
            ·
              refine ⟨47645818100844852014393089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63527757467793136019190785 47645818100844852014393089)
              ·
                refine ⟨35734363575633639010794817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47645818100844852014393089 35734363575633639010794817)
                ·
                  refine ⟨26800772681725229258096113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35734363575633639010794817 26800772681725229258096113)
                  ·
                    refine ⟨20100579511293921943572085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26800772681725229258096113 20100579511293921943572085)
                    ·
                      refine ⟨1884429329183805182209883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20100579511293921943572085 1884429329183805182209883)
                      ·
                        rfl

theorem cell23_3669913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3669913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669913 prefixEnd_3669913 := by exact prefixLift 3669913
  have htrace : WordTrace (prefixWord ++ tailWord_3669913) baseStart_3669913 baseEnd_3669913 := by
    simpa [prefixWord, tailWord_3669913, baseEnd_3669913] using wordTrace_append hprefix tailTrace_3669913
  have hstable : (prefixWord ++ tailWord_3669913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669913).length < 2 ^ (prefixWord ++ tailWord_3669913).sum := by decide
  have hdescent : baseEnd_3669913 < baseStart_3669913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669963 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 9]
def baseStart_3669963 : Nat := 118140960795 + 3669963 * 2 ^ 59
def prefixEnd_3669963 : Nat := 4983230072969 + 3 ^ 40 * 3669963 * 2
def baseEnd_3669963 : Nat := 209383889246281109620517

theorem tailTrace_3669963 : CollatzResearch.WordTrace tailWord_3669963 prefixEnd_3669963 209383889246281109620517 := by
  unfold tailWord_3669963
  simp only [CollatzResearch.WordTrace]
  refine ⟨133854547203358305625022543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89236364802238870416681695 133854547203358305625022543)
  ·
    refine ⟨200781820805037458437533815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133854547203358305625022543 200781820805037458437533815)
    ·
      refine ⟨301172731207556187656300723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200781820805037458437533815 301172731207556187656300723)
      ·
        refine ⟨451759096811334281484451085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301172731207556187656300723 451759096811334281484451085)
        ·
          refine ⟨169409661304250355556669157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451759096811334281484451085 169409661304250355556669157)
          ·
            refine ⟨31764311494546941666875467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169409661304250355556669157 31764311494546941666875467)
            ·
              refine ⟨47646467241820412500313201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31764311494546941666875467 47646467241820412500313201)
              ·
                refine ⟨35734850431365309375234901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47646467241820412500313201 35734850431365309375234901)
                ·
                  refine ⟨209383889246281109620517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35734850431365309375234901 209383889246281109620517)
                  ·
                    rfl

theorem cell23_3669963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_3669963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669963 prefixEnd_3669963 := by exact prefixLift 3669963
  have htrace : WordTrace (prefixWord ++ tailWord_3669963) baseStart_3669963 baseEnd_3669963 := by
    simpa [prefixWord, tailWord_3669963, baseEnd_3669963] using wordTrace_append hprefix tailTrace_3669963
  have hstable : (prefixWord ++ tailWord_3669963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669963).length < 2 ^ (prefixWord ++ tailWord_3669963).sum := by decide
  have hdescent : baseEnd_3669963 < baseStart_3669963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669991 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3669991 : Nat := 118140960795 + 3669991 * 2 ^ 59
def prefixEnd_3669991 : Nat := 4983230072969 + 3 ^ 40 * 3669991 * 2
def baseEnd_3669991 : Nat := 1884469380674855877034525

theorem tailTrace_3669991 : CollatzResearch.WordTrace tailWord_3669991 prefixEnd_3669991 1884469380674855877034525 := by
  unfold tailWord_3669991
  simp only [CollatzResearch.WordTrace]
  refine ⟨133855568447256866407041827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89237045631504577604694551 133855568447256866407041827)
  ·
    refine ⟨200783352670885299610562741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133855568447256866407041827 200783352670885299610562741)
    ·
      refine ⟨18823439312895496838490257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200783352670885299610562741 18823439312895496838490257)
      ·
        refine ⟨14117579484671622628867693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18823439312895496838490257 14117579484671622628867693)
        ·
          refine ⟨5294092306751858485825385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14117579484671622628867693 5294092306751858485825385)
          ·
            refine ⟨3970569230063893864369039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294092306751858485825385 3970569230063893864369039)
            ·
              refine ⟨5955853845095840796553559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970569230063893864369039 5955853845095840796553559)
              ·
                refine ⟨8933780767643761194830339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955853845095840796553559 8933780767643761194830339)
                ·
                  refine ⟨13400671151465641792245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933780767643761194830339 13400671151465641792245509)
                  ·
                    refine ⟨2512625840899807836046033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13400671151465641792245509 2512625840899807836046033)
                    ·
                      refine ⟨1884469380674855877034525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512625840899807836046033 1884469380674855877034525)
                      ·
                        rfl

theorem cell23_3669991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3669991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3669991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3669991 prefixEnd_3669991 := by exact prefixLift 3669991
  have htrace : WordTrace (prefixWord ++ tailWord_3669991) baseStart_3669991 baseEnd_3669991 := by
    simpa [prefixWord, tailWord_3669991, baseEnd_3669991] using wordTrace_append hprefix tailTrace_3669991
  have hstable : (prefixWord ++ tailWord_3669991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669991).length < 2 ^ (prefixWord ++ tailWord_3669991).sum := by decide
  have hdescent : baseEnd_3669991 < baseStart_3669991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670037 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3670037 : Nat := 118140960795 + 3670037 * 2 ^ 59
def prefixEnd_3670037 : Nat := 4983230072969 + 3 ^ 40 * 3670037 * 2
def baseEnd_3670037 : Nat := 1884493000784962697059313

theorem tailTrace_3670037 : CollatzResearch.WordTrace tailWord_3670037 prefixEnd_3670037 1884493000784962697059313 := by
  unfold tailWord_3670037
  simp only [CollatzResearch.WordTrace]
  refine ⟨133857246205090216263216365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89238164136726810842144243 133857246205090216263216365)
  ·
    refine ⟨50196467326908831098706137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133857246205090216263216365 50196467326908831098706137)
    ·
      refine ⟨37647350495181623324029603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50196467326908831098706137 37647350495181623324029603)
      ·
        refine ⟨56471025742772434986044405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37647350495181623324029603 56471025742772434986044405)
        ·
          refine ⟨5294158663384915779941663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56471025742772434986044405 5294158663384915779941663)
          ·
            refine ⟨7941237995077373669912495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294158663384915779941663 7941237995077373669912495)
            ·
              refine ⟨11911856992616060504868743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941237995077373669912495 11911856992616060504868743)
              ·
                refine ⟨17867785488924090757303115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11911856992616060504868743 17867785488924090757303115)
                ·
                  refine ⟨26801678233386136135954673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17867785488924090757303115 26801678233386136135954673)
                  ·
                    refine ⟨20101258675039602101966005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26801678233386136135954673 20101258675039602101966005)
                    ·
                      refine ⟨1884493000784962697059313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20101258675039602101966005 1884493000784962697059313)
                      ·
                        rfl

theorem cell23_3670037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3670037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670037 prefixEnd_3670037 := by exact prefixLift 3670037
  have htrace : WordTrace (prefixWord ++ tailWord_3670037) baseStart_3670037 baseEnd_3670037 := by
    simpa [prefixWord, tailWord_3670037, baseEnd_3670037] using wordTrace_append hprefix tailTrace_3670037
  have hstable : (prefixWord ++ tailWord_3670037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670037).length < 2 ^ (prefixWord ++ tailWord_3670037).sum := by decide
  have hdescent : baseEnd_3670037 < baseStart_3670037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670047 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 6, 2]
def baseStart_3670047 : Nat := 118140960795 + 3670047 * 2 ^ 59
def prefixEnd_3670047 : Nat := 4983230072969 + 3 ^ 40 * 3670047 * 2
def baseEnd_3670047 : Nat := 1884498135591507657934267

theorem tailTrace_3670047 : CollatzResearch.WordTrace tailWord_3670047 prefixEnd_3670047 1884498135591507657934267 := by
  unfold tailWord_3670047
  simp only [CollatzResearch.WordTrace]
  refine ⟨133857610935053987971080395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89238407290035991980720263 133857610935053987971080395)
  ·
    refine ⟨200786416402580981956620593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133857610935053987971080395 200786416402580981956620593)
    ·
      refine ⟨150589812301935736467465445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200786416402580981956620593 150589812301935736467465445)
      ·
        refine ⟨28235589806612950587649771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150589812301935736467465445 28235589806612950587649771)
        ·
          refine ⟨42353384709919425881474657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28235589806612950587649771 42353384709919425881474657)
          ·
            refine ⟨31765038532439569411105993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42353384709919425881474657 31765038532439569411105993)
            ·
              refine ⟨23823778899329677058329495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31765038532439569411105993 23823778899329677058329495)
              ·
                refine ⟨35735668348994515587494243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23823778899329677058329495 35735668348994515587494243)
                ·
                  refine ⟨53603502523491773381241365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35735668348994515587494243 53603502523491773381241365)
                  ·
                    refine ⟨2512664180788676877245689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53603502523491773381241365 2512664180788676877245689)
                    ·
                      refine ⟨1884498135591507657934267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512664180788676877245689 1884498135591507657934267)
                      ·
                        rfl

theorem cell23_3670047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_3670047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670047 prefixEnd_3670047 := by exact prefixLift 3670047
  have htrace : WordTrace (prefixWord ++ tailWord_3670047) baseStart_3670047 baseEnd_3670047 := by
    simpa [prefixWord, tailWord_3670047, baseEnd_3670047] using wordTrace_append hprefix tailTrace_3670047
  have hstable : (prefixWord ++ tailWord_3670047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670047).length < 2 ^ (prefixWord ++ tailWord_3670047).sum := by decide
  have hdescent : baseEnd_3670047 < baseStart_3670047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670067 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3]
def baseStart_3670067 : Nat := 118140960795 + 3670067 * 2 ^ 59
def prefixEnd_3670067 : Nat := 4983230072969 + 3 ^ 40 * 3670067 * 2
def baseEnd_3670067 : Nat := 1884508405204597579684175

theorem tailTrace_3670067 : CollatzResearch.WordTrace tailWord_3670067 prefixEnd_3670067 1884508405204597579684175 := by
  unfold tailWord_3670067
  simp only [CollatzResearch.WordTrace]
  refine ⟨133858340394981531386808455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89238893596654354257872303 133858340394981531386808455)
  ·
    refine ⟨200787510592472297080212683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133858340394981531386808455 200787510592472297080212683)
    ·
      refine ⟨301181265888708445620319025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200787510592472297080212683 301181265888708445620319025)
      ·
        refine ⟨225885949416531334215239269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301181265888708445620319025 225885949416531334215239269)
        ·
          refine ⟨42353615515599625165357363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225885949416531334215239269 42353615515599625165357363)
          ·
            refine ⟨63530423273399437748036045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42353615515599625165357363 63530423273399437748036045)
            ·
              refine ⟨23823908727524789155513517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63530423273399437748036045 23823908727524789155513517)
              ·
                refine ⟨8933965772821795933317569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23823908727524789155513517 8933965772821795933317569)
                ·
                  refine ⟨6700474329616346949988177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8933965772821795933317569 6700474329616346949988177)
                  ·
                    refine ⟨5025355747212260212491133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6700474329616346949988177 5025355747212260212491133)
                    ·
                      refine ⟨1884508405204597579684175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5025355747212260212491133 1884508405204597579684175)
                      ·
                        rfl

theorem cell23_3670067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_3670067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670067 prefixEnd_3670067 := by exact prefixLift 3670067
  have htrace : WordTrace (prefixWord ++ tailWord_3670067) baseStart_3670067 baseEnd_3670067 := by
    simpa [prefixWord, tailWord_3670067, baseEnd_3670067] using wordTrace_append hprefix tailTrace_3670067
  have hstable : (prefixWord ++ tailWord_3670067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670067).length < 2 ^ (prefixWord ++ tailWord_3670067).sum := by decide
  have hdescent : baseEnd_3670067 < baseStart_3670067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670074 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_3670074 : Nat := 118140960795 + 3670074 * 2 ^ 59
def prefixEnd_3670074 : Nat := 4983230072969 + 3 ^ 40 * 3670074 * 2
def baseEnd_3670074 : Nat := 628170666523059684098881

theorem tailTrace_3670074 : CollatzResearch.WordTrace tailWord_3670074 prefixEnd_3670074 628170666523059684098881 := by
  unfold tailWord_3670074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464648926489042895578319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89239063803970781054875517 33464648926489042895578319)
  ·
    refine ⟨50196973389733564343367479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33464648926489042895578319 50196973389733564343367479)
    ·
      refine ⟨75295460084600346515051219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50196973389733564343367479 75295460084600346515051219)
      ·
        refine ⟨112943190126900519772576829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75295460084600346515051219 112943190126900519772576829)
        ·
          refine ⟨42353696297587694914716311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112943190126900519772576829 42353696297587694914716311)
          ·
            refine ⟨63530544446381542372074467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42353696297587694914716311 63530544446381542372074467)
            ·
              refine ⟨95295816669572313558111701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63530544446381542372074467 95295816669572313558111701)
              ·
                refine ⟨2233495703193101099018243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95295816669572313558111701 2233495703193101099018243)
                ·
                  refine ⟨3350243554789651648527365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233495703193101099018243 3350243554789651648527365)
                  ·
                    refine ⟨628170666523059684098881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350243554789651648527365 628170666523059684098881)
                    ·
                      rfl

theorem cell23_3670074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_3670074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670074 prefixEnd_3670074 := by exact prefixLift 3670074
  have htrace : WordTrace (prefixWord ++ tailWord_3670074) baseStart_3670074 baseEnd_3670074 := by
    simpa [prefixWord, tailWord_3670074, baseEnd_3670074] using wordTrace_append hprefix tailTrace_3670074
  have hstable : (prefixWord ++ tailWord_3670074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670074).length < 2 ^ (prefixWord ++ tailWord_3670074).sum := by decide
  have hdescent : baseEnd_3670074 < baseStart_3670074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670087 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 6]
def baseStart_3670087 : Nat := 118140960795 + 3670087 * 2 ^ 59
def prefixEnd_3670087 : Nat := 4983230072969 + 3 ^ 40 * 3670087 * 2
def baseEnd_3670087 : Nat := 209390963868631944603787

theorem tailTrace_3670087 : CollatzResearch.WordTrace tailWord_3670087 prefixEnd_3670087 209390963868631944603787 := by
  unfold tailWord_3670087
  simp only [CollatzResearch.WordTrace]
  refine ⟨133859069854909074802536515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89239379903272716535024343 133859069854909074802536515)
  ·
    refine ⟨200788604782363612203804773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133859069854909074802536515 200788604782363612203804773)
    ·
      refine ⟨37647863396693177288213395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200788604782363612203804773 37647863396693177288213395)
      ·
        refine ⟨56471795095039765932320093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37647863396693177288213395 56471795095039765932320093)
        ·
          refine ⟨21176923160639912224620035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56471795095039765932320093 21176923160639912224620035)
          ·
            refine ⟨31765384740959868336930053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21176923160639912224620035 31765384740959868336930053)
            ·
              refine ⟨5956009638929975313174385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31765384740959868336930053 5956009638929975313174385)
              ·
                refine ⟨4467007229197481484880789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956009638929975313174385 4467007229197481484880789)
                ·
                  refine ⟨209390963868631944603787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4467007229197481484880789 209390963868631944603787)
                  ·
                    rfl

theorem cell23_3670087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 6].length) (baseStart_3670087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670087 prefixEnd_3670087 := by exact prefixLift 3670087
  have htrace : WordTrace (prefixWord ++ tailWord_3670087) baseStart_3670087 baseEnd_3670087 := by
    simpa [prefixWord, tailWord_3670087, baseEnd_3670087] using wordTrace_append hprefix tailTrace_3670087
  have hstable : (prefixWord ++ tailWord_3670087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670087).length < 2 ^ (prefixWord ++ tailWord_3670087).sum := by decide
  have hdescent : baseEnd_3670087 < baseStart_3670087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670090 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3670090 : Nat := 118140960795 + 3670090 * 2 ^ 59
def prefixEnd_3670090 : Nat := 4983230072969 + 3 ^ 40 * 3670090 * 2
def baseEnd_3670090 : Nat := 1884520215259650989696569

theorem tailTrace_3670090 : CollatzResearch.WordTrace tailWord_3670090 prefixEnd_3670090 1884520215259650989696569 := by
  unfold tailWord_3670090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464794818474551578723931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89239452849265470876597149 33464794818474551578723931)
  ·
    refine ⟨50197192227711827368085897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33464794818474551578723931 50197192227711827368085897)
    ·
      refine ⟨37647894170783870526064423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50197192227711827368085897 37647894170783870526064423)
      ·
        refine ⟨56471841256175805789096635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37647894170783870526064423 56471841256175805789096635)
        ·
          refine ⟨84707761884263708683644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56471841256175805789096635 84707761884263708683644953)
          ·
            refine ⟨63530821413197781512733715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84707761884263708683644953 63530821413197781512733715)
            ·
              refine ⟨95296232119796672269100573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63530821413197781512733715 95296232119796672269100573)
              ·
                refine ⟨35736087044923752100912715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95296232119796672269100573 35736087044923752100912715)
                ·
                  refine ⟨53604130567385628151369073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35736087044923752100912715 53604130567385628151369073)
                  ·
                    refine ⟨40203097925539221113526805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53604130567385628151369073 40203097925539221113526805)
                    ·
                      refine ⟨1884520215259650989696569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40203097925539221113526805 1884520215259650989696569)
                      ·
                        rfl

theorem cell23_3670090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3670090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670090 prefixEnd_3670090 := by exact prefixLift 3670090
  have htrace : WordTrace (prefixWord ++ tailWord_3670090) baseStart_3670090 baseEnd_3670090 := by
    simpa [prefixWord, tailWord_3670090, baseEnd_3670090] using wordTrace_append hprefix tailTrace_3670090
  have hstable : (prefixWord ++ tailWord_3670090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670090).length < 2 ^ (prefixWord ++ tailWord_3670090).sum := by decide
  have hdescent : baseEnd_3670090 < baseStart_3670090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670117 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3670117 : Nat := 118140960795 + 3670117 * 2 ^ 59
def prefixEnd_3670117 : Nat := 4983230072969 + 3 ^ 40 * 3670117 * 2
def baseEnd_3670117 : Nat := 628178026412440794686315

theorem tailTrace_3670117 : CollatzResearch.WordTrace tailWord_3670117 prefixEnd_3670117 628178026412440794686315 := by
  unfold tailWord_3670117
  simp only [CollatzResearch.WordTrace]
  refine ⟨133860164044800389926128605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89240109363200259950752403 133860164044800389926128605)
  ·
    refine ⟨50197561516800146222298227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133860164044800389926128605 50197561516800146222298227)
    ·
      refine ⟨75296342275200219333447341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50197561516800146222298227 75296342275200219333447341)
      ·
        refine ⟨28236128353200082250042753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75296342275200219333447341 28236128353200082250042753)
        ·
          refine ⟨21177096264900061687532065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28236128353200082250042753 21177096264900061687532065)
          ·
            refine ⟨15882822198675046265649049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21177096264900061687532065 15882822198675046265649049)
            ·
              refine ⟨11912116649006284699236787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15882822198675046265649049 11912116649006284699236787)
              ·
                refine ⟨17868174973509427048855181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11912116649006284699236787 17868174973509427048855181)
                ·
                  refine ⟨6700565615066035143320693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17868174973509427048855181 6700565615066035143320693)
                  ·
                    refine ⟨628178026412440794686315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6700565615066035143320693 628178026412440794686315)
                    ·
                      rfl

theorem cell23_3670117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3670117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670117 prefixEnd_3670117 := by exact prefixLift 3670117
  have htrace : WordTrace (prefixWord ++ tailWord_3670117) baseStart_3670117 baseEnd_3670117 := by
    simpa [prefixWord, tailWord_3670117, baseEnd_3670117] using wordTrace_append hprefix tailTrace_3670117
  have hstable : (prefixWord ++ tailWord_3670117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670117).length < 2 ^ (prefixWord ++ tailWord_3670117).sum := by decide
  have hdescent : baseEnd_3670117 < baseStart_3670117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670124 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_3670124 : Nat := 118140960795 + 3670124 * 2 ^ 59
def prefixEnd_3670124 : Nat := 4983230072969 + 3 ^ 40 * 3670124 * 2
def baseEnd_3670124 : Nat := 1884537673601903856671413

theorem tailTrace_3670124 : CollatzResearch.WordTrace tailWord_3670124 prefixEnd_3670124 1884537673601903856671413 := by
  unfold tailWord_3670124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66930209677887515060816713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89240279570516686747755617 66930209677887515060816713)
  ·
    refine ⟨50197657258415636295612535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66930209677887515060816713 50197657258415636295612535)
    ·
      refine ⟨75296485887623454443418803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50197657258415636295612535 75296485887623454443418803)
      ·
        refine ⟨112944728831435181665128205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75296485887623454443418803 112944728831435181665128205)
        ·
          refine ⟨42354273311788193124423077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112944728831435181665128205 42354273311788193124423077)
          ·
            refine ⟨7941426245960286210829327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42354273311788193124423077 7941426245960286210829327)
            ·
              refine ⟨11912139368940429316243991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941426245960286210829327 11912139368940429316243991)
              ·
                refine ⟨17868209053410643974365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11912139368940429316243991 17868209053410643974365987)
                ·
                  refine ⟨26802313580115965961548981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17868209053410643974365987 26802313580115965961548981)
                  ·
                    refine ⟨2512716898135871808895217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26802313580115965961548981 2512716898135871808895217)
                    ·
                      refine ⟨1884537673601903856671413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512716898135871808895217 1884537673601903856671413)
                      ·
                        rfl

theorem cell23_3670124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_3670124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670124 prefixEnd_3670124 := by exact prefixLift 3670124
  have htrace : WordTrace (prefixWord ++ tailWord_3670124) baseStart_3670124 baseEnd_3670124 := by
    simpa [prefixWord, tailWord_3670124, baseEnd_3670124] using wordTrace_append hprefix tailTrace_3670124
  have hstable : (prefixWord ++ tailWord_3670124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670124).length < 2 ^ (prefixWord ++ tailWord_3670124).sum := by decide
  have hdescent : baseEnd_3670124 < baseStart_3670124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670160 : List Nat := [2, 1, 1, 1, 1, 1, 6, 10]
def baseStart_3670160 : Nat := 118140960795 + 3670160 * 2 ^ 59
def prefixEnd_3670160 : Nat := 4983230072969 + 3 ^ 40 * 3670160 * 2
def baseEnd_3670160 : Nat := 69798376255757989474861

theorem tailTrace_3670160 : CollatzResearch.WordTrace tailWord_3670160 prefixEnd_3670160 69798376255757989474861 := by
  unfold tailWord_3670160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66930866191822304134971967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89241154922429738846629289 66930866191822304134971967)
  ·
    refine ⟨100396299287733456202457951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66930866191822304134971967 100396299287733456202457951)
    ·
      refine ⟨150594448931600184303686927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100396299287733456202457951 150594448931600184303686927)
      ·
        refine ⟨225891673397400276455530391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150594448931600184303686927 225891673397400276455530391)
        ·
          refine ⟨338837510096100414683295587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225891673397400276455530391 338837510096100414683295587)
          ·
            refine ⟨508256265144150622024943381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338837510096100414683295587 508256265144150622024943381)
            ·
              refine ⟨23824512428632060407419221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 508256265144150622024943381 23824512428632060407419221)
              ·
                refine ⟨69798376255757989474861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23824512428632060407419221 69798376255757989474861)
                ·
                  rfl

theorem cell23_3670160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_3670160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670160 prefixEnd_3670160 := by exact prefixLift 3670160
  have htrace : WordTrace (prefixWord ++ tailWord_3670160) baseStart_3670160 baseEnd_3670160 := by
    simpa [prefixWord, tailWord_3670160, baseEnd_3670160] using wordTrace_append hprefix tailTrace_3670160
  have hstable : (prefixWord ++ tailWord_3670160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670160).length < 2 ^ (prefixWord ++ tailWord_3670160).sum := by decide
  have hdescent : baseEnd_3670160 < baseStart_3670160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670177 : List Nat := [1, 2, 3, 3, 1, 3, 1, 9]
def baseStart_3670177 : Nat := 118140960795 + 3670177 * 2 ^ 59
def prefixEnd_3670177 : Nat := 4983230072969 + 3 ^ 40 * 3670177 * 2
def baseEnd_3670177 : Nat := 69798699558392301826247

theorem tailTrace_3670177 : CollatzResearch.WordTrace tailWord_3670177 prefixEnd_3670177 69798699558392301826247 := by
  unfold tailWord_3670177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133862352424583020173312785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89241568283055346782208523 133862352424583020173312785)
  ·
    refine ⟨100396764318437265129984589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133862352424583020173312785 100396764318437265129984589)
    ·
      refine ⟨37648786619413974423744221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100396764318437265129984589 37648786619413974423744221)
      ·
        refine ⟨14118294982280240408904083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37648786619413974423744221 14118294982280240408904083)
        ·
          refine ⟨21177442473420360613356125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14118294982280240408904083 21177442473420360613356125)
          ·
            refine ⟨7941540927532635230008547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21177442473420360613356125 7941540927532635230008547)
            ·
              refine ⟨11912311391298952845012821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941540927532635230008547 11912311391298952845012821)
              ·
                refine ⟨69798699558392301826247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11912311391298952845012821 69798699558392301826247)
                ·
                  rfl

theorem cell23_3670177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 9].length) (baseStart_3670177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670177 prefixEnd_3670177 := by exact prefixLift 3670177
  have htrace : WordTrace (prefixWord ++ tailWord_3670177) baseStart_3670177 baseEnd_3670177 := by
    simpa [prefixWord, tailWord_3670177, baseEnd_3670177] using wordTrace_append hprefix tailTrace_3670177
  have hstable : (prefixWord ++ tailWord_3670177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670177).length < 2 ^ (prefixWord ++ tailWord_3670177).sum := by decide
  have hdescent : baseEnd_3670177 < baseStart_3670177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670242 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3670242 : Nat := 118140960795 + 3670242 * 2 ^ 59
def prefixEnd_3670242 : Nat := 4983230072969 + 3 ^ 40 * 3670242 * 2
def baseEnd_3670242 : Nat := 1884598264319134394995871

theorem tailTrace_3670242 : CollatzResearch.WordTrace tailWord_3670242 prefixEnd_3670242 1884598264319134394995871 := by
  unfold tailWord_3670242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33466180792336884068607245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89243148779565024182952653 33466180792336884068607245)
  ·
    refine ⟨12549817797126331525727717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33466180792336884068607245 12549817797126331525727717)
    ·
      refine ⟨2353090836961187161073947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12549817797126331525727717 2353090836961187161073947)
      ·
        refine ⟨3529636255441780741610921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353090836961187161073947 3529636255441780741610921)
        ·
          refine ⟨2647227191581335556208191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529636255441780741610921 2647227191581335556208191)
          ·
            refine ⟨3970840787372003334312287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647227191581335556208191 3970840787372003334312287)
            ·
              refine ⟨5956261181058005001468431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970840787372003334312287 5956261181058005001468431)
              ·
                refine ⟨8934391771587007502202647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956261181058005001468431 8934391771587007502202647)
                ·
                  refine ⟨13401587657380511253303971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934391771587007502202647 13401587657380511253303971)
                  ·
                    refine ⟨20102381486070766879955957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13401587657380511253303971 20102381486070766879955957)
                    ·
                      refine ⟨1884598264319134394995871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20102381486070766879955957 1884598264319134394995871)
                      ·
                        rfl

theorem cell23_3670242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3670242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670242 prefixEnd_3670242 := by exact prefixLift 3670242
  have htrace : WordTrace (prefixWord ++ tailWord_3670242) baseStart_3670242 baseEnd_3670242 := by
    simpa [prefixWord, tailWord_3670242, baseEnd_3670242] using wordTrace_append hprefix tailTrace_3670242
  have hstable : (prefixWord ++ tailWord_3670242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670242).length < 2 ^ (prefixWord ++ tailWord_3670242).sum := by decide
  have hdescent : baseEnd_3670242 < baseStart_3670242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670312 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3670312 : Nat := 118140960795 + 3670312 * 2 ^ 59
def prefixEnd_3670312 : Nat := 4983230072969 + 3 ^ 40 * 3670312 * 2
def baseEnd_3670312 : Nat := 1884634207964949121120549

theorem tailTrace_3670312 : CollatzResearch.WordTrace tailWord_3670312 prefixEnd_3670312 1884634207964949121120549 := by
  unfold tailWord_3670312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66933638139546969114738595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89244850852729292152984793 66933638139546969114738595)
  ·
    refine ⟨100400457209320453672107893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66933638139546969114738595 100400457209320453672107893)
    ·
      refine ⟨9412542863373792531760115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100400457209320453672107893 9412542863373792531760115)
      ·
        refine ⟨14118814295060688797640173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412542863373792531760115 14118814295060688797640173)
        ·
          refine ⟨5294555360647758299115065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14118814295060688797640173 5294555360647758299115065)
          ·
            refine ⟨3970916520485818724336299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294555360647758299115065 3970916520485818724336299)
            ·
              refine ⟨5956374780728728086504449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970916520485818724336299 5956374780728728086504449)
              ·
                refine ⟨4467281085546546064878337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956374780728728086504449 4467281085546546064878337)
                ·
                  refine ⟨3350460814159909548658753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4467281085546546064878337 3350460814159909548658753)
                  ·
                    refine ⟨2512845610619932161494065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3350460814159909548658753 2512845610619932161494065)
                    ·
                      refine ⟨1884634207964949121120549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512845610619932161494065 1884634207964949121120549)
                      ·
                        rfl

theorem cell23_3670312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3670312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670312 prefixEnd_3670312 := by exact prefixLift 3670312
  have htrace : WordTrace (prefixWord ++ tailWord_3670312) baseStart_3670312 baseEnd_3670312 := by
    simpa [prefixWord, tailWord_3670312, baseEnd_3670312] using wordTrace_append hprefix tailTrace_3670312
  have hstable : (prefixWord ++ tailWord_3670312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670312).length < 2 ^ (prefixWord ++ tailWord_3670312).sum := by decide
  have hdescent : baseEnd_3670312 < baseStart_3670312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670318 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3670318 : Nat := 118140960795 + 3670318 * 2 ^ 59
def prefixEnd_3670318 : Nat := 4983230072969 + 3 ^ 40 * 3670318 * 2
def baseEnd_3670318 : Nat := 209404143205430677516169

theorem tailTrace_3670318 : CollatzResearch.WordTrace tailWord_3670318 prefixEnd_3670318 209404143205430677516169 := by
  unfold tailWord_3670318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16733436889634025156774451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89244996744714800836130405 16733436889634025156774451)
  ·
    refine ⟨25100155334451037735161677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16733436889634025156774451 25100155334451037735161677)
    ·
      refine ⟨9412558250419139150685629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25100155334451037735161677 9412558250419139150685629)
      ·
        refine ⟨3529709343907177181507111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9412558250419139150685629 3529709343907177181507111)
        ·
          refine ⟨5294564015860765772260667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529709343907177181507111 5294564015860765772260667)
          ·
            refine ⟨7941846023791148658391001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294564015860765772260667 7941846023791148658391001)
            ·
              refine ⟨5956384517843361493793251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941846023791148658391001 5956384517843361493793251)
              ·
                refine ⟨8934576776765042240689877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956384517843361493793251 8934576776765042240689877)
                ·
                  refine ⟨209404143205430677516169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8934576776765042240689877 209404143205430677516169)
                  ·
                    rfl

theorem cell23_3670318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3670318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670318 prefixEnd_3670318 := by exact prefixLift 3670318
  have htrace : WordTrace (prefixWord ++ tailWord_3670318) baseStart_3670318 baseEnd_3670318 := by
    simpa [prefixWord, tailWord_3670318, baseEnd_3670318] using wordTrace_append hprefix tailTrace_3670318
  have hstable : (prefixWord ++ tailWord_3670318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670318).length < 2 ^ (prefixWord ++ tailWord_3670318).sum := by decide
  have hdescent : baseEnd_3670318 < baseStart_3670318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670347 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_3670347 : Nat := 118140960795 + 3670347 * 2 ^ 59
def prefixEnd_3670347 : Nat := 4983230072969 + 3 ^ 40 * 3670347 * 2
def baseEnd_3670347 : Nat := 1884652179787856484182887

theorem tailTrace_3670347 : CollatzResearch.WordTrace tailWord_3670347 prefixEnd_3670347 1884652179787856484182887 := by
  unfold tailWord_3670347
  simp only [CollatzResearch.WordTrace]
  refine ⟨133868552833967139207001295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89245701889311426138000863 133868552833967139207001295)
  ·
    refine ⟨200802829250950708810501943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133868552833967139207001295 200802829250950708810501943)
    ·
      refine ⟨301204243876426063215752915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200802829250950708810501943 301204243876426063215752915)
      ·
        refine ⟨451806365814639094823629373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301204243876426063215752915 451806365814639094823629373)
        ·
          refine ⟨169427387180489660558861015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451806365814639094823629373 169427387180489660558861015)
          ·
            refine ⟨254141080770734490838291523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169427387180489660558861015 254141080770734490838291523)
            ·
              refine ⟨381211621156101736257437285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254141080770734490838291523 381211621156101736257437285)
              ·
                refine ⟨71477178966769075548269491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381211621156101736257437285 71477178966769075548269491)
                ·
                  refine ⟨107215768450153613322404237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71477178966769075548269491 107215768450153613322404237)
                  ·
                    refine ⟨40205913168807604995901589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107215768450153613322404237 40205913168807604995901589)
                    ·
                      refine ⟨1884652179787856484182887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40205913168807604995901589 1884652179787856484182887)
                      ·
                        rfl

theorem cell23_3670347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_3670347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670347 prefixEnd_3670347 := by exact prefixLift 3670347
  have htrace : WordTrace (prefixWord ++ tailWord_3670347) baseStart_3670347 baseEnd_3670347 := by
    simpa [prefixWord, tailWord_3670347, baseEnd_3670347] using wordTrace_append hprefix tailTrace_3670347
  have hstable : (prefixWord ++ tailWord_3670347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670347).length < 2 ^ (prefixWord ++ tailWord_3670347).sum := by decide
  have hdescent : baseEnd_3670347 < baseStart_3670347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670371 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3670371 : Nat := 118140960795 + 3670371 * 2 ^ 59
def prefixEnd_3670371 : Nat := 4983230072969 + 3 ^ 40 * 3670371 * 2
def baseEnd_3670371 : Nat := 1884664503323564390282777

theorem tailTrace_3670371 : CollatzResearch.WordTrace tailWord_3670371 prefixEnd_3670371 1884664503323564390282777 := by
  unfold tailWord_3670371
  simp only [CollatzResearch.WordTrace]
  refine ⟨133869428185880191305874967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89246285457253460870583311 133869428185880191305874967)
  ·
    refine ⟨200804142278820286958812451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133869428185880191305874967 200804142278820286958812451)
    ·
      refine ⟨301206213418230430438218677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200804142278820286958812451 301206213418230430438218677)
      ·
        refine ⟨28238082507959102853583001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301206213418230430438218677 28238082507959102853583001)
        ·
          refine ⟨21178561880969327140187251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28238082507959102853583001 21178561880969327140187251)
          ·
            refine ⟨31767842821453990710280877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21178561880969327140187251 31767842821453990710280877)
            ·
              refine ⟨11912941058045246516355329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31767842821453990710280877 11912941058045246516355329)
              ·
                refine ⟨8934705793533934887266497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11912941058045246516355329 8934705793533934887266497)
                ·
                  refine ⟨6701029345150451165449873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934705793533934887266497 6701029345150451165449873)
                  ·
                    refine ⟨5025772008862838374087405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701029345150451165449873 5025772008862838374087405)
                    ·
                      refine ⟨1884664503323564390282777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5025772008862838374087405 1884664503323564390282777)
                      ·
                        rfl

theorem cell23_3670371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3670371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670371 prefixEnd_3670371 := by exact prefixLift 3670371
  have htrace : WordTrace (prefixWord ++ tailWord_3670371) baseStart_3670371 baseEnd_3670371 := by
    simpa [prefixWord, tailWord_3670371, baseEnd_3670371] using wordTrace_append hprefix tailTrace_3670371
  have hstable : (prefixWord ++ tailWord_3670371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670371).length < 2 ^ (prefixWord ++ tailWord_3670371).sum := by decide
  have hdescent : baseEnd_3670371 < baseStart_3670371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670378 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3670378 : Nat := 118140960795 + 3670378 * 2 ^ 59
def prefixEnd_3670378 : Nat := 4983230072969 + 3 ^ 40 * 3670378 * 2
def baseEnd_3670378 : Nat := 628222699229381954298415

theorem tailTrace_3670378 : CollatzResearch.WordTrace tailWord_3670378 prefixEnd_3670378 628222699229381954298415 := by
  unfold tailWord_3670378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33467420874213707875344947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89246455664569887667586525 33467420874213707875344947)
  ·
    refine ⟨50201131311320561813017421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33467420874213707875344947 50201131311320561813017421)
    ·
      refine ⟨18825424241745210679881533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50201131311320561813017421 18825424241745210679881533)
      ·
        refine ⟨7059534090654454004955575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18825424241745210679881533 7059534090654454004955575)
        ·
          refine ⟨10589301135981681007433363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7059534090654454004955575 10589301135981681007433363)
          ·
            refine ⟨15883951703972521511150045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589301135981681007433363 15883951703972521511150045)
            ·
              refine ⟨5956481888989695566681267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15883951703972521511150045 5956481888989695566681267)
              ·
                refine ⟨8934722833484543350021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956481888989695566681267 8934722833484543350021901)
                ·
                  refine ⟨3350521062556703756258213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8934722833484543350021901 3350521062556703756258213)
                  ·
                    refine ⟨628222699229381954298415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350521062556703756258213 628222699229381954298415)
                    ·
                      rfl

theorem cell23_3670378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3670378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670378 prefixEnd_3670378 := by exact prefixLift 3670378
  have htrace : WordTrace (prefixWord ++ tailWord_3670378) baseStart_3670378 baseEnd_3670378 := by
    simpa [prefixWord, tailWord_3670378, baseEnd_3670378] using wordTrace_append hprefix tailTrace_3670378
  have hstable : (prefixWord ++ tailWord_3670378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670378).length < 2 ^ (prefixWord ++ tailWord_3670378).sum := by decide
  have hdescent : baseEnd_3670378 < baseStart_3670378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670429 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3670429 : Nat := 118140960795 + 3670429 * 2 ^ 59
def prefixEnd_3670429 : Nat := 4983230072969 + 3 ^ 40 * 3670429 * 2
def baseEnd_3670429 : Nat := 628231428400508387785837

theorem tailTrace_3670429 : CollatzResearch.WordTrace tailWord_3670429 prefixEnd_3670429 628231428400508387785837 := by
  unfold tailWord_3670429
  simp only [CollatzResearch.WordTrace]
  refine ⟨133871543619670067211486341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89247695746446711474324227 133871543619670067211486341)
  ·
    refine ⟨25100914428688137602153689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133871543619670067211486341 25100914428688137602153689)
    ·
      refine ⟨18825685821516103201615267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25100914428688137602153689 18825685821516103201615267)
      ·
        refine ⟨28238528732274154802422901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18825685821516103201615267 28238528732274154802422901)
        ·
          refine ⟨2647362068650702012727147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28238528732274154802422901 2647362068650702012727147)
          ·
            refine ⟨3971043102976053019090721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647362068650702012727147 3971043102976053019090721)
            ·
              refine ⟨2978282327232039764318041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971043102976053019090721 2978282327232039764318041)
              ·
                refine ⟨2233711745424029823238531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978282327232039764318041 2233711745424029823238531)
                ·
                  refine ⟨3350567618136044734857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233711745424029823238531 3350567618136044734857797)
                  ·
                    refine ⟨628231428400508387785837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350567618136044734857797 628231428400508387785837)
                    ·
                      rfl

theorem cell23_3670429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3670429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670429 prefixEnd_3670429 := by exact prefixLift 3670429
  have htrace : WordTrace (prefixWord ++ tailWord_3670429) baseStart_3670429 baseEnd_3670429 := by
    simpa [prefixWord, tailWord_3670429, baseEnd_3670429] using wordTrace_append hprefix tailTrace_3670429
  have hstable : (prefixWord ++ tailWord_3670429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670429).length < 2 ^ (prefixWord ++ tailWord_3670429).sum := by decide
  have hdescent : baseEnd_3670429 < baseStart_3670429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670435 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 1, 1, 3]
def baseStart_3670435 : Nat := 118140960795 + 3670435 * 2 ^ 59
def prefixEnd_3670435 : Nat := 4983230072969 + 3 ^ 40 * 3670435 * 2
def baseEnd_3670435 : Nat := 1884697366085452139882483

theorem tailTrace_3670435 : CollatzResearch.WordTrace tailWord_3670435 prefixEnd_3670435 1884697366085452139882483 := by
  unfold tailWord_3670435
  simp only [CollatzResearch.WordTrace]
  refine ⟨133871762457648330236204759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89247841638432220157469839 133871762457648330236204759)
  ·
    refine ⟨200807643686472495354307139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133871762457648330236204759 200807643686472495354307139)
    ·
      refine ⟨301211465529708743031460709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200807643686472495354307139 301211465529708743031460709)
      ·
        refine ⟨56477149786820389318398883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301211465529708743031460709 56477149786820389318398883)
        ·
          refine ⟨84715724680230583977598325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56477149786820389318398883 84715724680230583977598325)
          ·
            refine ⟨7942099188771617247899843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84715724680230583977598325 7942099188771617247899843)
            ·
              refine ⟨11913148783157425871849765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942099188771617247899843 11913148783157425871849765)
              ·
                refine ⟨2233715396842017350971831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11913148783157425871849765 2233715396842017350971831)
                ·
                  refine ⟨3350573095263026026457747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233715396842017350971831 3350573095263026026457747)
                  ·
                    refine ⟨5025859642894539039686621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3350573095263026026457747 5025859642894539039686621)
                    ·
                      refine ⟨1884697366085452139882483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5025859642894539039686621 1884697366085452139882483)
                      ·
                        rfl

theorem cell23_3670435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_3670435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670435 prefixEnd_3670435 := by exact prefixLift 3670435
  have htrace : WordTrace (prefixWord ++ tailWord_3670435) baseStart_3670435 baseEnd_3670435 := by
    simpa [prefixWord, tailWord_3670435, baseEnd_3670435] using wordTrace_append hprefix tailTrace_3670435
  have hstable : (prefixWord ++ tailWord_3670435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670435).length < 2 ^ (prefixWord ++ tailWord_3670435).sum := by decide
  have hdescent : baseEnd_3670435 < baseStart_3670435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670444 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_3670444 : Nat := 118140960795 + 3670444 * 2 ^ 59
def prefixEnd_3670444 : Nat := 4983230072969 + 3 ^ 40 * 3670444 * 2
def baseEnd_3670444 : Nat := 1884701987411342604669941

theorem tailTrace_3670444 : CollatzResearch.WordTrace tailWord_3670444 prefixEnd_3670444 1884701987411342604669941 := by
  unfold tailWord_3670444
  simp only [CollatzResearch.WordTrace]
  refine ⟨66936045357307862386641193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89248060476410483182188257 66936045357307862386641193)
  ·
    refine ⟨50202034017980896789980895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66936045357307862386641193 50202034017980896789980895)
    ·
      refine ⟨75303051026971345184971343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50202034017980896789980895 75303051026971345184971343)
      ·
        refine ⟨112954576540457017777457015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75303051026971345184971343 112954576540457017777457015)
        ·
          refine ⟨169431864810685526666185523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112954576540457017777457015 169431864810685526666185523)
          ·
            refine ⟨254147797216028289999278285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169431864810685526666185523 254147797216028289999278285)
            ·
              refine ⟨95305423956010608749729357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254147797216028289999278285 95305423956010608749729357)
              ·
                refine ⟨35739533983503978281148509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95305423956010608749729357 35739533983503978281148509)
                ·
                  refine ⟨13402325243813991855430691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35739533983503978281148509 13402325243813991855430691)
                  ·
                    refine ⟨20103487865720987783146037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13402325243813991855430691 20103487865720987783146037)
                    ·
                      refine ⟨1884701987411342604669941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20103487865720987783146037 1884701987411342604669941)
                      ·
                        rfl

theorem cell23_3670444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_3670444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670444 prefixEnd_3670444 := by exact prefixLift 3670444
  have htrace : WordTrace (prefixWord ++ tailWord_3670444) baseStart_3670444 baseEnd_3670444 := by
    simpa [prefixWord, tailWord_3670444, baseEnd_3670444] using wordTrace_append hprefix tailTrace_3670444
  have hstable : (prefixWord ++ tailWord_3670444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670444).length < 2 ^ (prefixWord ++ tailWord_3670444).sum := by decide
  have hdescent : baseEnd_3670444 < baseStart_3670444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670471 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3670471 : Nat := 118140960795 + 3670471 * 2 ^ 59
def prefixEnd_3670471 : Nat := 4983230072969 + 3 ^ 40 * 3670471 * 2
def baseEnd_3670471 : Nat := 1884715851389013999032317

theorem tailTrace_3670471 : CollatzResearch.WordTrace tailWord_3670471 prefixEnd_3670471 1884715851389013999032317 := by
  unfold tailWord_3670471
  simp only [CollatzResearch.WordTrace]
  refine ⟨133873075485517908384515267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89248716990345272256343511 133873075485517908384515267)
  ·
    refine ⟨200809613228276862576772901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133873075485517908384515267 200809613228276862576772901)
    ·
      refine ⟨37651802480301911733144919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200809613228276862576772901 37651802480301911733144919)
      ·
        refine ⟨56477703720452867599717379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37651802480301911733144919 56477703720452867599717379)
        ·
          refine ⟨84716555580679301399576069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56477703720452867599717379 84716555580679301399576069)
          ·
            refine ⟨15884354171377369012420513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84716555580679301399576069 15884354171377369012420513)
            ·
              refine ⟨11913265628533026759315385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15884354171377369012420513 11913265628533026759315385)
              ·
                refine ⟨8934949221399770069486539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11913265628533026759315385 8934949221399770069486539)
                ·
                  refine ⟨13402423832099655104229809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934949221399770069486539 13402423832099655104229809)
                  ·
                    refine ⟨10051817874074741328172357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13402423832099655104229809 10051817874074741328172357)
                    ·
                      refine ⟨1884715851389013999032317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10051817874074741328172357 1884715851389013999032317)
                      ·
                        rfl

theorem cell23_3670471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3670471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670471 prefixEnd_3670471 := by exact prefixLift 3670471
  have htrace : WordTrace (prefixWord ++ tailWord_3670471) baseStart_3670471 baseEnd_3670471 := by
    simpa [prefixWord, tailWord_3670471, baseEnd_3670471] using wordTrace_append hprefix tailTrace_3670471
  have hstable : (prefixWord ++ tailWord_3670471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670471).length < 2 ^ (prefixWord ++ tailWord_3670471).sum := by decide
  have hdescent : baseEnd_3670471 < baseStart_3670471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670485 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3670485 : Nat := 118140960795 + 3670485 * 2 ^ 59
def prefixEnd_3670485 : Nat := 4983230072969 + 3 ^ 40 * 3670485 * 2
def baseEnd_3670485 : Nat := 628241013372725648085751

theorem tailTrace_3670485 : CollatzResearch.WordTrace tailWord_3670485 prefixEnd_3670485 628241013372725648085751 := by
  unfold tailWord_3670485
  simp only [CollatzResearch.WordTrace]
  refine ⟨133873586107467188775524909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89249057404978125850349939 133873586107467188775524909)
  ·
    refine ⟨50202594790300195790821841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133873586107467188775524909 50202594790300195790821841)
    ·
      refine ⟨37651946092725146843116381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50202594790300195790821841 37651946092725146843116381)
      ·
        refine ⟨14119479784771930066168643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37651946092725146843116381 14119479784771930066168643)
        ·
          refine ⟨21179219677157895099252965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14119479784771930066168643 21179219677157895099252965)
          ·
            refine ⟨3971103689467105331109931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21179219677157895099252965 3971103689467105331109931)
            ·
              refine ⟨5956655534200657996664897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971103689467105331109931 5956655534200657996664897)
              ·
                refine ⟨4467491650650493497498673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956655534200657996664897 4467491650650493497498673)
                ·
                  refine ⟨3350618737987870123124005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4467491650650493497498673 3350618737987870123124005)
                  ·
                    refine ⟨628241013372725648085751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350618737987870123124005 628241013372725648085751)
                    ·
                      rfl

theorem cell23_3670485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3670485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670485 prefixEnd_3670485 := by exact prefixLift 3670485
  have htrace : WordTrace (prefixWord ++ tailWord_3670485) baseStart_3670485 baseEnd_3670485 := by
    simpa [prefixWord, tailWord_3670485, baseEnd_3670485] using wordTrace_append hprefix tailTrace_3670485
  have hstable : (prefixWord ++ tailWord_3670485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670485).length < 2 ^ (prefixWord ++ tailWord_3670485).sum := by decide
  have hdescent : baseEnd_3670485 < baseStart_3670485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670561 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3670561 : Nat := 118140960795 + 3670561 * 2 ^ 59
def prefixEnd_3670561 : Nat := 4983230072969 + 3 ^ 40 * 3670561 * 2
def baseEnd_3670561 : Nat := 1884762064647918646906903

theorem tailTrace_3670561 : CollatzResearch.WordTrace tailWord_3670561 prefixEnd_3670561 1884762064647918646906903 := by
  unfold tailWord_3670561
  simp only [CollatzResearch.WordTrace]
  refine ⟨133876358055191853755291537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89250905370127902503527691 133876358055191853755291537)
  ·
    refine ⟨100407268541393890316468653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133876358055191853755291537 100407268541393890316468653)
    ·
      refine ⟨37652725703022708868675745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100407268541393890316468653 37652725703022708868675745)
      ·
        refine ⟨28239544277267031651506809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37652725703022708868675745 28239544277267031651506809)
        ·
          refine ⟨21179658207950273738630107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28239544277267031651506809 21179658207950273738630107)
          ·
            refine ⟨31769487311925410607945161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21179658207950273738630107 31769487311925410607945161)
            ·
              refine ⟨23827115483944057955958871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31769487311925410607945161 23827115483944057955958871)
              ·
                refine ⟨35740673225916086933938307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23827115483944057955958871 35740673225916086933938307)
                ·
                  refine ⟨53611009838874130400907461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35740673225916086933938307 53611009838874130400907461)
                  ·
                    refine ⟨10052064344788899450170149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53611009838874130400907461 10052064344788899450170149)
                    ·
                      refine ⟨1884762064647918646906903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10052064344788899450170149 1884762064647918646906903)
                      ·
                        rfl

theorem cell23_3670561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3670561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670561 prefixEnd_3670561 := by exact prefixLift 3670561
  have htrace : WordTrace (prefixWord ++ tailWord_3670561) baseStart_3670561 baseEnd_3670561 := by
    simpa [prefixWord, tailWord_3670561, baseEnd_3670561] using wordTrace_append hprefix tailTrace_3670561
  have hstable : (prefixWord ++ tailWord_3670561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670561).length < 2 ^ (prefixWord ++ tailWord_3670561).sum := by decide
  have hdescent : baseEnd_3670561 < baseStart_3670561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670568 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3670568 : Nat := 118140960795 + 3670568 * 2 ^ 59
def prefixEnd_3670568 : Nat := 4983230072969 + 3 ^ 40 * 3670568 * 2
def baseEnd_3670568 : Nat := 1884765659012500119519371

theorem tailTrace_3670568 : CollatzResearch.WordTrace tailWord_3670568 prefixEnd_3670568 1884765659012500119519371 := by
  unfold tailWord_3670568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66938306683083246975398179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89251075577444329300530905 66938306683083246975398179)
  ·
    refine ⟨100407460024624870463097269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66938306683083246975398179 100407460024624870463097269)
    ·
      refine ⟨9413199377308581605915369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100407460024624870463097269 9413199377308581605915369)
      ·
        refine ⟨7059899532981436204436527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9413199377308581605915369 7059899532981436204436527)
        ·
          refine ⟨10589849299472154306654791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7059899532981436204436527 10589849299472154306654791)
          ·
            refine ⟨15884773949208231459982187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589849299472154306654791 15884773949208231459982187)
            ·
              refine ⟨23827160923812347189973281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884773949208231459982187 23827160923812347189973281)
              ·
                refine ⟨17870370692859260392479961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23827160923812347189973281 17870370692859260392479961)
                ·
                  refine ⟨13402778019644445294359971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17870370692859260392479961 13402778019644445294359971)
                  ·
                    refine ⟨20104167029466667941539957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13402778019644445294359971 20104167029466667941539957)
                    ·
                      refine ⟨1884765659012500119519371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20104167029466667941539957 1884765659012500119519371)
                      ·
                        rfl

theorem cell23_3670568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3670568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670568 prefixEnd_3670568 := by exact prefixLift 3670568
  have htrace : WordTrace (prefixWord ++ tailWord_3670568) baseStart_3670568 baseEnd_3670568 := by
    simpa [prefixWord, tailWord_3670568, baseEnd_3670568] using wordTrace_append hprefix tailTrace_3670568
  have hstable : (prefixWord ++ tailWord_3670568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670568).length < 2 ^ (prefixWord ++ tailWord_3670568).sum := by decide
  have hdescent : baseEnd_3670568 < baseStart_3670568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670582 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_3670582 : Nat := 118140960795 + 3670582 * 2 ^ 59
def prefixEnd_3670582 : Nat := 4983230072969 + 3 ^ 40 * 3670582 * 2
def baseEnd_3670582 : Nat := 1884772847741663064744307

theorem tailTrace_3670582 : CollatzResearch.WordTrace tailWord_3670582 prefixEnd_3670582 1884772847741663064744307 := by
  unfold tailWord_3670582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367320249257235896362875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89251415992077182894537333 8367320249257235896362875)
  ·
    refine ⟨12550980373885853844544313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8367320249257235896362875 12550980373885853844544313)
    ·
      refine ⟨9413235280414390383408235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12550980373885853844544313 9413235280414390383408235)
      ·
        refine ⟨14119852920621585575112353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413235280414390383408235 14119852920621585575112353)
        ·
          refine ⟨10589889690466189181334265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119852920621585575112353 10589889690466189181334265)
          ·
            refine ⟨7942417267849641886000699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10589889690466189181334265 7942417267849641886000699)
            ·
              refine ⟨11913625901774462829001049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942417267849641886000699 11913625901774462829001049)
              ·
                refine ⟨8935219426330847121750787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11913625901774462829001049 8935219426330847121750787)
                ·
                  refine ⟨13402829139496270682626181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8935219426330847121750787 13402829139496270682626181)
                  ·
                    refine ⟨2513030463655550752992409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13402829139496270682626181 2513030463655550752992409)
                    ·
                      refine ⟨1884772847741663064744307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513030463655550752992409 1884772847741663064744307)
                      ·
                        rfl

theorem cell23_3670582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_3670582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670582 prefixEnd_3670582 := by exact prefixLift 3670582
  have htrace : WordTrace (prefixWord ++ tailWord_3670582) baseStart_3670582 baseEnd_3670582 := by
    simpa [prefixWord, tailWord_3670582, baseEnd_3670582] using wordTrace_append hprefix tailTrace_3670582
  have hstable : (prefixWord ++ tailWord_3670582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670582).length < 2 ^ (prefixWord ++ tailWord_3670582).sum := by decide
  have hdescent : baseEnd_3670582 < baseStart_3670582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670681 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3670681 : Nat := 118140960795 + 3670681 * 2 ^ 59
def prefixEnd_3670681 : Nat := 4983230072969 + 3 ^ 40 * 3670681 * 2
def baseEnd_3670681 : Nat := 1884823682326458177406351

theorem tailTrace_3670681 : CollatzResearch.WordTrace tailWord_3670681 prefixEnd_3670681 1884823682326458177406351 := by
  unfold tailWord_3670681
  simp only [CollatzResearch.WordTrace]
  refine ⟨133880734814757114249659897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89253823209838076166439931 133880734814757114249659897)
  ·
    refine ⟨100410551111067835687244923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133880734814757114249659897 100410551111067835687244923)
    ·
      refine ⟨150615826666601753530867385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100410551111067835687244923 150615826666601753530867385)
      ·
        refine ⟨112961869999951315148150539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150615826666601753530867385 112961869999951315148150539)
        ·
          refine ⟨169442804999926972722225809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112961869999951315148150539 169442804999926972722225809)
          ·
            refine ⟨127082103749945229541669357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169442804999926972722225809 127082103749945229541669357)
            ·
              refine ⟨47655788906229461078126009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127082103749945229541669357 47655788906229461078126009)
              ·
                refine ⟨35741841679672095808594507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47655788906229461078126009 35741841679672095808594507)
                ·
                  refine ⟨53612762519508143712891761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35741841679672095808594507 53612762519508143712891761)
                  ·
                    refine ⟨40209571889631107784668821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53612762519508143712891761 40209571889631107784668821)
                    ·
                      refine ⟨1884823682326458177406351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40209571889631107784668821 1884823682326458177406351)
                      ·
                        rfl

theorem cell23_3670681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3670681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670681 prefixEnd_3670681 := by exact prefixLift 3670681
  have htrace : WordTrace (prefixWord ++ tailWord_3670681) baseStart_3670681 baseEnd_3670681 := by
    simpa [prefixWord, tailWord_3670681, baseEnd_3670681] using wordTrace_append hprefix tailTrace_3670681
  have hstable : (prefixWord ++ tailWord_3670681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670681).length < 2 ^ (prefixWord ++ tailWord_3670681).sum := by decide
  have hdescent : baseEnd_3670681 < baseStart_3670681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670755 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 6]
def baseStart_3670755 : Nat := 118140960795 + 3670755 * 2 ^ 59
def prefixEnd_3670755 : Nat := 4983230072969 + 3 ^ 40 * 3670755 * 2
def baseEnd_3670755 : Nat := 628287226631630295960337

theorem tailTrace_3670755 : CollatzResearch.WordTrace tailWord_3670755 prefixEnd_3670755 628287226631630295960337 := by
  unfold tailWord_3670755
  simp only [CollatzResearch.WordTrace]
  refine ⟨133883433816489024887853719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89255622544326016591902479 133883433816489024887853719)
  ·
    refine ⟨200825150724733537331780579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133883433816489024887853719 200825150724733537331780579)
    ·
      refine ⟨301237726087100305997670869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200825150724733537331780579 301237726087100305997670869)
      ·
        refine ⟨7060259205166413421820411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 301237726087100305997670869 7060259205166413421820411)
        ·
          refine ⟨10590388807749620132730617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060259205166413421820411 10590388807749620132730617)
          ·
            refine ⟨7942791605812215099547963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10590388807749620132730617 7942791605812215099547963)
            ·
              refine ⟨11914187408718322649321945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942791605812215099547963 11914187408718322649321945)
              ·
                refine ⟨8935640556538741986991459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11914187408718322649321945 8935640556538741986991459)
                ·
                  refine ⟨13403460834808112980487189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8935640556538741986991459 13403460834808112980487189)
                  ·
                    refine ⟨628287226631630295960337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13403460834808112980487189 628287226631630295960337)
                    ·
                      rfl

theorem cell23_3670755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].length) (baseStart_3670755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670755 prefixEnd_3670755 := by exact prefixLift 3670755
  have htrace : WordTrace (prefixWord ++ tailWord_3670755) baseStart_3670755 baseEnd_3670755 := by
    simpa [prefixWord, tailWord_3670755, baseEnd_3670755] using wordTrace_append hprefix tailTrace_3670755
  have hstable : (prefixWord ++ tailWord_3670755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670755).length < 2 ^ (prefixWord ++ tailWord_3670755).sum := by decide
  have hdescent : baseEnd_3670755 < baseStart_3670755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670782 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3670782 : Nat := 118140960795 + 3670782 * 2 ^ 59
def prefixEnd_3670782 : Nat := 4983230072969 + 3 ^ 40 * 3670782 * 2
def baseEnd_3670782 : Nat := 1884875543872562282243387

theorem tailTrace_3670782 : CollatzResearch.WordTrace tailWord_3670782 prefixEnd_3670782 1884875543872562282243387 := by
  unfold tailWord_3670782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735552323423901062385825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89256279058260805666057733 16735552323423901062385825)
  ·
    refine ⟨12551664242567925796789369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16735552323423901062385825 12551664242567925796789369)
    ·
      refine ⟨9413748181925944347592027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12551664242567925796789369 9413748181925944347592027)
      ·
        refine ⟨14120622272888916521388041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413748181925944347592027 14120622272888916521388041)
        ·
          refine ⟨10590466704666687391041031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14120622272888916521388041 10590466704666687391041031)
          ·
            refine ⟨15885700057000031086561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590466704666687391041031 15885700057000031086561547)
            ·
              refine ⟨23828550085500046629842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15885700057000031086561547 23828550085500046629842321)
              ·
                refine ⟨17871412564125034972381741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23828550085500046629842321 17871412564125034972381741)
                ·
                  refine ⟨6701779711546888114643153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17871412564125034972381741 6701779711546888114643153)
                  ·
                    refine ⟨5026334783660166085982365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701779711546888114643153 5026334783660166085982365)
                    ·
                      refine ⟨1884875543872562282243387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026334783660166085982365 1884875543872562282243387)
                      ·
                        rfl

theorem cell23_3670782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3670782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670782 prefixEnd_3670782 := by exact prefixLift 3670782
  have htrace : WordTrace (prefixWord ++ tailWord_3670782) baseStart_3670782 baseEnd_3670782 := by
    simpa [prefixWord, tailWord_3670782, baseEnd_3670782] using wordTrace_append hprefix tailTrace_3670782
  have hstable : (prefixWord ++ tailWord_3670782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670782).length < 2 ^ (prefixWord ++ tailWord_3670782).sum := by decide
  have hdescent : baseEnd_3670782 < baseStart_3670782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670795 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 3]
def baseStart_3670795 : Nat := 118140960795 + 3670795 * 2 ^ 59
def prefixEnd_3670795 : Nat := 4983230072969 + 3 ^ 40 * 3670795 * 2
def baseEnd_3670795 : Nat := 1884882219121070731380827

theorem tailTrace_3670795 : CollatzResearch.WordTrace tailWord_3670795 prefixEnd_3670795 1884882219121070731380827 := by
  unfold tailWord_3670795
  simp only [CollatzResearch.WordTrace]
  refine ⟨133884892736344111719309839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89256595157562741146206559 133884892736344111719309839)
  ·
    refine ⟨200827339104516167578964759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133884892736344111719309839 200827339104516167578964759)
    ·
      refine ⟨301241008656774251368447139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200827339104516167578964759 301241008656774251368447139)
      ·
        refine ⟨451861512985161377052670709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301241008656774251368447139 451861512985161377052670709)
        ·
          refine ⟨42362016842358879098687879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 451861512985161377052670709 42362016842358879098687879)
          ·
            refine ⟨63543025263538318648031819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42362016842358879098687879 63543025263538318648031819)
            ·
              refine ⟨95314537895307477972047729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63543025263538318648031819 95314537895307477972047729)
              ·
                refine ⟨71485903421480608479035797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95314537895307477972047729 71485903421480608479035797)
                ·
                  refine ⟨3350901722881903522454803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71485903421480608479035797 3350901722881903522454803)
                  ·
                    refine ⟨5026352584322855283682205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3350901722881903522454803 5026352584322855283682205)
                    ·
                      refine ⟨1884882219121070731380827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026352584322855283682205 1884882219121070731380827)
                      ·
                        rfl

theorem cell23_3670795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 3].length) (baseStart_3670795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670795 prefixEnd_3670795 := by exact prefixLift 3670795
  have htrace : WordTrace (prefixWord ++ tailWord_3670795) baseStart_3670795 baseEnd_3670795 := by
    simpa [prefixWord, tailWord_3670795, baseEnd_3670795] using wordTrace_append hprefix tailTrace_3670795
  have hstable : (prefixWord ++ tailWord_3670795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670795).length < 2 ^ (prefixWord ++ tailWord_3670795).sum := by decide
  have hdescent : baseEnd_3670795 < baseStart_3670795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670798 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3670798 : Nat := 118140960795 + 3670798 * 2 ^ 59
def prefixEnd_3670798 : Nat := 4983230072969 + 3 ^ 40 * 3670798 * 2
def baseEnd_3670798 : Nat := 628294586521011406547771

theorem tailTrace_3670798 : CollatzResearch.WordTrace tailWord_3670798 prefixEnd_3670798 628294586521011406547771 := by
  unfold tailWord_3670798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735625269416655403958631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89256668103555495487779365 16735625269416655403958631)
  ·
    refine ⟨25103437904124983105937947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16735625269416655403958631 25103437904124983105937947)
    ·
      refine ⟨37655156856187474658906921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25103437904124983105937947 37655156856187474658906921)
      ·
        refine ⟨28241367642140605994180191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37655156856187474658906921 28241367642140605994180191)
        ·
          refine ⟨42362051463210908991270287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28241367642140605994180191 42362051463210908991270287)
          ·
            refine ⟨63543077194816363486905431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42362051463210908991270287 63543077194816363486905431)
            ·
              refine ⟨95314615792224545230358147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63543077194816363486905431 95314615792224545230358147)
              ·
                refine ⟨142971923688336817845537221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95314615792224545230358147 142971923688336817845537221)
                ·
                  refine ⟨26807235691563153346038229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142971923688336817845537221 26807235691563153346038229)
                  ·
                    refine ⟨628294586521011406547771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26807235691563153346038229 628294586521011406547771)
                    ·
                      rfl

theorem cell23_3670798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3670798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670798 prefixEnd_3670798 := by exact prefixLift 3670798
  have htrace : WordTrace (prefixWord ++ tailWord_3670798) baseStart_3670798 baseEnd_3670798 := by
    simpa [prefixWord, tailWord_3670798, baseEnd_3670798] using wordTrace_append hprefix tailTrace_3670798
  have hstable : (prefixWord ++ tailWord_3670798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670798).length < 2 ^ (prefixWord ++ tailWord_3670798).sum := by decide
  have hdescent : baseEnd_3670798 < baseStart_3670798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670808 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3670808 : Nat := 118140960795 + 3670808 * 2 ^ 59
def prefixEnd_3670808 : Nat := 4983230072969 + 3 ^ 40 * 3670808 * 2
def baseEnd_3670808 : Nat := 1884888894369579180518267

theorem tailTrace_3670808 : CollatzResearch.WordTrace tailWord_3670808 prefixEnd_3670808 1884888894369579180518267 := by
  unfold tailWord_3670808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66942683442648507469766539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89256911256864676626355385 66942683442648507469766539)
  ·
    refine ⟨100414025163972761204649809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66942683442648507469766539 100414025163972761204649809)
    ·
      refine ⟨75310518872979570903487357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100414025163972761204649809 75310518872979570903487357)
      ·
        refine ⟨28241444577367339088807759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75310518872979570903487357 28241444577367339088807759)
        ·
          refine ⟨42362166866051008633211639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28241444577367339088807759 42362166866051008633211639)
          ·
            refine ⟨63543250299076512949817459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42362166866051008633211639 63543250299076512949817459)
            ·
              refine ⟨95314875448614769424726189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63543250299076512949817459 95314875448614769424726189)
              ·
                refine ⟨35743078293230538534272321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95314875448614769424726189 35743078293230538534272321)
                ·
                  refine ⟨26807308719922903900704241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35743078293230538534272321 26807308719922903900704241)
                  ·
                    refine ⟨20105481539942177925528181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26807308719922903900704241 20105481539942177925528181)
                    ·
                      refine ⟨1884888894369579180518267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20105481539942177925528181 1884888894369579180518267)
                      ·
                        rfl

theorem cell23_3670808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3670808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670808 prefixEnd_3670808 := by exact prefixLift 3670808
  have htrace : WordTrace (prefixWord ++ tailWord_3670808) baseStart_3670808 baseEnd_3670808 := by
    simpa [prefixWord, tailWord_3670808, baseEnd_3670808] using wordTrace_append hprefix tailTrace_3670808
  have hstable : (prefixWord ++ tailWord_3670808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670808).length < 2 ^ (prefixWord ++ tailWord_3670808).sum := by decide
  have hdescent : baseEnd_3670808 < baseStart_3670808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670813 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3670813 : Nat := 118140960795 + 3670813 * 2 ^ 59
def prefixEnd_3670813 : Nat := 4983230072969 + 3 ^ 40 * 3670813 * 2
def baseEnd_3670813 : Nat := 1884891461772851660955745

theorem tailTrace_3670813 : CollatzResearch.WordTrace tailWord_3670813 prefixEnd_3670813 1884891461772851660955745 := by
  unfold tailWord_3670813
  simp only [CollatzResearch.WordTrace]
  refine ⟨133885549250278900793465093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89257032833519267195643395 133885549250278900793465093)
  ·
    refine ⟨25103540484427293898774705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133885549250278900793465093 25103540484427293898774705)
    ·
      refine ⟨18827655363320470424081029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25103540484427293898774705 18827655363320470424081029)
      ·
        refine ⟨3530185380622588204515193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18827655363320470424081029 3530185380622588204515193)
        ·
          refine ⟨2647639035466941153386395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530185380622588204515193 2647639035466941153386395)
          ·
            refine ⟨3971458553200411730079593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647639035466941153386395 3971458553200411730079593)
            ·
              refine ⟨2978593914900308797559695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971458553200411730079593 2978593914900308797559695)
              ·
                refine ⟨4467890872350463196339543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978593914900308797559695 4467890872350463196339543)
                ·
                  refine ⟨6701836308525694794509315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467890872350463196339543 6701836308525694794509315)
                  ·
                    refine ⟨10052754462788542191763973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701836308525694794509315 10052754462788542191763973)
                    ·
                      refine ⟨1884891461772851660955745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10052754462788542191763973 1884891461772851660955745)
                      ·
                        rfl

theorem cell23_3670813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3670813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670813 prefixEnd_3670813 := by exact prefixLift 3670813
  have htrace : WordTrace (prefixWord ++ tailWord_3670813) baseStart_3670813 baseEnd_3670813 := by
    simpa [prefixWord, tailWord_3670813, baseEnd_3670813] using wordTrace_append hprefix tailTrace_3670813
  have hstable : (prefixWord ++ tailWord_3670813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670813).length < 2 ^ (prefixWord ++ tailWord_3670813).sum := by decide
  have hdescent : baseEnd_3670813 < baseStart_3670813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670828 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_3670828 : Nat := 118140960795 + 3670828 * 2 ^ 59
def prefixEnd_3670828 : Nat := 4983230072969 + 3 ^ 40 * 3670828 * 2
def baseEnd_3670828 : Nat := 628299721327556367422725

theorem tailTrace_3670828 : CollatzResearch.WordTrace tailWord_3670828 prefixEnd_3670828 628299721327556367422725 := by
  unfold tailWord_3670828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66943048172612279177630569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89257397563483038903507425 66943048172612279177630569)
  ·
    refine ⟨50207286129459209383222927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66943048172612279177630569 50207286129459209383222927)
    ·
      refine ⟨75310929194188814074834391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50207286129459209383222927 75310929194188814074834391)
      ·
        refine ⟨112966393791283221112251587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75310929194188814074834391 112966393791283221112251587)
        ·
          refine ⟨169449590686924831668377381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112966393791283221112251587 169449590686924831668377381)
          ·
            refine ⟨31771798253798405937820759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169449590686924831668377381 31771798253798405937820759)
            ·
              refine ⟨47657697380697608906731139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31771798253798405937820759 47657697380697608906731139)
              ·
                refine ⟨71486546071046413360096709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47657697380697608906731139 71486546071046413360096709)
                ·
                  refine ⟨13403727388321202505018133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71486546071046413360096709 13403727388321202505018133)
                  ·
                    refine ⟨628299721327556367422725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13403727388321202505018133 628299721327556367422725)
                    ·
                      rfl

theorem cell23_3670828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_3670828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670828 prefixEnd_3670828 := by exact prefixLift 3670828
  have htrace : WordTrace (prefixWord ++ tailWord_3670828) baseStart_3670828 baseEnd_3670828 := by
    simpa [prefixWord, tailWord_3670828, baseEnd_3670828] using wordTrace_append hprefix tailTrace_3670828
  have hstable : (prefixWord ++ tailWord_3670828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670828).length < 2 ^ (prefixWord ++ tailWord_3670828).sum := by decide
  have hdescent : baseEnd_3670828 < baseStart_3670828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670846 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3670846 : Nat := 118140960795 + 3670846 * 2 ^ 59
def prefixEnd_3670846 : Nat := 4983230072969 + 3 ^ 40 * 3670846 * 2
def baseEnd_3670846 : Nat := 1884908406634450031843093

theorem tailTrace_3670846 : CollatzResearch.WordTrace tailWord_3670846 prefixEnd_3670846 1884908406634450031843093 := by
  unfold tailWord_3670846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735844107394918428677049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89257835239439564952944261 16735844107394918428677049)
  ·
    refine ⟨12551883080546188821507787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16735844107394918428677049 12551883080546188821507787)
    ·
      refine ⟨18827824620819283232261681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12551883080546188821507787 18827824620819283232261681)
      ·
        refine ⟨14120868465614462424196261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18827824620819283232261681 14120868465614462424196261)
        ·
          refine ⟨2647662837302711704536799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14120868465614462424196261 2647662837302711704536799)
          ·
            refine ⟨3971494255954067556805199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647662837302711704536799 3971494255954067556805199)
            ·
              refine ⟨5957241383931101335207799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971494255954067556805199 5957241383931101335207799)
              ·
                refine ⟨8935862075896652002811699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957241383931101335207799 8935862075896652002811699)
                ·
                  refine ⟨13403793113844978004217549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8935862075896652002811699 13403793113844978004217549)
                  ·
                    refine ⟨5026422417691866751581581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13403793113844978004217549 5026422417691866751581581)
                    ·
                      refine ⟨1884908406634450031843093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026422417691866751581581 1884908406634450031843093)
                      ·
                        rfl

theorem cell23_3670846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3670846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670846 prefixEnd_3670846 := by exact prefixLift 3670846
  have htrace : WordTrace (prefixWord ++ tailWord_3670846) baseStart_3670846 baseEnd_3670846 := by
    simpa [prefixWord, tailWord_3670846, baseEnd_3670846] using wordTrace_append hprefix tailTrace_3670846
  have hstable : (prefixWord ++ tailWord_3670846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670846).length < 2 ^ (prefixWord ++ tailWord_3670846).sum := by decide
  have hdescent : baseEnd_3670846 < baseStart_3670846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670858 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_3670858 : Nat := 118140960795 + 3670858 * 2 ^ 59
def prefixEnd_3670858 : Nat := 4983230072969 + 3 ^ 40 * 3670858 * 2
def baseEnd_3670858 : Nat := 209434952044700442765893

theorem tailTrace_3670858 : CollatzResearch.WordTrace tailWord_3670858 prefixEnd_3670858 209434952044700442765893 := by
  unfold tailWord_3670858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33471797633778968369713307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89258127023410582319235485 33471797633778968369713307)
  ·
    refine ⟨50207696450668452554569961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33471797633778968369713307 50207696450668452554569961)
    ·
      refine ⟨37655772338001339415927471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50207696450668452554569961 37655772338001339415927471)
      ·
        refine ⟨56483658507002009123891207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37655772338001339415927471 56483658507002009123891207)
        ·
          refine ⟨84725487760503013685836811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56483658507002009123891207 84725487760503013685836811)
          ·
            refine ⟨127088231640754520528755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84725487760503013685836811 127088231640754520528755217)
            ·
              refine ⟨95316173730565890396566413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127088231640754520528755217 95316173730565890396566413)
              ·
                refine ⟨35743565148962208898712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95316173730565890396566413 35743565148962208898712405)
                ·
                  refine ⟨209434952044700442765893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35743565148962208898712405 209434952044700442765893)
                  ·
                    rfl

theorem cell23_3670858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_3670858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670858 prefixEnd_3670858 := by exact prefixLift 3670858
  have htrace : WordTrace (prefixWord ++ tailWord_3670858) baseStart_3670858 baseEnd_3670858 := by
    simpa [prefixWord, tailWord_3670858, baseEnd_3670858] using wordTrace_append hprefix tailTrace_3670858
  have hstable : (prefixWord ++ tailWord_3670858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670858).length < 2 ^ (prefixWord ++ tailWord_3670858).sum := by decide
  have hdescent : baseEnd_3670858 < baseStart_3670858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670885 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3670885 : Nat := 118140960795 + 3670885 * 2 ^ 59
def prefixEnd_3670885 : Nat := 4983230072969 + 3 ^ 40 * 3670885 * 2
def baseEnd_3670885 : Nat := 1884928432379975379255413

theorem tailTrace_3670885 : CollatzResearch.WordTrace tailWord_3670885 prefixEnd_3670885 1884928432379975379255413 := by
  unfold tailWord_3670885
  simp only [CollatzResearch.WordTrace]
  refine ⟨133888175306018057090086109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89258783537345371393390739 133888175306018057090086109)
  ·
    refine ⟨50208065739756771408782291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133888175306018057090086109 50208065739756771408782291)
    ·
      refine ⟨75312098609635157113173437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50208065739756771408782291 75312098609635157113173437)
      ·
        refine ⟨28242036978613183917440039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75312098609635157113173437 28242036978613183917440039)
        ·
          refine ⟨42363055467919775876160059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28242036978613183917440039 42363055467919775876160059)
          ·
            refine ⟨63544583201879663814240089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42363055467919775876160059 63544583201879663814240089)
            ·
              refine ⟨47658437401409747860680067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63544583201879663814240089 47658437401409747860680067)
              ·
                refine ⟨71487656102114621791020101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47658437401409747860680067 71487656102114621791020101)
                ·
                  refine ⟨13403935519146491585816269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71487656102114621791020101 13403935519146491585816269)
                  ·
                    refine ⟨5026475819679934344681101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13403935519146491585816269 5026475819679934344681101)
                    ·
                      refine ⟨1884928432379975379255413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026475819679934344681101 1884928432379975379255413)
                      ·
                        rfl

theorem cell23_3670885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3670885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670885 prefixEnd_3670885 := by exact prefixLift 3670885
  have htrace : WordTrace (prefixWord ++ tailWord_3670885) baseStart_3670885 baseEnd_3670885 := by
    simpa [prefixWord, tailWord_3670885, baseEnd_3670885] using wordTrace_append hprefix tailTrace_3670885
  have hstable : (prefixWord ++ tailWord_3670885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670885).length < 2 ^ (prefixWord ++ tailWord_3670885).sum := by decide
  have hdescent : baseEnd_3670885 < baseStart_3670885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670922 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_3670922 : Nat := 118140960795 + 3670922 * 2 ^ 59
def prefixEnd_3670922 : Nat := 4983230072969 + 3 ^ 40 * 3670922 * 2
def baseEnd_3670922 : Nat := 628315810388063911497581

theorem tailTrace_3670922 : CollatzResearch.WordTrace tailWord_3670922 prefixEnd_3670922 628315810388063911497581 := by
  unfold tailWord_3670922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33472381201721003102295755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89259683204589341606122013 33472381201721003102295755)
  ·
    refine ⟨50208571802581504653443633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33472381201721003102295755 50208571802581504653443633)
    ·
      refine ⟨37656428851936128490082725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50208571802581504653443633 37656428851936128490082725)
      ·
        refine ⟨7060580409738024091890511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37656428851936128490082725 7060580409738024091890511)
        ·
          refine ⟨10590870614607036137835767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060580409738024091890511 10590870614607036137835767)
          ·
            refine ⟨15886305921910554206753651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590870614607036137835767 15886305921910554206753651)
            ·
              refine ⟨23829458882865831310130477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15886305921910554206753651 23829458882865831310130477)
              ·
                refine ⟨8936047081074686741298929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23829458882865831310130477 8936047081074686741298929)
                ·
                  refine ⟨6702035310806015055974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8936047081074686741298929 6702035310806015055974197)
                  ·
                    refine ⟨628315810388063911497581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6702035310806015055974197 628315810388063911497581)
                    ·
                      rfl

theorem cell23_3670922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_3670922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670922 prefixEnd_3670922 := by exact prefixLift 3670922
  have htrace : WordTrace (prefixWord ++ tailWord_3670922) baseStart_3670922 baseEnd_3670922 := by
    simpa [prefixWord, tailWord_3670922, baseEnd_3670922] using wordTrace_append hprefix tailTrace_3670922
  have hstable : (prefixWord ++ tailWord_3670922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670922).length < 2 ^ (prefixWord ++ tailWord_3670922).sum := by decide
  have hdescent : baseEnd_3670922 < baseStart_3670922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670975 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_3670975 : Nat := 118140960795 + 3670975 * 2 ^ 59
def prefixEnd_3670975 : Nat := 4983230072969 + 3 ^ 40 * 3670975 * 2
def baseEnd_3670975 : Nat := 1884974645638880027129999

theorem tailTrace_3670975 : CollatzResearch.WordTrace tailWord_3670975 prefixEnd_3670975 1884974645638880027129999 := by
  unfold tailWord_3670975
  simp only [CollatzResearch.WordTrace]
  refine ⟨133891457875692002460862379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89260971917128001640574919 133891457875692002460862379)
  ·
    refine ⟨200837186813538003691293569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133891457875692002460862379 200837186813538003691293569)
    ·
      refine ⟨150627890110153502768470177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200837186813538003691293569 150627890110153502768470177)
      ·
        refine ⟨112970917582615127076352633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150627890110153502768470177 112970917582615127076352633)
        ·
          refine ⟨84728188186961345307264475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112970917582615127076352633 84728188186961345307264475)
          ·
            refine ⟨127092282280442017960896713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84728188186961345307264475 127092282280442017960896713)
            ·
              refine ⟨95319211710331513470672535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127092282280442017960896713 95319211710331513470672535)
              ·
                refine ⟨142978817565497270206008803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95319211710331513470672535 142978817565497270206008803)
                ·
                  refine ⟨214468226348245905309013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142978817565497270206008803 214468226348245905309013205)
                  ·
                    refine ⟨5026599055037013405679997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214468226348245905309013205 5026599055037013405679997)
                    ·
                      refine ⟨1884974645638880027129999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026599055037013405679997 1884974645638880027129999)
                      ·
                        rfl

theorem cell23_3670975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_3670975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670975 prefixEnd_3670975 := by exact prefixLift 3670975
  have htrace : WordTrace (prefixWord ++ tailWord_3670975) baseStart_3670975 baseEnd_3670975 := by
    simpa [prefixWord, tailWord_3670975, baseEnd_3670975] using wordTrace_append hprefix tailTrace_3670975
  have hstable : (prefixWord ++ tailWord_3670975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670975).length < 2 ^ (prefixWord ++ tailWord_3670975).sum := by decide
  have hdescent : baseEnd_3670975 < baseStart_3670975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670992 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_3670992 : Nat := 118140960795 + 3670992 * 2 ^ 59
def prefixEnd_3670992 : Nat := 4983230072969 + 3 ^ 40 * 3670992 * 2
def baseEnd_3670992 : Nat := 1884983374810006460617421

theorem tailTrace_3670992 : CollatzResearch.WordTrace tailWord_3670992 prefixEnd_3670992 1884983374810006460617421 := by
  unfold tailWord_3670992
  simp only [CollatzResearch.WordTrace]
  refine ⟨66946038958315207182115615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89261385277753609576154153 66946038958315207182115615)
  ·
    refine ⟨100419058437472810773173423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66946038958315207182115615 100419058437472810773173423)
    ·
      refine ⟨150628587656209216159760135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100419058437472810773173423 150628587656209216159760135)
      ·
        refine ⟨225942881484313824239640203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150628587656209216159760135 225942881484313824239640203)
        ·
          refine ⟨338914322226470736359460305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225942881484313824239640203 338914322226470736359460305)
          ·
            refine ⟨254185741669853052269595229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338914322226470736359460305 254185741669853052269595229)
            ·
              refine ⟨95319653126194894601098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254185741669853052269595229 95319653126194894601098211)
              ·
                refine ⟨142979479689292341901647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95319653126194894601098211 142979479689292341901647317)
                ·
                  refine ⟨3351081555217789263319859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142979479689292341901647317 3351081555217789263319859)
                  ·
                    refine ⟨5026622332826683894979789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3351081555217789263319859 5026622332826683894979789)
                    ·
                      refine ⟨1884983374810006460617421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026622332826683894979789 1884983374810006460617421)
                      ·
                        rfl

theorem cell23_3670992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_3670992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670992 prefixEnd_3670992 := by exact prefixLift 3670992
  have htrace : WordTrace (prefixWord ++ tailWord_3670992) baseStart_3670992 baseEnd_3670992 := by
    simpa [prefixWord, tailWord_3670992, baseEnd_3670992] using wordTrace_append hprefix tailTrace_3670992
  have hstable : (prefixWord ++ tailWord_3670992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670992).length < 2 ^ (prefixWord ++ tailWord_3670992).sum := by decide
  have hdescent : baseEnd_3670992 < baseStart_3670992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671032 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_3671032 : Nat := 118140960795 + 3671032 * 2 ^ 59
def prefixEnd_3671032 : Nat := 4983230072969 + 3 ^ 40 * 3671032 * 2
def baseEnd_3671032 : Nat := 1885003914036186304117237

theorem tailTrace_3671032 : CollatzResearch.WordTrace tailWord_3671032 prefixEnd_3671032 1885003914036186304117237 := by
  unfold tailWord_3671032
  simp only [CollatzResearch.WordTrace]
  refine ⟨66946768418242750597843675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89262357890990334130458233 66946768418242750597843675)
  ·
    refine ⟨100420152627364125896765513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66946768418242750597843675 100420152627364125896765513)
    ·
      refine ⟨75315114470523094422574135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100420152627364125896765513 75315114470523094422574135)
      ·
        refine ⟨112972671705784641633861203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75315114470523094422574135 112972671705784641633861203)
        ·
          refine ⟨169459007558676962450791805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112972671705784641633861203 169459007558676962450791805)
          ·
            refine ⟨63547127834503860919046927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169459007558676962450791805 63547127834503860919046927)
            ·
              refine ⟨95320691751755791378570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63547127834503860919046927 95320691751755791378570391)
              ·
                refine ⟨142981037627633687067855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95320691751755791378570391 142981037627633687067855587)
                ·
                  refine ⟨214471556441450530601783381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142981037627633687067855587 214471556441450530601783381)
                  ·
                    refine ⟨2513338552048248405489649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 214471556441450530601783381 2513338552048248405489649)
                    ·
                      refine ⟨1885003914036186304117237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513338552048248405489649 1885003914036186304117237)
                      ·
                        rfl

theorem cell23_3671032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_3671032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671032 prefixEnd_3671032 := by exact prefixLift 3671032
  have htrace : WordTrace (prefixWord ++ tailWord_3671032) baseStart_3671032 baseEnd_3671032 := by
    simpa [prefixWord, tailWord_3671032, baseEnd_3671032] using wordTrace_append hprefix tailTrace_3671032
  have hstable : (prefixWord ++ tailWord_3671032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671032).length < 2 ^ (prefixWord ++ tailWord_3671032).sum := by decide
  have hdescent : baseEnd_3671032 < baseStart_3671032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671035 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_3671035 : Nat := 118140960795 + 3671035 * 2 ^ 59
def prefixEnd_3671035 : Nat := 4983230072969 + 3 ^ 40 * 3671035 * 2
def baseEnd_3671035 : Nat := 1885005454478149792379723

theorem tailTrace_3671035 : CollatzResearch.WordTrace tailWord_3671035 prefixEnd_3671035 1885005454478149792379723 := by
  unfold tailWord_3671035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133893646255474632708046559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89262430836983088472031039 133893646255474632708046559)
  ·
    refine ⟨200840469383211949062069839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133893646255474632708046559 200840469383211949062069839)
    ·
      refine ⟨301260704074817923593104759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200840469383211949062069839 301260704074817923593104759)
      ·
        refine ⟨451891056112226885389657139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301260704074817923593104759 451891056112226885389657139)
        ·
          refine ⟨677836584168340328084485709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451891056112226885389657139 677836584168340328084485709)
          ·
            refine ⟨254188719063127623031682141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677836584168340328084485709 254188719063127623031682141)
            ·
              refine ⟨95320769648672858636880803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254188719063127623031682141 95320769648672858636880803)
              ·
                refine ⟨142981154473009287955321205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95320769648672858636880803 142981154473009287955321205)
                ·
                  refine ⟨13404483231844620745811363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142981154473009287955321205 13404483231844620745811363)
                  ·
                    refine ⟨20106724847766931118717045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404483231844620745811363 20106724847766931118717045)
                    ·
                      refine ⟨1885005454478149792379723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20106724847766931118717045 1885005454478149792379723)
                      ·
                        rfl

theorem cell23_3671035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_3671035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671035 prefixEnd_3671035 := by exact prefixLift 3671035
  have htrace : WordTrace (prefixWord ++ tailWord_3671035) baseStart_3671035 baseEnd_3671035 := by
    simpa [prefixWord, tailWord_3671035, baseEnd_3671035] using wordTrace_append hprefix tailTrace_3671035
  have hstable : (prefixWord ++ tailWord_3671035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671035).length < 2 ^ (prefixWord ++ tailWord_3671035).sum := by decide
  have hdescent : baseEnd_3671035 < baseStart_3671035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671049 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 5, 2, 2]
def baseStart_3671049 : Nat := 118140960795 + 3671049 * 2 ^ 59
def prefixEnd_3671049 : Nat := 4983230072969 + 3 ^ 40 * 3671049 * 2
def baseEnd_3671049 : Nat := 1885012643207312737604659

theorem tailTrace_3671049 : CollatzResearch.WordTrace tailWord_3671049 prefixEnd_3671049 1885012643207312737604659 := by
  unfold tailWord_3671049
  simp only [CollatzResearch.WordTrace]
  refine ⟨133894156877423913099056201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89262771251615942066037467 133894156877423913099056201)
  ·
    refine ⟨100420617658067934824292151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133894156877423913099056201 100420617658067934824292151)
    ·
      refine ⟨150630926487101902236438227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100420617658067934824292151 150630926487101902236438227)
      ·
        refine ⟨225946389730652853354657341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150630926487101902236438227 225946389730652853354657341)
        ·
          refine ⟨84729896148994820007996503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225946389730652853354657341 84729896148994820007996503)
          ·
            refine ⟨127094844223492230011994755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84729896148994820007996503 127094844223492230011994755)
            ·
              refine ⟨190642266335238345017992133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127094844223492230011994755 190642266335238345017992133)
              ·
                refine ⟨35745424937857189690873525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190642266335238345017992133 35745424937857189690873525)
                ·
                  refine ⟨3351133587924111533519393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35745424937857189690873525 3351133587924111533519393)
                  ·
                    refine ⟨2513350190943083650139545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351133587924111533519393 2513350190943083650139545)
                    ·
                      refine ⟨1885012643207312737604659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513350190943083650139545 1885012643207312737604659)
                      ·
                        rfl

theorem cell23_3671049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2, 2].length) (baseStart_3671049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671049 prefixEnd_3671049 := by exact prefixLift 3671049
  have htrace : WordTrace (prefixWord ++ tailWord_3671049) baseStart_3671049 baseEnd_3671049 := by
    simpa [prefixWord, tailWord_3671049, baseEnd_3671049] using wordTrace_append hprefix tailTrace_3671049
  have hstable : (prefixWord ++ tailWord_3671049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671049).length < 2 ^ (prefixWord ++ tailWord_3671049).sum := by decide
  have hdescent : baseEnd_3671049 < baseStart_3671049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671052 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3671052 : Nat := 118140960795 + 3671052 * 2 ^ 59
def prefixEnd_3671052 : Nat := 4983230072969 + 3 ^ 40 * 3671052 * 2
def baseEnd_3671052 : Nat := 1885014183649276225867145

theorem tailTrace_3671052 : CollatzResearch.WordTrace tailWord_3671052 prefixEnd_3671052 1885014183649276225867145 := by
  unfold tailWord_3671052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66947133148206522305707705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89262844197608696407610273 66947133148206522305707705)
  ·
    refine ⟨50210349861154891729280779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66947133148206522305707705 50210349861154891729280779)
    ·
      refine ⟨75315524791732337593921169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50210349861154891729280779 75315524791732337593921169)
      ·
        refine ⟨56486643593799253195440877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75315524791732337593921169 56486643593799253195440877)
        ·
          refine ⟨21182491347674719948290329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56486643593799253195440877 21182491347674719948290329)
          ·
            refine ⟨15886868510756039961217747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21182491347674719948290329 15886868510756039961217747)
            ·
              refine ⟨23830302766134059941826621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15886868510756039961217747 23830302766134059941826621)
              ·
                refine ⟨8936363537300272478184983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23830302766134059941826621 8936363537300272478184983)
                ·
                  refine ⟨13404545305950408717277475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8936363537300272478184983 13404545305950408717277475)
                  ·
                    refine ⟨20106817958925613075916213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404545305950408717277475 20106817958925613075916213)
                    ·
                      refine ⟨1885014183649276225867145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20106817958925613075916213 1885014183649276225867145)
                      ·
                        rfl

theorem cell23_3671052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3671052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671052 prefixEnd_3671052 := by exact prefixLift 3671052
  have htrace : WordTrace (prefixWord ++ tailWord_3671052) baseStart_3671052 baseEnd_3671052 := by
    simpa [prefixWord, tailWord_3671052, baseEnd_3671052] using wordTrace_append hprefix tailTrace_3671052
  have hstable : (prefixWord ++ tailWord_3671052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671052).length < 2 ^ (prefixWord ++ tailWord_3671052).sum := by decide
  have hdescent : baseEnd_3671052 < baseStart_3671052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671076 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3671076 : Nat := 118140960795 + 3671076 * 2 ^ 59
def prefixEnd_3671076 : Nat := 4983230072969 + 3 ^ 40 * 3671076 * 2
def baseEnd_3671076 : Nat := 628342169061661377322345

theorem tailTrace_3671076 : CollatzResearch.WordTrace tailWord_3671076 prefixEnd_3671076 628342169061661377322345 := by
  unfold tailWord_3671076
  simp only [CollatzResearch.WordTrace]
  refine ⟨66947570824163048355144541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89263427765550731140192721 66947570824163048355144541)
  ·
    refine ⟨25105339059061143133179203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66947570824163048355144541 25105339059061143133179203)
    ·
      refine ⟨37658008588591714699768805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25105339059061143133179203 37658008588591714699768805)
      ·
        refine ⟨7060876610360946506206651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37658008588591714699768805 7060876610360946506206651)
        ·
          refine ⟨10591314915541419759309977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060876610360946506206651 10591314915541419759309977)
          ·
            refine ⟨7943486186656064819482483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10591314915541419759309977 7943486186656064819482483)
            ·
              refine ⟨11915229279984097229223725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943486186656064819482483 11915229279984097229223725)
              ·
                refine ⟨4468210979994036460958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11915229279984097229223725 4468210979994036460958897)
                ·
                  refine ⟨3351158234995527345719173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468210979994036460958897 3351158234995527345719173)
                  ·
                    refine ⟨628342169061661377322345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351158234995527345719173 628342169061661377322345)
                    ·
                      rfl

theorem cell23_3671076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3671076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671076 prefixEnd_3671076 := by exact prefixLift 3671076
  have htrace : WordTrace (prefixWord ++ tailWord_3671076) baseStart_3671076 baseEnd_3671076 := by
    simpa [prefixWord, tailWord_3671076, baseEnd_3671076] using wordTrace_append hprefix tailTrace_3671076
  have hstable : (prefixWord ++ tailWord_3671076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671076).length < 2 ^ (prefixWord ++ tailWord_3671076).sum := by decide
  have hdescent : baseEnd_3671076 < baseStart_3671076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671079 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3671079 : Nat := 118140960795 + 3671079 * 2 ^ 59
def prefixEnd_3671079 : Nat := 4983230072969 + 3 ^ 40 * 3671079 * 2
def baseEnd_3671079 : Nat := 1885028047626947620229521

theorem tailTrace_3671079 : CollatzResearch.WordTrace tailWord_3671079 prefixEnd_3671079 1885028047626947620229521 := by
  unfold tailWord_3671079
  simp only [CollatzResearch.WordTrace]
  refine ⟨133895251067315228222648291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89263500711543485481765527 133895251067315228222648291)
  ·
    refine ⟨200842876600972842333972437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133895251067315228222648291 200842876600972842333972437)
    ·
      refine ⟨4707254920335300992202479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 200842876600972842333972437 4707254920335300992202479)
      ·
        refine ⟨7060882380502951488303719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707254920335300992202479 7060882380502951488303719)
        ·
          refine ⟨10591323570754427232455579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060882380502951488303719 10591323570754427232455579)
          ·
            refine ⟨15886985356131640848683369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591323570754427232455579 15886985356131640848683369)
            ·
              refine ⟨11915239017098730636512527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15886985356131640848683369 11915239017098730636512527)
              ·
                refine ⟨17872858525648095954768791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915239017098730636512527 17872858525648095954768791)
                ·
                  refine ⟨26809287788472143932153187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17872858525648095954768791 26809287788472143932153187)
                  ·
                    refine ⟨40213931682708215898229781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26809287788472143932153187 40213931682708215898229781)
                    ·
                      refine ⟨1885028047626947620229521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40213931682708215898229781 1885028047626947620229521)
                      ·
                        rfl

theorem cell23_3671079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3671079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671079 prefixEnd_3671079 := by exact prefixLift 3671079
  have htrace : WordTrace (prefixWord ++ tailWord_3671079) baseStart_3671079 baseEnd_3671079 := by
    simpa [prefixWord, tailWord_3671079, baseEnd_3671079] using wordTrace_append hprefix tailTrace_3671079
  have hstable : (prefixWord ++ tailWord_3671079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671079).length < 2 ^ (prefixWord ++ tailWord_3671079).sum := by decide
  have hdescent : baseEnd_3671079 < baseStart_3671079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671117 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_3671117 : Nat := 118140960795 + 3671117 * 2 ^ 59
def prefixEnd_3671117 : Nat := 4983230072969 + 3 ^ 40 * 3671117 * 2
def baseEnd_3671117 : Nat := 1885047559891818471554347

theorem tailTrace_3671117 : CollatzResearch.WordTrace tailWord_3671117 prefixEnd_3671117 1885047559891818471554347 := by
  unfold tailWord_3671117
  simp only [CollatzResearch.WordTrace]
  refine ⟨133896637041177560712531605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89264424694118373808354403 133896637041177560712531605)
  ·
    refine ⟨6276404861305198158399919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133896637041177560712531605 6276404861305198158399919)
    ·
      refine ⟨9414607291957797237599879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6276404861305198158399919 9414607291957797237599879)
      ·
        refine ⟨14121910937936695856399819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414607291957797237599879 14121910937936695856399819)
        ·
          refine ⟨21182866406905043784599729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14121910937936695856399819 21182866406905043784599729)
          ·
            refine ⟨15887149805178782838449797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21182866406905043784599729 15887149805178782838449797)
            ·
              refine ⟨2978840588471021782209337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15887149805178782838449797 2978840588471021782209337)
              ·
                refine ⟨2234130441353266336657003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978840588471021782209337 2234130441353266336657003)
                ·
                  refine ⟨3351195662029899504985505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234130441353266336657003 3351195662029899504985505)
                  ·
                    refine ⟨2513396746522424628739129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351195662029899504985505 2513396746522424628739129)
                    ·
                      refine ⟨1885047559891818471554347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513396746522424628739129 1885047559891818471554347)
                      ·
                        rfl

theorem cell23_3671117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_3671117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671117 prefixEnd_3671117 := by exact prefixLift 3671117
  have htrace : WordTrace (prefixWord ++ tailWord_3671117) baseStart_3671117 baseEnd_3671117 := by
    simpa [prefixWord, tailWord_3671117, baseEnd_3671117] using wordTrace_append hprefix tailTrace_3671117
  have hstable : (prefixWord ++ tailWord_3671117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671117).length < 2 ^ (prefixWord ++ tailWord_3671117).sum := by decide
  have hdescent : baseEnd_3671117 < baseStart_3671117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671133 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3671133 : Nat := 118140960795 + 3671133 * 2 ^ 59
def prefixEnd_3671133 : Nat := 4983230072969 + 3 ^ 40 * 3671133 * 2
def baseEnd_3671133 : Nat := 1885055775582290408954273

theorem tailTrace_3671133 : CollatzResearch.WordTrace tailWord_3671133 prefixEnd_3671133 1885055775582290408954273 := by
  unfold tailWord_3671133
  simp only [CollatzResearch.WordTrace]
  refine ⟨133897220609119595445114053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89264813739413063630076035 133897220609119595445114053)
  ·
    refine ⟨25105728864209924145958885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133897220609119595445114053 25105728864209924145958885)
    ·
      refine ⟨4707324162039360777367291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25105728864209924145958885 4707324162039360777367291)
      ·
        refine ⟨7060986243059041166050937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707324162039360777367291 7060986243059041166050937)
        ·
          refine ⟨5295739682294280874538203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060986243059041166050937 5295739682294280874538203)
          ·
            refine ⟨7943609523441421311807305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295739682294280874538203 7943609523441421311807305)
            ·
              refine ⟨5957707142581065983855479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7943609523441421311807305 5957707142581065983855479)
              ·
                refine ⟨8936560713871598975783219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957707142581065983855479 8936560713871598975783219)
                ·
                  refine ⟨13404841070807398463674829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8936560713871598975783219 13404841070807398463674829)
                  ·
                    refine ⟨5026815401552774423878061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13404841070807398463674829 5026815401552774423878061)
                    ·
                      refine ⟨1885055775582290408954273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026815401552774423878061 1885055775582290408954273)
                      ·
                        rfl

theorem cell23_3671133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3671133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671133 prefixEnd_3671133 := by exact prefixLift 3671133
  have htrace : WordTrace (prefixWord ++ tailWord_3671133) baseStart_3671133 baseEnd_3671133 := by
    simpa [prefixWord, tailWord_3671133, baseEnd_3671133] using wordTrace_append hprefix tailTrace_3671133
  have hstable : (prefixWord ++ tailWord_3671133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671133).length < 2 ^ (prefixWord ++ tailWord_3671133).sum := by decide
  have hdescent : baseEnd_3671133 < baseStart_3671133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671152 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_3671152 : Nat := 118140960795 + 3671152 * 2 ^ 59
def prefixEnd_3671152 : Nat := 4983230072969 + 3 ^ 40 * 3671152 * 2
def baseEnd_3671152 : Nat := 1885065531714725834616685

theorem tailTrace_3671152 : CollatzResearch.WordTrace tailWord_3671152 prefixEnd_3671152 1885065531714725834616685 := by
  unfold tailWord_3671152
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948956798025380845027855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89265275730700507793370473 66948956798025380845027855)
  ·
    refine ⟨100423435197038071267541783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66948956798025380845027855 100423435197038071267541783)
    ·
      refine ⟨150635152795557106901312675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100423435197038071267541783 150635152795557106901312675)
      ·
        refine ⟨225952729193335660351969013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150635152795557106901312675 225952729193335660351969013)
        ·
          refine ⟨21183068361875218157997095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225952729193335660351969013 21183068361875218157997095)
          ·
            refine ⟨31774602542812827236995643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21183068361875218157997095 31774602542812827236995643)
            ·
              refine ⟨47661903814219240855493465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31774602542812827236995643 47661903814219240855493465)
              ·
                refine ⟨35746427860664430641620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47661903814219240855493465 35746427860664430641620099)
                ·
                  refine ⟨53619641790996645962430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35746427860664430641620099 53619641790996645962430149)
                  ·
                    refine ⟨10053682835811871117955653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53619641790996645962430149 10053682835811871117955653)
                    ·
                      refine ⟨1885065531714725834616685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10053682835811871117955653 1885065531714725834616685)
                      ·
                        rfl

theorem cell23_3671152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_3671152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671152 prefixEnd_3671152 := by exact prefixLift 3671152
  have htrace : WordTrace (prefixWord ++ tailWord_3671152) baseStart_3671152 baseEnd_3671152 := by
    simpa [prefixWord, tailWord_3671152, baseEnd_3671152] using wordTrace_append hprefix tailTrace_3671152
  have hstable : (prefixWord ++ tailWord_3671152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671152).length < 2 ^ (prefixWord ++ tailWord_3671152).sum := by decide
  have hdescent : baseEnd_3671152 < baseStart_3671152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671169 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3671169 : Nat := 118140960795 + 3671169 * 2 ^ 59
def prefixEnd_3671169 : Nat := 4983230072969 + 3 ^ 40 * 3671169 * 2
def baseEnd_3671169 : Nat := 1885074260885852268104107

theorem tailTrace_3671169 : CollatzResearch.WordTrace tailWord_3671169 prefixEnd_3671169 1885074260885852268104107 := by
  unfold tailWord_3671169
  simp only [CollatzResearch.WordTrace]
  refine ⟨133898533636989173593424561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89265689091326115728949707 133898533636989173593424561)
  ·
    refine ⟨100423900227741880195068421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133898533636989173593424561 100423900227741880195068421)
    ·
      refine ⟨18829481292701602536575329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100423900227741880195068421 18829481292701602536575329)
      ·
        refine ⟨14122110969526201902431497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18829481292701602536575329 14122110969526201902431497)
        ·
          refine ⟨10591583227144651426823623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14122110969526201902431497 10591583227144651426823623)
          ·
            refine ⟨15887374840716977140235435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591583227144651426823623 15887374840716977140235435)
            ·
              refine ⟨23831062261075465710353153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887374840716977140235435 23831062261075465710353153)
              ·
                refine ⟨17873296695806599282764865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23831062261075465710353153 17873296695806599282764865)
                ·
                  refine ⟨13404972521854949462073649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17873296695806599282764865 13404972521854949462073649)
                  ·
                    refine ⟨10053729391391212096555237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13404972521854949462073649 10053729391391212096555237)
                    ·
                      refine ⟨1885074260885852268104107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10053729391391212096555237 1885074260885852268104107)
                      ·
                        rfl

theorem cell23_3671169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3671169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671169 prefixEnd_3671169 := by exact prefixLift 3671169
  have htrace : WordTrace (prefixWord ++ tailWord_3671169) baseStart_3671169 baseEnd_3671169 := by
    simpa [prefixWord, tailWord_3671169, baseEnd_3671169] using wordTrace_append hprefix tailTrace_3671169
  have hstable : (prefixWord ++ tailWord_3671169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671169).length < 2 ^ (prefixWord ++ tailWord_3671169).sum := by decide
  have hdescent : baseEnd_3671169 < baseStart_3671169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671173 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_3671173 : Nat := 118140960795 + 3671173 * 2 ^ 59
def prefixEnd_3671173 : Nat := 4983230072969 + 3 ^ 40 * 3671173 * 2
def baseEnd_3671173 : Nat := 1885076314808470252454089

theorem tailTrace_3671173 : CollatzResearch.WordTrace tailWord_3671173 prefixEnd_3671173 1885076314808470252454089 := by
  unfold tailWord_3671173
  simp only [CollatzResearch.WordTrace]
  refine ⟨133898679528974682276570173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89265786352649788184380115 133898679528974682276570173)
  ·
    refine ⟨50212004823365505853713815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133898679528974682276570173 50212004823365505853713815)
    ·
      refine ⟨75318007235048258780570723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50212004823365505853713815 75318007235048258780570723)
      ·
        refine ⟨112977010852572388170856085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75318007235048258780570723 112977010852572388170856085)
        ·
          refine ⟨5295797383714330695508879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112977010852572388170856085 5295797383714330695508879)
          ·
            refine ⟨7943696075571496043263319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295797383714330695508879 7943696075571496043263319)
            ·
              refine ⟨11915544113357244064894979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943696075571496043263319 11915544113357244064894979)
              ·
                refine ⟨17873316170035866097342469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915544113357244064894979 17873316170035866097342469)
                ·
                  refine ⟨3351246781881724893251713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17873316170035866097342469 3351246781881724893251713)
                  ·
                    refine ⟨2513435086411293669938785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351246781881724893251713 2513435086411293669938785)
                    ·
                      refine ⟨1885076314808470252454089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513435086411293669938785 1885076314808470252454089)
                      ·
                        rfl

theorem cell23_3671173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_3671173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671173 prefixEnd_3671173 := by exact prefixLift 3671173
  have htrace : WordTrace (prefixWord ++ tailWord_3671173) baseStart_3671173 baseEnd_3671173 := by
    simpa [prefixWord, tailWord_3671173, baseEnd_3671173] using wordTrace_append hprefix tailTrace_3671173
  have hstable : (prefixWord ++ tailWord_3671173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671173).length < 2 ^ (prefixWord ++ tailWord_3671173).sum := by decide
  have hdescent : baseEnd_3671173 < baseStart_3671173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671229 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3671229 : Nat := 118140960795 + 3671229 * 2 ^ 59
def prefixEnd_3671229 : Nat := 4983230072969 + 3 ^ 40 * 3671229 * 2
def baseEnd_3671229 : Nat := 1885105069725122033353831

theorem tailTrace_3671229 : CollatzResearch.WordTrace tailWord_3671229 prefixEnd_3671229 1885105069725122033353831 := by
  unfold tailWord_3671229
  simp only [CollatzResearch.WordTrace]
  refine ⟨133900722016771803840608741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89267148011181202560405827 133900722016771803840608741)
  ·
    refine ⟨25106385378144713220114139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133900722016771803840608741 25106385378144713220114139)
    ·
      refine ⟨37659578067217069830171209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25106385378144713220114139 37659578067217069830171209)
      ·
        refine ⟨28244683550412802372628407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37659578067217069830171209 28244683550412802372628407)
        ·
          refine ⟨42367025325619203558942611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28244683550412802372628407 42367025325619203558942611)
          ·
            refine ⟨63550537988428805338413917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42367025325619203558942611 63550537988428805338413917)
            ·
              refine ⟨23831451745660802001905219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63550537988428805338413917 23831451745660802001905219)
              ·
                refine ⟨35747177618491203002857829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23831451745660802001905219 35747177618491203002857829)
                ·
                  refine ⟨6702595803467100563035843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35747177618491203002857829 6702595803467100563035843)
                  ·
                    refine ⟨10053893705200650844553765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6702595803467100563035843 10053893705200650844553765)
                    ·
                      refine ⟨1885105069725122033353831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10053893705200650844553765 1885105069725122033353831)
                      ·
                        rfl

theorem cell23_3671229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3671229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671229 prefixEnd_3671229 := by exact prefixLift 3671229
  have htrace : WordTrace (prefixWord ++ tailWord_3671229) baseStart_3671229 baseEnd_3671229 := by
    simpa [prefixWord, tailWord_3671229, baseEnd_3671229] using wordTrace_append hprefix tailTrace_3671229
  have hstable : (prefixWord ++ tailWord_3671229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671229).length < 2 ^ (prefixWord ++ tailWord_3671229).sum := by decide
  have hdescent : baseEnd_3671229 < baseStart_3671229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671236 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3671236 : Nat := 118140960795 + 3671236 * 2 ^ 59
def prefixEnd_3671236 : Nat := 4983230072969 + 3 ^ 40 * 3671236 * 2
def baseEnd_3671236 : Nat := 1885108664089703505966299

theorem tailTrace_3671236 : CollatzResearch.WordTrace tailWord_3671236 prefixEnd_3671236 1885108664089703505966299 := by
  unfold tailWord_3671236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66950488663873222018056781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89267318218497629357409041 66950488663873222018056781)
  ·
    refine ⟨25106433248952458256771293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66950488663873222018056781 25106433248952458256771293)
    ·
      refine ⟨9414912468357171846289235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25106433248952458256771293 9414912468357171846289235)
      ·
        refine ⟨14122368702535757769433853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414912468357171846289235 14122368702535757769433853)
        ·
          refine ⟨5295888263450909163537695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14122368702535757769433853 5295888263450909163537695)
          ·
            refine ⟨7943832395176363745306543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295888263450909163537695 7943832395176363745306543)
            ·
              refine ⟨11915748592764545617959815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943832395176363745306543 11915748592764545617959815)
              ·
                refine ⟨17873622889146818426939723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915748592764545617959815 17873622889146818426939723)
                ·
                  refine ⟨26810434333720227640409585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17873622889146818426939723 26810434333720227640409585)
                  ·
                    refine ⟨20107825750290170730307189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26810434333720227640409585 20107825750290170730307189)
                    ·
                      refine ⟨1885108664089703505966299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20107825750290170730307189 1885108664089703505966299)
                      ·
                        rfl

theorem cell23_3671236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3671236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671236 prefixEnd_3671236 := by exact prefixLift 3671236
  have htrace : WordTrace (prefixWord ++ tailWord_3671236) baseStart_3671236 baseEnd_3671236 := by
    simpa [prefixWord, tailWord_3671236, baseEnd_3671236] using wordTrace_append hprefix tailTrace_3671236
  have hstable : (prefixWord ++ tailWord_3671236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671236).length < 2 ^ (prefixWord ++ tailWord_3671236).sum := by decide
  have hdescent : baseEnd_3671236 < baseStart_3671236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671249 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_3671249 : Nat := 118140960795 + 3671249 * 2 ^ 59
def prefixEnd_3671249 : Nat := 4983230072969 + 3 ^ 40 * 3671249 * 2
def baseEnd_3671249 : Nat := 1885115339338211955103739

theorem tailTrace_3671249 : CollatzResearch.WordTrace tailWord_3671249 prefixEnd_3671249 1885115339338211955103739 := by
  unfold tailWord_3671249
  simp only [CollatzResearch.WordTrace]
  refine ⟨133901451476699347256336801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89267634317799564837557867 133901451476699347256336801)
  ·
    refine ⟨100426088607524510442252601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133901451476699347256336801 100426088607524510442252601)
    ·
      refine ⟨75319566455643382831689451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100426088607524510442252601 75319566455643382831689451)
      ·
        refine ⟨112979349683465074247534177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75319566455643382831689451 112979349683465074247534177)
        ·
          refine ⟨84734512262598805685650633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112979349683465074247534177 84734512262598805685650633)
          ·
            refine ⟨63550884196949104264237975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84734512262598805685650633 63550884196949104264237975)
            ·
              refine ⟨95326326295423656396356963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63550884196949104264237975 95326326295423656396356963)
              ·
                refine ⟨142989489443135484594535445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95326326295423656396356963 142989489443135484594535445)
                ·
                  refine ⟨6702632317646975840368849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142989489443135484594535445 6702632317646975840368849)
                  ·
                    refine ⟨5026974238235231880276637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702632317646975840368849 5026974238235231880276637)
                    ·
                      refine ⟨1885115339338211955103739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5026974238235231880276637 1885115339338211955103739)
                      ·
                        rfl

theorem cell23_3671249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_3671249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671249 prefixEnd_3671249 := by exact prefixLift 3671249
  have htrace : WordTrace (prefixWord ++ tailWord_3671249) baseStart_3671249 baseEnd_3671249 := by
    simpa [prefixWord, tailWord_3671249, baseEnd_3671249] using wordTrace_append hprefix tailTrace_3671249
  have hstable : (prefixWord ++ tailWord_3671249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671249).length < 2 ^ (prefixWord ++ tailWord_3671249).sum := by decide
  have hdescent : baseEnd_3671249 < baseStart_3671249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671296 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_3671296 : Nat := 118140960795 + 3671296 * 2 ^ 59
def prefixEnd_3671296 : Nat := 4983230072969 + 3 ^ 40 * 3671296 * 2
def baseEnd_3671296 : Nat := 1885139472928973271216023

theorem tailTrace_3671296 : CollatzResearch.WordTrace tailWord_3671296 prefixEnd_3671296 1885139472928973271216023 := by
  unfold tailWord_3671296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66951582853764537141648871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89268777138352716188865161 66951582853764537141648871)
  ·
    refine ⟨100427374280646805712473307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66951582853764537141648871 100427374280646805712473307)
    ·
      refine ⟨150641061420970208568709961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100427374280646805712473307 150641061420970208568709961)
      ·
        refine ⟨112980796065727656426532471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150641061420970208568709961 112980796065727656426532471)
        ·
          refine ⟨169471194098591484639798707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112980796065727656426532471 169471194098591484639798707)
          ·
            refine ⟨254206791147887226959698061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169471194098591484639798707 254206791147887226959698061)
            ·
              refine ⟨95327546680457710109886773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254206791147887226959698061 95327546680457710109886773)
              ·
                refine ⟨8936957501292910322801885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95327546680457710109886773 8936957501292910322801885)
                ·
                  refine ⟨3351359062984841371050707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8936957501292910322801885 3351359062984841371050707)
                  ·
                    refine ⟨5027038594477262056576061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3351359062984841371050707 5027038594477262056576061)
                    ·
                      refine ⟨1885139472928973271216023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027038594477262056576061 1885139472928973271216023)
                      ·
                        rfl

theorem cell23_3671296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_3671296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671296 prefixEnd_3671296 := by exact prefixLift 3671296
  have htrace : WordTrace (prefixWord ++ tailWord_3671296) baseStart_3671296 baseEnd_3671296 := by
    simpa [prefixWord, tailWord_3671296, baseEnd_3671296] using wordTrace_append hprefix tailTrace_3671296
  have hstable : (prefixWord ++ tailWord_3671296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671296).length < 2 ^ (prefixWord ++ tailWord_3671296).sum := by decide
  have hdescent : baseEnd_3671296 < baseStart_3671296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671299 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 3, 5]
def baseStart_3671299 : Nat := 118140960795 + 3671299 * 2 ^ 59
def prefixEnd_3671299 : Nat := 4983230072969 + 3 ^ 40 * 3671299 * 2
def baseEnd_3671299 : Nat := 628380337790312253159503

theorem tailTrace_3671299 : CollatzResearch.WordTrace tailWord_3671299 prefixEnd_3671299 628380337790312253159503 := by
  unfold tailWord_3671299
  simp only [CollatzResearch.WordTrace]
  refine ⟨133903275126518205795656951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89268850084345470530437967 133903275126518205795656951)
  ·
    refine ⟨200854912689777308693485427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133903275126518205795656951 200854912689777308693485427)
    ·
      refine ⟨301282369034665963040228141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200854912689777308693485427 301282369034665963040228141)
      ·
        refine ⟨112980888387999736140085553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301282369034665963040228141 112980888387999736140085553)
        ·
          refine ⟨84735666290999802105064165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112980888387999736140085553 84735666290999802105064165)
          ·
            refine ⟨15887937429562462894699531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84735666290999802105064165 15887937429562462894699531)
            ·
              refine ⟨23831906144343694342049297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887937429562462894699531 23831906144343694342049297)
              ·
                refine ⟨17873929608257770756536973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23831906144343694342049297 17873929608257770756536973)
                ·
                  refine ⟨6702723603096664033701365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17873929608257770756536973 6702723603096664033701365)
                  ·
                    refine ⟨628380337790312253159503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6702723603096664033701365 628380337790312253159503)
                    ·
                      rfl

theorem cell23_3671299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].length) (baseStart_3671299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671299 prefixEnd_3671299 := by exact prefixLift 3671299
  have htrace : WordTrace (prefixWord ++ tailWord_3671299) baseStart_3671299 baseEnd_3671299 := by
    simpa [prefixWord, tailWord_3671299, baseEnd_3671299] using wordTrace_append hprefix tailTrace_3671299
  have hstable : (prefixWord ++ tailWord_3671299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671299).length < 2 ^ (prefixWord ++ tailWord_3671299).sum := by decide
  have hdescent : baseEnd_3671299 < baseStart_3671299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671306 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_3671306 : Nat := 118140960795 + 3671306 * 2 ^ 59
def prefixEnd_3671306 : Nat := 4983230072969 + 3 ^ 40 * 3671306 * 2
def baseEnd_3671306 : Nat := 1885144607735518232090977

theorem tailTrace_3671306 : CollatzResearch.WordTrace tailWord_3671306 prefixEnd_3671306 1885144607735518232090977 := by
  unfold tailWord_3671306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33475882609373211497790443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89269020291661897327441181 33475882609373211497790443)
  ·
    refine ⟨50213823914059817246685665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33475882609373211497790443 50213823914059817246685665)
    ·
      refine ⟨37660367935544862935014249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50213823914059817246685665 37660367935544862935014249)
      ·
        refine ⟨28245275951658647201260687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37660367935544862935014249 28245275951658647201260687)
        ·
          refine ⟨42367913927487970801891031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28245275951658647201260687 42367913927487970801891031)
          ·
            refine ⟨63551870891231956202836547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42367913927487970801891031 63551870891231956202836547)
            ·
              refine ⟨95327806336847934304254821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63551870891231956202836547 95327806336847934304254821)
              ·
                refine ⟨17873963688158987682047779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95327806336847934304254821 17873963688158987682047779)
                ·
                  refine ⟨26810945532238481523071669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17873963688158987682047779 26810945532238481523071669)
                  ·
                    refine ⟨2513526143647357642787969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26810945532238481523071669 2513526143647357642787969)
                    ·
                      refine ⟨1885144607735518232090977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513526143647357642787969 1885144607735518232090977)
                      ·
                        rfl

theorem cell23_3671306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_3671306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671306 prefixEnd_3671306 := by exact prefixLift 3671306
  have htrace : WordTrace (prefixWord ++ tailWord_3671306) baseStart_3671306 baseEnd_3671306 := by
    simpa [prefixWord, tailWord_3671306, baseEnd_3671306] using wordTrace_append hprefix tailTrace_3671306
  have hstable : (prefixWord ++ tailWord_3671306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671306).length < 2 ^ (prefixWord ++ tailWord_3671306).sum := by decide
  have hdescent : baseEnd_3671306 < baseStart_3671306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671333 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_3671333 : Nat := 118140960795 + 3671333 * 2 ^ 59
def prefixEnd_3671333 : Nat := 4983230072969 + 3 ^ 40 * 3671333 * 2
def baseEnd_3671333 : Nat := 628386157237729875484451

theorem tailTrace_3671333 : CollatzResearch.WordTrace tailWord_3671333 prefixEnd_3671333 628386157237729875484451 := by
  unfold tailWord_3671333
  simp only [CollatzResearch.WordTrace]
  refine ⟨133904515208395029602394653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89269676805596686401596435 133904515208395029602394653)
  ·
    refine ⟨50214193203148136100897995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133904515208395029602394653 50214193203148136100897995)
    ·
      refine ⟨75321289804722204151346993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50214193203148136100897995 75321289804722204151346993)
      ·
        refine ⟨56490967353541653113510245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75321289804722204151346993 56490967353541653113510245)
        ·
          refine ⟨10592056378789059958783171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56490967353541653113510245 10592056378789059958783171)
          ·
            refine ⟨15888084568183589938174757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10592056378789059958783171 15888084568183589938174757)
            ·
              refine ⟨2979015856534423113407767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15888084568183589938174757 2979015856534423113407767)
              ·
                refine ⟨4468523784801634670111651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979015856534423113407767 4468523784801634670111651)
                ·
                  refine ⟨6702785677202452005167477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468523784801634670111651 6702785677202452005167477)
                  ·
                    refine ⟨628386157237729875484451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6702785677202452005167477 628386157237729875484451)
                    ·
                      rfl

theorem cell23_3671333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_3671333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671333 prefixEnd_3671333 := by exact prefixLift 3671333
  have htrace : WordTrace (prefixWord ++ tailWord_3671333) baseStart_3671333 baseEnd_3671333 := by
    simpa [prefixWord, tailWord_3671333, baseEnd_3671333] using wordTrace_append hprefix tailTrace_3671333
  have hstable : (prefixWord ++ tailWord_3671333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671333).length < 2 ^ (prefixWord ++ tailWord_3671333).sum := by decide
  have hdescent : baseEnd_3671333 < baseStart_3671333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671356 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3671356 : Nat := 118140960795 + 3671356 * 2 ^ 59
def prefixEnd_3671356 : Nat := 4983230072969 + 3 ^ 40 * 3671356 * 2
def baseEnd_3671356 : Nat := 1885170281768243036465747

theorem tailTrace_3671356 : CollatzResearch.WordTrace tailWord_3671356 prefixEnd_3671356 1885170281768243036465747 := by
  unfold tailWord_3671356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66952677043655852265240961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89270236058207803020321281 66952677043655852265240961)
  ·
    refine ⟨50214507782741889198930721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66952677043655852265240961 50214507782741889198930721)
    ·
      refine ⟨37660880837056416899198041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50214507782741889198930721 37660880837056416899198041)
      ·
        refine ⟨28245660627792312674398531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37660880837056416899198041 28245660627792312674398531)
        ·
          refine ⟨42368490941688469011597797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28245660627792312674398531 42368490941688469011597797)
          ·
            refine ⟨7944092051566587939674587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42368490941688469011597797 7944092051566587939674587)
            ·
              refine ⟨11916138077349881909511881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944092051566587939674587 11916138077349881909511881)
              ·
                refine ⟨8937103558012411432133911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11916138077349881909511881 8937103558012411432133911)
                ·
                  refine ⟨13405655337018617148200867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937103558012411432133911 13405655337018617148200867)
                  ·
                    refine ⟨20108483005527925722301301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13405655337018617148200867 20108483005527925722301301)
                    ·
                      refine ⟨1885170281768243036465747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20108483005527925722301301 1885170281768243036465747)
                      ·
                        rfl

theorem cell23_3671356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3671356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671356 prefixEnd_3671356 := by exact prefixLift 3671356
  have htrace : WordTrace (prefixWord ++ tailWord_3671356) baseStart_3671356 baseEnd_3671356 := by
    simpa [prefixWord, tailWord_3671356, baseEnd_3671356] using wordTrace_append hprefix tailTrace_3671356
  have hstable : (prefixWord ++ tailWord_3671356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671356).length < 2 ^ (prefixWord ++ tailWord_3671356).sum := by decide
  have hdescent : baseEnd_3671356 < baseStart_3671356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671386 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_3671386 : Nat := 118140960795 + 3671386 * 2 ^ 59
def prefixEnd_3671386 : Nat := 4983230072969 + 3 ^ 40 * 3671386 * 2
def baseEnd_3671386 : Nat := 1885185686187877919090609

theorem tailTrace_3671386 : CollatzResearch.WordTrace tailWord_3671386 prefixEnd_3671386 1885185686187877919090609 := by
  unfold tailWord_3671386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33476612069300754913518503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89270965518135346436049341 33476612069300754913518503)
  ·
    refine ⟨50214918103951132370277755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33476612069300754913518503 50214918103951132370277755)
    ·
      refine ⟨75322377155926698555416633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50214918103951132370277755 75322377155926698555416633)
      ·
        refine ⟨56491782866945023916562475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75322377155926698555416633 56491782866945023916562475)
        ·
          refine ⟨84737674300417535874843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56491782866945023916562475 84737674300417535874843713)
          ·
            refine ⟨63553255725313151906132785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84737674300417535874843713 63553255725313151906132785)
            ·
              refine ⟨47664941793984863929599589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63553255725313151906132785 47664941793984863929599589)
              ·
                refine ⟨8937176586372161986799923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47664941793984863929599589 8937176586372161986799923)
                ·
                  refine ⟨13405764879558242980199885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937176586372161986799923 13405764879558242980199885)
                  ·
                    refine ⟨5027161829834341117574957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13405764879558242980199885 5027161829834341117574957)
                    ·
                      refine ⟨1885185686187877919090609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027161829834341117574957 1885185686187877919090609)
                      ·
                        rfl

theorem cell23_3671386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_3671386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671386 prefixEnd_3671386 := by exact prefixLift 3671386
  have htrace : WordTrace (prefixWord ++ tailWord_3671386) baseStart_3671386 baseEnd_3671386 := by
    simpa [prefixWord, tailWord_3671386, baseEnd_3671386] using wordTrace_append hprefix tailTrace_3671386
  have hstable : (prefixWord ++ tailWord_3671386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671386).length < 2 ^ (prefixWord ++ tailWord_3671386).sum := by decide
  have hdescent : baseEnd_3671386 < baseStart_3671386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671404 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_3671404 : Nat := 118140960795 + 3671404 * 2 ^ 59
def prefixEnd_3671404 : Nat := 4983230072969 + 3 ^ 40 * 3671404 * 2
def baseEnd_3671404 : Nat := 1885194928839658848665527

theorem tailTrace_3671404 : CollatzResearch.WordTrace tailWord_3671404 prefixEnd_3671404 1885194928839658848665527 := by
  unfold tailWord_3671404
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953552395568904364114633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89271403194091872485486177 66953552395568904364114633)
  ·
    refine ⟨50215164296676678273085975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66953552395568904364114633 50215164296676678273085975)
    ·
      refine ⟨75322746445015017409628963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50215164296676678273085975 75322746445015017409628963)
      ·
        refine ⟨112984119667522526114443445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75322746445015017409628963 112984119667522526114443445)
        ·
          refine ⟨10592261218830236823229073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112984119667522526114443445 10592261218830236823229073)
          ·
            refine ⟨7944195914122677617421805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10592261218830236823229073 7944195914122677617421805)
            ·
              refine ⟨2979073467796004106533177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7944195914122677617421805 2979073467796004106533177)
              ·
                refine ⟨2234305100847003079899883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979073467796004106533177 2234305100847003079899883)
                ·
                  refine ⟨3351457651270504619849825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234305100847003079899883 3351457651270504619849825)
                  ·
                    refine ⟨2513593238452878464887369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351457651270504619849825 2513593238452878464887369)
                    ·
                      refine ⟨1885194928839658848665527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513593238452878464887369 1885194928839658848665527)
                      ·
                        rfl

theorem cell23_3671404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_3671404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671404 prefixEnd_3671404 := by exact prefixLift 3671404
  have htrace : WordTrace (prefixWord ++ tailWord_3671404) baseStart_3671404 baseEnd_3671404 := by
    simpa [prefixWord, tailWord_3671404, baseEnd_3671404] using wordTrace_append hprefix tailTrace_3671404
  have hstable : (prefixWord ++ tailWord_3671404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671404).length < 2 ^ (prefixWord ++ tailWord_3671404).sum := by decide
  have hdescent : baseEnd_3671404 < baseStart_3671404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671419 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 8]
def baseStart_3671419 : Nat := 118140960795 + 3671419 * 2 ^ 59
def prefixEnd_3671419 : Nat := 4983230072969 + 3 ^ 40 * 3671419 * 2
def baseEnd_3671419 : Nat := 628400877016492096659319

theorem tailTrace_3671419 : CollatzResearch.WordTrace tailWord_3671419 prefixEnd_3671419 628400877016492096659319 := by
  unfold tailWord_3671419
  simp only [CollatzResearch.WordTrace]
  refine ⟨133907651886083466290025311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89271767924055644193350207 133907651886083466290025311)
  ·
    refine ⟨200861477829125199435037967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133907651886083466290025311 200861477829125199435037967)
    ·
      refine ⟨301292216743687799152556951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200861477829125199435037967 301292216743687799152556951)
      ·
        refine ⟨451938325115531698728835427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301292216743687799152556951 451938325115531698728835427)
        ·
          refine ⟨677907487673297548093253141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451938325115531698728835427 677907487673297548093253141)
          ·
            refine ⟨31776913484685822566871241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 677907487673297548093253141 31776913484685822566871241)
            ·
              refine ⟨23832685113514366925153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31776913484685822566871241 23832685113514366925153431)
              ·
                refine ⟨35749027670271550387730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23832685113514366925153431 35749027670271550387730147)
                ·
                  refine ⟨53623541505407325581595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35749027670271550387730147 53623541505407325581595221)
                  ·
                    refine ⟨628400877016492096659319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53623541505407325581595221 628400877016492096659319)
                    ·
                      rfl

theorem cell23_3671419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_3671419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671419 prefixEnd_3671419 := by exact prefixLift 3671419
  have htrace : WordTrace (prefixWord ++ tailWord_3671419) baseStart_3671419 baseEnd_3671419 := by
    simpa [prefixWord, tailWord_3671419, baseEnd_3671419] using wordTrace_append hprefix tailTrace_3671419
  have hstable : (prefixWord ++ tailWord_3671419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671419).length < 2 ^ (prefixWord ++ tailWord_3671419).sum := by decide
  have hdescent : baseEnd_3671419 < baseStart_3671419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671454 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3671454 : Nat := 118140960795 + 3671454 * 2 ^ 59
def prefixEnd_3671454 : Nat := 4983230072969 + 3 ^ 40 * 3671454 * 2
def baseEnd_3671454 : Nat := 1885220602872383653040297

theorem tailTrace_3671454 : CollatzResearch.WordTrace tailWord_3671454 prefixEnd_3671454 1885220602872383653040297 := by
  unfold tailWord_3671454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16738616055119583408443677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89272618960637778178366277 16738616055119583408443677)
  ·
    refine ⟨6276981020669843778166379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16738616055119583408443677 6276981020669843778166379)
    ·
      refine ⟨9415471531004765667249569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6276981020669843778166379 9415471531004765667249569)
      ·
        refine ⟨7061603648253574250437177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9415471531004765667249569 7061603648253574250437177)
        ·
          refine ⟨5296202736190180687827883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061603648253574250437177 5296202736190180687827883)
          ·
            refine ⟨7944304104285271031741825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296202736190180687827883 7944304104285271031741825)
            ·
              refine ⟨5958228078213953273806369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944304104285271031741825 5958228078213953273806369)
              ·
                refine ⟨4468671058660464955354777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958228078213953273806369 4468671058660464955354777)
                ·
                  refine ⟨3351503293995348716516083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468671058660464955354777 3351503293995348716516083)
                  ·
                    refine ⟨5027254940993023074774125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3351503293995348716516083 5027254940993023074774125)
                    ·
                      refine ⟨1885220602872383653040297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027254940993023074774125 1885220602872383653040297)
                      ·
                        rfl

theorem cell23_3671454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3671454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671454 prefixEnd_3671454 := by exact prefixLift 3671454
  have htrace : WordTrace (prefixWord ++ tailWord_3671454) baseStart_3671454 baseEnd_3671454 := by
    simpa [prefixWord, tailWord_3671454, baseEnd_3671454] using wordTrace_append hprefix tailTrace_3671454
  have hstable : (prefixWord ++ tailWord_3671454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671454).length < 2 ^ (prefixWord ++ tailWord_3671454).sum := by decide
  have hdescent : baseEnd_3671454 < baseStart_3671454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671456 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3671456 : Nat := 118140960795 + 3671456 * 2 ^ 59
def prefixEnd_3671456 : Nat := 4983230072969 + 3 ^ 40 * 3671456 * 2
def baseEnd_3671456 : Nat := 1885221629833692645215287

theorem tailTrace_3671456 : CollatzResearch.WordTrace tailWord_3671456 prefixEnd_3671456 1885221629833692645215287 := by
  unfold tailWord_3671456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66954500693474710804561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89272667591299614406081481 66954500693474710804561111)
  ·
    refine ⟨100431751040212066206841667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66954500693474710804561111 100431751040212066206841667)
    ·
      refine ⟨150647626560318099310262501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100431751040212066206841667 150647626560318099310262501)
      ·
        refine ⟨28246429980059643620674219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150647626560318099310262501 28246429980059643620674219)
        ·
          refine ⟨42369644970089465431011329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28246429980059643620674219 42369644970089465431011329)
          ·
            refine ⟨31777233727567099073258497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42369644970089465431011329 31777233727567099073258497)
            ·
              refine ⟨23832925295675324304943873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31777233727567099073258497 23832925295675324304943873)
              ·
                refine ⟨17874693971756493228707905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23832925295675324304943873 17874693971756493228707905)
                ·
                  refine ⟨13406020478817369921530929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17874693971756493228707905 13406020478817369921530929)
                  ·
                    refine ⟨10054515359113027441148197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13406020478817369921530929 10054515359113027441148197)
                    ·
                      refine ⟨1885221629833692645215287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10054515359113027441148197 1885221629833692645215287)
                      ·
                        rfl

theorem cell23_3671456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3671456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671456 prefixEnd_3671456 := by exact prefixLift 3671456
  have htrace : WordTrace (prefixWord ++ tailWord_3671456) baseStart_3671456 baseEnd_3671456 := by
    simpa [prefixWord, tailWord_3671456, baseEnd_3671456] using wordTrace_append hprefix tailTrace_3671456
  have hstable : (prefixWord ++ tailWord_3671456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671456).length < 2 ^ (prefixWord ++ tailWord_3671456).sum := by decide
  have hdescent : baseEnd_3671456 < baseStart_3671456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671477 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_3671477 : Nat := 118140960795 + 3671477 * 2 ^ 59
def prefixEnd_3671477 : Nat := 4983230072969 + 3 ^ 40 * 3671477 * 2
def baseEnd_3671477 : Nat := 1885232412927437063052691

theorem tailTrace_3671477 : CollatzResearch.WordTrace tailWord_3671477 prefixEnd_3671477 1885232412927437063052691 := by
  unfold tailWord_3671477
  simp only [CollatzResearch.WordTrace]
  refine ⟨133909767319873342195636685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89273178213248894797091123 133909767319873342195636685)
  ·
    refine ⟨50216162744952503323363757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133909767319873342195636685 50216162744952503323363757)
    ·
      refine ⟨18831061029357188746261409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50216162744952503323363757 18831061029357188746261409)
      ·
        refine ⟨14123295772017891559696057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18831061029357188746261409 14123295772017891559696057)
        ·
          refine ⟨10592471829013418669772043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14123295772017891559696057 10592471829013418669772043)
          ·
            refine ⟨15888707743520128004658065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10592471829013418669772043 15888707743520128004658065)
            ·
              refine ⟨11916530807640096003493549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15888707743520128004658065 11916530807640096003493549)
              ·
                refine ⟨4468699052865036001310081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11916530807640096003493549 4468699052865036001310081)
                ·
                  refine ⟨3351524289648777000982561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468699052865036001310081 3351524289648777000982561)
                  ·
                    refine ⟨2513643217236582750736921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351524289648777000982561 2513643217236582750736921)
                    ·
                      refine ⟨1885232412927437063052691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513643217236582750736921 1885232412927437063052691)
                      ·
                        rfl

theorem cell23_3671477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_3671477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671477 prefixEnd_3671477 := by exact prefixLift 3671477
  have htrace : WordTrace (prefixWord ++ tailWord_3671477) baseStart_3671477 baseEnd_3671477 := by
    simpa [prefixWord, tailWord_3671477, baseEnd_3671477] using wordTrace_append hprefix tailTrace_3671477
  have hstable : (prefixWord ++ tailWord_3671477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671477).length < 2 ^ (prefixWord ++ tailWord_3671477).sum := by decide
  have hdescent : baseEnd_3671477 < baseStart_3671477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671496 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_3671496 : Nat := 118140960795 + 3671496 * 2 ^ 59
def prefixEnd_3671496 : Nat := 4983230072969 + 3 ^ 40 * 3671496 * 2
def baseEnd_3671496 : Nat := 628414056353290829571701

theorem tailTrace_3671496 : CollatzResearch.WordTrace tailWord_3671496 prefixEnd_3671496 628414056353290829571701 := by
  unfold tailWord_3671496
  simp only [CollatzResearch.WordTrace]
  refine ⟨66955230153402254220289171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89273640204536338960385561 66955230153402254220289171)
  ·
    refine ⟨100432845230103381330433757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66955230153402254220289171 100432845230103381330433757)
    ·
      refine ⟨37662316961288767998912659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100432845230103381330433757 37662316961288767998912659)
      ·
        refine ⟨56493475441933151998368989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37662316961288767998912659 56493475441933151998368989)
        ·
          refine ⟨21185053290724931999388371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56493475441933151998368989 21185053290724931999388371)
          ·
            refine ⟨31777579936087397999082557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21185053290724931999388371 31777579936087397999082557)
            ·
              refine ⟨11916592476032774249655959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31777579936087397999082557 11916592476032774249655959)
              ·
                refine ⟨17874888714049161374483939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916592476032774249655959 17874888714049161374483939)
                ·
                  refine ⟨26812333071073742061725909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17874888714049161374483939 26812333071073742061725909)
                  ·
                    refine ⟨628414056353290829571701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26812333071073742061725909 628414056353290829571701)
                    ·
                      rfl

theorem cell23_3671496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_3671496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671496 prefixEnd_3671496 := by exact prefixLift 3671496
  have htrace : WordTrace (prefixWord ++ tailWord_3671496) baseStart_3671496 baseEnd_3671496 := by
    simpa [prefixWord, tailWord_3671496, baseEnd_3671496] using wordTrace_append hprefix tailTrace_3671496
  have hstable : (prefixWord ++ tailWord_3671496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671496).length < 2 ^ (prefixWord ++ tailWord_3671496).sum := by decide
  have hdescent : baseEnd_3671496 < baseStart_3671496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671500 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 5]
def baseStart_3671500 : Nat := 118140960795 + 3671500 * 2 ^ 59
def prefixEnd_3671500 : Nat := 4983230072969 + 3 ^ 40 * 3671500 * 2
def baseEnd_3671500 : Nat := 209471580331387830340565

theorem tailTrace_3671500 : CollatzResearch.WordTrace tailWord_3671500 prefixEnd_3671500 209471580331387830340565 := by
  unfold tailWord_3671500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66955303099395008561861977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89273737465860011415815969 66955303099395008561861977)
  ·
    refine ⟨50216477324546256421396483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66955303099395008561861977 50216477324546256421396483)
    ·
      refine ⟨75324715986819384632094725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50216477324546256421396483 75324715986819384632094725)
      ·
        refine ⟨14123384247528634618517761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75324715986819384632094725 14123384247528634618517761)
        ·
          refine ⟨10592538185646475963888321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14123384247528634618517761 10592538185646475963888321)
          ·
            refine ⟨7944403639234856972916241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10592538185646475963888321 7944403639234856972916241)
            ·
              refine ⟨5958302729426142729687181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944403639234856972916241 5958302729426142729687181)
              ·
                refine ⟨2234363523534803523632693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958302729426142729687181 2234363523534803523632693)
                ·
                  refine ⟨209471580331387830340565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234363523534803523632693 209471580331387830340565)
                  ·
                    rfl

theorem cell23_3671500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_3671500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671500 prefixEnd_3671500 := by exact prefixLift 3671500
  have htrace : WordTrace (prefixWord ++ tailWord_3671500) baseStart_3671500 baseEnd_3671500 := by
    simpa [prefixWord, tailWord_3671500, baseEnd_3671500] using wordTrace_append hprefix tailTrace_3671500
  have hstable : (prefixWord ++ tailWord_3671500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671500).length < 2 ^ (prefixWord ++ tailWord_3671500).sum := by decide
  have hdescent : baseEnd_3671500 < baseStart_3671500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671510 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3671510 : Nat := 118140960795 + 3671510 * 2 ^ 59
def prefixEnd_3671510 : Nat := 4983230072969 + 3 ^ 40 * 3671510 * 2
def baseEnd_3671510 : Nat := 1885249357789035433940039

theorem tailTrace_3671510 : CollatzResearch.WordTrace tailWord_3671510 prefixEnd_3671510 1885249357789035433940039 := by
  unfold tailWord_3671510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369435683047111801974249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89273980619169192554391989 8369435683047111801974249)
  ·
    refine ⟨6277076762285333851480687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8369435683047111801974249 6277076762285333851480687)
    ·
      refine ⟨9415615143428000777221031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277076762285333851480687 9415615143428000777221031)
      ·
        refine ⟨14123422715142001165831547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9415615143428000777221031 14123422715142001165831547)
        ·
          refine ⟨21185134072713001748747321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14123422715142001165831547 21185134072713001748747321)
          ·
            refine ⟨15888850554534751311560491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21185134072713001748747321 15888850554534751311560491)
            ·
              refine ⟨23833275831802126967340737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15888850554534751311560491 23833275831802126967340737)
              ·
                refine ⟨17874956873851595225505553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23833275831802126967340737 17874956873851595225505553)
                ·
                  refine ⟨13406217655388696419129165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17874956873851595225505553 13406217655388696419129165)
                  ·
                    refine ⟨5027331620770761157173437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13406217655388696419129165 5027331620770761157173437)
                    ·
                      refine ⟨1885249357789035433940039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027331620770761157173437 1885249357789035433940039)
                      ·
                        rfl

theorem cell23_3671510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3671510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671510 prefixEnd_3671510 := by exact prefixLift 3671510
  have htrace : WordTrace (prefixWord ++ tailWord_3671510) baseStart_3671510 baseEnd_3671510 := by
    simpa [prefixWord, tailWord_3671510, baseEnd_3671510] using wordTrace_append hprefix tailTrace_3671510
  have hstable : (prefixWord ++ tailWord_3671510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671510).length < 2 ^ (prefixWord ++ tailWord_3671510).sum := by decide
  have hdescent : baseEnd_3671510 < baseStart_3671510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671546 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_3671546 : Nat := 118140960795 + 3671546 * 2 ^ 59
def prefixEnd_3671546 : Nat := 4983230072969 + 3 ^ 40 * 3671546 * 2
def baseEnd_3671546 : Nat := 1885267843092597293089873

theorem tailTrace_3671546 : CollatzResearch.WordTrace tailWord_3671546 prefixEnd_3671546 1885267843092597293089873 := by
  unfold tailWord_3671546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478070989155841744974623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89274855971082244653265661 33478070989155841744974623)
  ·
    refine ⟨50217106483733762617461935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33478070989155841744974623 50217106483733762617461935)
    ·
      refine ⟨75325659725600643926192903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50217106483733762617461935 75325659725600643926192903)
      ·
        refine ⟨112988489588400965889289355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75325659725600643926192903 112988489588400965889289355)
        ·
          refine ⟨169482734382601448833934033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112988489588400965889289355 169482734382601448833934033)
          ·
            refine ⟨127112050786951086625450525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169482734382601448833934033 127112050786951086625450525)
            ·
              refine ⟨47667019045106657484543947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127112050786951086625450525 47667019045106657484543947)
              ·
                refine ⟨71500528567659986226815921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47667019045106657484543947 71500528567659986226815921)
                ·
                  refine ⟨53625396425744989670111941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71500528567659986226815921 53625396425744989670111941)
                  ·
                    refine ⟨10054761829827185563145989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53625396425744989670111941 10054761829827185563145989)
                    ·
                      refine ⟨1885267843092597293089873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10054761829827185563145989 1885267843092597293089873)
                      ·
                        rfl

theorem cell23_3671546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_3671546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671546 prefixEnd_3671546 := by exact prefixLift 3671546
  have htrace : WordTrace (prefixWord ++ tailWord_3671546) baseStart_3671546 baseEnd_3671546 := by
    simpa [prefixWord, tailWord_3671546, baseEnd_3671546] using wordTrace_append hprefix tailTrace_3671546
  have hstable : (prefixWord ++ tailWord_3671546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671546).length < 2 ^ (prefixWord ++ tailWord_3671546).sum := by decide
  have hdescent : baseEnd_3671546 < baseStart_3671546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671603 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 3, 5]
def baseStart_3671603 : Nat := 118140960795 + 3671603 * 2 ^ 59
def prefixEnd_3671603 : Nat := 4983230072969 + 3 ^ 40 * 3671603 * 2
def baseEnd_3671603 : Nat := 628432370496634523359037

theorem tailTrace_3671603 : CollatzResearch.WordTrace tailWord_3671603 prefixEnd_3671603 628432370496634523359037 := by
  unfold tailWord_3671603
  simp only [CollatzResearch.WordTrace]
  refine ⟨133914362917416865714723463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89276241944944577143148975 133914362917416865714723463)
  ·
    refine ⟨200871544376125298572085195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133914362917416865714723463 200871544376125298572085195)
    ·
      refine ⟨301307316564187947858127793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200871544376125298572085195 301307316564187947858127793)
      ·
        refine ⟨225980487423140960893595845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301307316564187947858127793 225980487423140960893595845)
        ·
          refine ⟨42371341391838930167549221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225980487423140960893595845 42371341391838930167549221)
          ·
            refine ⟨7944626510969799406415479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42371341391838930167549221 7944626510969799406415479)
            ·
              refine ⟨11916939766454699109623219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944626510969799406415479 11916939766454699109623219)
              ·
                refine ⟨17875409649682048664434829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916939766454699109623219 17875409649682048664434829)
                ·
                  refine ⟨6703278618630768249163061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17875409649682048664434829 6703278618630768249163061)
                  ·
                    refine ⟨628432370496634523359037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6703278618630768249163061 628432370496634523359037)
                    ·
                      rfl

theorem cell23_3671603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].length) (baseStart_3671603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671603 prefixEnd_3671603 := by exact prefixLift 3671603
  have htrace : WordTrace (prefixWord ++ tailWord_3671603) baseStart_3671603 baseEnd_3671603 := by
    simpa [prefixWord, tailWord_3671603, baseEnd_3671603] using wordTrace_append hprefix tailTrace_3671603
  have hstable : (prefixWord ++ tailWord_3671603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671603).length < 2 ^ (prefixWord ++ tailWord_3671603).sum := by decide
  have hdescent : baseEnd_3671603 < baseStart_3671603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671634 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_3671634 : Nat := 118140960795 + 3671634 * 2 ^ 59
def prefixEnd_3671634 : Nat := 4983230072969 + 3 ^ 40 * 3671634 * 2
def baseEnd_3671634 : Nat := 1885313029390192948789469

theorem tailTrace_3671634 : CollatzResearch.WordTrace tailWord_3671634 prefixEnd_3671634 1885313029390192948789469 := by
  unfold tailWord_3671634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478873395076139502275489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89276995720203038672734637 33478873395076139502275489)
  ·
    refine ⟨25109155046307104626706617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33478873395076139502275489 25109155046307104626706617)
    ·
      refine ⟨18831866284730328470029963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25109155046307104626706617 18831866284730328470029963)
      ·
        refine ⟨28247799427095492705044945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831866284730328470029963 28247799427095492705044945)
        ·
          refine ⟨21185849570321619528783709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28247799427095492705044945 21185849570321619528783709)
          ·
            refine ⟨7944693588870607323293891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21185849570321619528783709 7944693588870607323293891)
            ·
              refine ⟨11917040383305910984940837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944693588870607323293891 11917040383305910984940837)
              ·
                refine ⟨2234445071869858309676407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11917040383305910984940837 2234445071869858309676407)
                ·
                  refine ⟨3351667607804787464514611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234445071869858309676407 3351667607804787464514611)
                  ·
                    refine ⟨5027501411707181196771917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3351667607804787464514611 5027501411707181196771917)
                    ·
                      refine ⟨1885313029390192948789469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027501411707181196771917 1885313029390192948789469)
                      ·
                        rfl

theorem cell23_3671634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_3671634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671634 prefixEnd_3671634 := by exact prefixLift 3671634
  have htrace : WordTrace (prefixWord ++ tailWord_3671634) baseStart_3671634 baseEnd_3671634 := by
    simpa [prefixWord, tailWord_3671634, baseEnd_3671634] using wordTrace_append hprefix tailTrace_3671634
  have hstable : (prefixWord ++ tailWord_3671634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671634).length < 2 ^ (prefixWord ++ tailWord_3671634).sum := by decide
  have hdescent : baseEnd_3671634 < baseStart_3671634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671660 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_3671660 : Nat := 118140960795 + 3671660 * 2 ^ 59
def prefixEnd_3671660 : Nat := 4983230072969 + 3 ^ 40 * 3671660 * 2
def baseEnd_3671660 : Nat := 1885326379887209847064349

theorem tailTrace_3671660 : CollatzResearch.WordTrace tailWord_3671660 prefixEnd_3671660 1885326379887209847064349 := by
  unfold tailWord_3671660
  simp only [CollatzResearch.WordTrace]
  refine ⟨66958220939105182224774217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89277627918806909633032289 66958220939105182224774217)
  ·
    refine ⟨50218665704328886668580663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66958220939105182224774217 50218665704328886668580663)
    ·
      refine ⟨75327998556493330002870995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50218665704328886668580663 75327998556493330002870995)
      ·
        refine ⟨112991997834739995004306493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75327998556493330002870995 112991997834739995004306493)
        ·
          refine ⟨42371999188027498126614935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112991997834739995004306493 42371999188027498126614935)
          ·
            refine ⟨63557998782041247189922403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42371999188027498126614935 63557998782041247189922403)
            ·
              refine ⟨95336998173061870784883605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63557998782041247189922403 95336998173061870784883605)
              ·
                refine ⟨4468921789362275193041419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95336998173061870784883605 4468921789362275193041419)
                ·
                  refine ⟨6703382684043412789562129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468921789362275193041419 6703382684043412789562129)
                  ·
                    refine ⟨5027537013032559592171597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6703382684043412789562129 5027537013032559592171597)
                    ·
                      refine ⟨1885326379887209847064349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027537013032559592171597 1885326379887209847064349)
                      ·
                        rfl

theorem cell23_3671660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_3671660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671660 prefixEnd_3671660 := by exact prefixLift 3671660
  have htrace : WordTrace (prefixWord ++ tailWord_3671660) baseStart_3671660 baseEnd_3671660 := by
    simpa [prefixWord, tailWord_3671660, baseEnd_3671660] using wordTrace_append hprefix tailTrace_3671660
  have hstable : (prefixWord ++ tailWord_3671660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671660).length < 2 ^ (prefixWord ++ tailWord_3671660).sum := by decide
  have hdescent : baseEnd_3671660 < baseStart_3671660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671661 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_3671661 : Nat := 118140960795 + 3671661 * 2 ^ 59
def prefixEnd_3671661 : Nat := 4983230072969 + 3 ^ 40 * 3671661 * 2
def baseEnd_3671661 : Nat := 1885326893367864343151845

theorem tailTrace_3671661 : CollatzResearch.WordTrace tailWord_3671661 prefixEnd_3671661 1885326893367864343151845 := by
  unfold tailWord_3671661
  simp only [CollatzResearch.WordTrace]
  refine ⟨133916478351206741620334837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89277652234137827746889891 133916478351206741620334837)
  ·
    refine ⟨12554669845425632026906391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133916478351206741620334837 12554669845425632026906391)
    ·
      refine ⟨18832004768138448040359587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554669845425632026906391 18832004768138448040359587)
      ·
        refine ⟨28248007152207672060539381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18832004768138448040359587 28248007152207672060539381)
        ·
          refine ⟨2648250670519469255675567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28248007152207672060539381 2648250670519469255675567)
          ·
            refine ⟨3972376005779203883513351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648250670519469255675567 3972376005779203883513351)
            ·
              refine ⟨5958564008668805825270027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972376005779203883513351 5958564008668805825270027)
              ·
                refine ⟨8937846013003208737905041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958564008668805825270027 8937846013003208737905041)
                ·
                  refine ⟨6703384509752406553428781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8937846013003208737905041 6703384509752406553428781)
                  ·
                    refine ⟨2513769191157152457535793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6703384509752406553428781 2513769191157152457535793)
                    ·
                      refine ⟨1885326893367864343151845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513769191157152457535793 1885326893367864343151845)
                      ·
                        rfl

theorem cell23_3671661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_3671661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671661 prefixEnd_3671661 := by exact prefixLift 3671661
  have htrace : WordTrace (prefixWord ++ tailWord_3671661) baseStart_3671661 baseEnd_3671661 := by
    simpa [prefixWord, tailWord_3671661, baseEnd_3671661] using wordTrace_append hprefix tailTrace_3671661
  have hstable : (prefixWord ++ tailWord_3671661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671661).length < 2 ^ (prefixWord ++ tailWord_3671661).sum := by decide
  have hdescent : baseEnd_3671661 < baseStart_3671661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671677 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_3671677 : Nat := 118140960795 + 3671677 * 2 ^ 59
def prefixEnd_3671677 : Nat := 4983230072969 + 3 ^ 40 * 3671677 * 2
def baseEnd_3671677 : Nat := 1885335109058336280551771

theorem tailTrace_3671677 : CollatzResearch.WordTrace tailWord_3671677 prefixEnd_3671677 1885335109058336280551771 := by
  unfold tailWord_3671677
  simp only [CollatzResearch.WordTrace]
  refine ⟨133917061919148776352917285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89278041279432517568611523 133917061919148776352917285)
  ·
    refine ⟨25109449109840395566171991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133917061919148776352917285 25109449109840395566171991)
    ·
      refine ⟨37664173664760593349257987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25109449109840395566171991 37664173664760593349257987)
      ·
        refine ⟨56496260497140890023886981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37664173664760593349257987 56496260497140890023886981)
        ·
          refine ⟨10593048843213916879478809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56496260497140890023886981 10593048843213916879478809)
          ·
            refine ⟨7944786632410437659609107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10593048843213916879478809 7944786632410437659609107)
            ·
              refine ⟨11917179948615656489413661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944786632410437659609107 11917179948615656489413661)
              ·
                refine ⟨4468942480730871183530123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11917179948615656489413661 4468942480730871183530123)
                ·
                  refine ⟨6703413721096306775295185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468942480730871183530123 6703413721096306775295185)
                  ·
                    refine ⟨5027560290822230081471389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6703413721096306775295185 5027560290822230081471389)
                    ·
                      refine ⟨1885335109058336280551771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5027560290822230081471389 1885335109058336280551771)
                      ·
                        rfl

theorem cell23_3671677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_3671677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671677 prefixEnd_3671677 := by exact prefixLift 3671677
  have htrace : WordTrace (prefixWord ++ tailWord_3671677) baseStart_3671677 baseEnd_3671677 := by
    simpa [prefixWord, tailWord_3671677, baseEnd_3671677] using wordTrace_append hprefix tailTrace_3671677
  have hstable : (prefixWord ++ tailWord_3671677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671677).length < 2 ^ (prefixWord ++ tailWord_3671677).sum := by decide
  have hdescent : baseEnd_3671677 < baseStart_3671677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671684 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_3671684 : Nat := 118140960795 + 3671684 * 2 ^ 59
def prefixEnd_3671684 : Nat := 4983230072969 + 3 ^ 40 * 3671684 * 2
def baseEnd_3671684 : Nat := 628446234474305917721413

theorem tailTrace_3671684 : CollatzResearch.WordTrace tailWord_3671684 prefixEnd_3671684 628446234474305917721413 := by
  unfold tailWord_3671684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66958658615061708274211053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89278211486748944365614737 66958658615061708274211053)
  ·
    refine ⟨25109496980648140602829145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66958658615061708274211053 25109496980648140602829145)
    ·
      refine ⟨18832122735486105452121859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25109496980648140602829145 18832122735486105452121859)
      ·
        refine ⟨28248184103229158178182789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18832122735486105452121859 28248184103229158178182789)
        ·
          refine ⟨5296534519355467158409273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28248184103229158178182789 5296534519355467158409273)
          ·
            refine ⟨3972400889516600368806955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5296534519355467158409273 3972400889516600368806955)
            ·
              refine ⟨5958601334274900553210433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972400889516600368806955 5958601334274900553210433)
              ·
                refine ⟨4468951000706175414907825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958601334274900553210433 4468951000706175414907825)
                ·
                  refine ⟨3351713250529631561180869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468951000706175414907825 3351713250529631561180869)
                  ·
                    refine ⟨628446234474305917721413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351713250529631561180869 628446234474305917721413)
                    ·
                      rfl

theorem cell23_3671684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_3671684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671684 prefixEnd_3671684 := by exact prefixLift 3671684
  have htrace : WordTrace (prefixWord ++ tailWord_3671684) baseStart_3671684 baseEnd_3671684 := by
    simpa [prefixWord, tailWord_3671684, baseEnd_3671684] using wordTrace_append hprefix tailTrace_3671684
  have hstable : (prefixWord ++ tailWord_3671684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671684).length < 2 ^ (prefixWord ++ tailWord_3671684).sum := by decide
  have hdescent : baseEnd_3671684 < baseStart_3671684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671714 : List Nat := [3, 3, 1, 4, 1, 2, 2, 7]
def baseStart_3671714 : Nat := 118140960795 + 3671714 * 2 ^ 59
def prefixEnd_3671714 : Nat := 4983230072969 + 3 ^ 40 * 3671714 * 2
def baseEnd_3671714 : Nat := 69827929920094542066263

theorem tailTrace_3671714 : CollatzResearch.WordTrace tailWord_3671714 prefixEnd_3671714 69827929920094542066263 := by
  unfold tailWord_3671714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33479602855003682918003549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89278940946676487781342797 33479602855003682918003549)
  ·
    refine ⟨12554851070626381094251331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33479602855003682918003549 12554851070626381094251331)
    ·
      refine ⟨18832276605939571641376997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554851070626381094251331 18832276605939571641376997)
      ·
        refine ⟨3531051863613669682758187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18832276605939571641376997 3531051863613669682758187)
        ·
          refine ⟨5296577795420504524137281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531051863613669682758187 5296577795420504524137281)
          ·
            refine ⟨3972433346565378393102961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5296577795420504524137281 3972433346565378393102961)
            ·
              refine ⟨2979325009924033794827221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972433346565378393102961 2979325009924033794827221)
              ·
                refine ⟨69827929920094542066263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2979325009924033794827221 69827929920094542066263)
                ·
                  rfl

theorem cell23_3671714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_3671714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671714 prefixEnd_3671714 := by exact prefixLift 3671714
  have htrace : WordTrace (prefixWord ++ tailWord_3671714) baseStart_3671714 baseEnd_3671714 := by
    simpa [prefixWord, tailWord_3671714, baseEnd_3671714] using wordTrace_append hprefix tailTrace_3671714
  have hstable : (prefixWord ++ tailWord_3671714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671714).length < 2 ^ (prefixWord ++ tailWord_3671714).sum := by decide
  have hdescent : baseEnd_3671714 < baseStart_3671714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671717 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_3671717 : Nat := 118140960795 + 3671717 * 2 ^ 59
def prefixEnd_3671717 : Nat := 4983230072969 + 3 ^ 40 * 3671717 * 2
def baseEnd_3671717 : Nat := 1885355648284516124051587

theorem tailTrace_3671717 : CollatzResearch.WordTrace tailWord_3671717 prefixEnd_3671717 1885355648284516124051587 := by
  unfold tailWord_3671717
  simp only [CollatzResearch.WordTrace]
  refine ⟨133918520839003863184373405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89279013892669242122915603 133918520839003863184373405)
  ·
    refine ⟨50219445314626448694140027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133918520839003863184373405 50219445314626448694140027)
    ·
      refine ⟨75329167971939673041210041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50219445314626448694140027 75329167971939673041210041)
      ·
        refine ⟨56496875978954754780907531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75329167971939673041210041 56496875978954754780907531)
        ·
          refine ⟨84745313968432132171361297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56496875978954754780907531 84745313968432132171361297)
          ·
            refine ⟨63558985476324099128520973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84745313968432132171361297 63558985476324099128520973)
            ·
              refine ⟨23834619553621537173195365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63558985476324099128520973 23834619553621537173195365)
              ·
                refine ⟨4468991166304038219974131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23834619553621537173195365 4468991166304038219974131)
                ·
                  refine ⟨6703486749456057329961197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468991166304038219974131 6703486749456057329961197)
                  ·
                    refine ⟨2513807531046021498735449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6703486749456057329961197 2513807531046021498735449)
                    ·
                      refine ⟨1885355648284516124051587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513807531046021498735449 1885355648284516124051587)
                      ·
                        rfl

theorem cell23_3671717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_3671717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671717 prefixEnd_3671717 := by exact prefixLift 3671717
  have htrace : WordTrace (prefixWord ++ tailWord_3671717) baseStart_3671717 baseEnd_3671717 := by
    simpa [prefixWord, tailWord_3671717, baseEnd_3671717] using wordTrace_append hprefix tailTrace_3671717
  have hstable : (prefixWord ++ tailWord_3671717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671717).length < 2 ^ (prefixWord ++ tailWord_3671717).sum := by decide
  have hdescent : baseEnd_3671717 < baseStart_3671717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671813 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3671813 : Nat := 118140960795 + 3671813 * 2 ^ 59
def prefixEnd_3671813 : Nat := 4983230072969 + 3 ^ 40 * 3671813 * 2
def baseEnd_3671813 : Nat := 628468314142449249483715

theorem tailTrace_3671813 : CollatzResearch.WordTrace tailWord_3671813 prefixEnd_3671813 628468314142449249483715 := by
  unfold tailWord_3671813
  simp only [CollatzResearch.WordTrace]
  refine ⟨133922022246656071579868093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89281348164437381053245395 133922022246656071579868093)
  ·
    refine ⟨50220758342496026842450535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133922022246656071579868093 50220758342496026842450535)
    ·
      refine ⟨75331137513744040263675803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50220758342496026842450535 75331137513744040263675803)
      ·
        refine ⟨112996706270616060395513705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75331137513744040263675803 112996706270616060395513705)
        ·
          refine ⟨84747529702962045296635279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112996706270616060395513705 84747529702962045296635279)
          ·
            refine ⟨127121294554443067944952919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84747529702962045296635279 127121294554443067944952919)
            ·
              refine ⟨190681941831664601917429379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127121294554443067944952919 190681941831664601917429379)
              ·
                refine ⟨286022912747496902876144069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190681941831664601917429379 286022912747496902876144069)
                ·
                  refine ⟨53629296140155669289277013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286022912747496902876144069 53629296140155669289277013)
                  ·
                    refine ⟨628468314142449249483715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53629296140155669289277013 628468314142449249483715)
                    ·
                      rfl

theorem cell23_3671813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3671813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671813 prefixEnd_3671813 := by exact prefixLift 3671813
  have htrace : WordTrace (prefixWord ++ tailWord_3671813) baseStart_3671813 baseEnd_3671813 := by
    simpa [prefixWord, tailWord_3671813, baseEnd_3671813] using wordTrace_append hprefix tailTrace_3671813
  have hstable : (prefixWord ++ tailWord_3671813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671813).length < 2 ^ (prefixWord ++ tailWord_3671813).sum := by decide
  have hdescent : baseEnd_3671813 < baseStart_3671813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671820 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3671820 : Nat := 118140960795 + 3671820 * 2 ^ 59
def prefixEnd_3671820 : Nat := 4983230072969 + 3 ^ 40 * 3671820 * 2
def baseEnd_3671820 : Nat := 1885408536791929221063613

theorem tailTrace_3671820 : CollatzResearch.WordTrace tailWord_3671820 prefixEnd_3671820 1885408536791929221063613 := by
  unfold tailWord_3671820
  simp only [CollatzResearch.WordTrace]
  refine ⟨66961138778815355887686457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89281518371753807850248609 66961138778815355887686457)
  ·
    refine ⟨50220854084111516915764843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66961138778815355887686457 50220854084111516915764843)
    ·
      refine ⟨75331281126167275373647265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50220854084111516915764843 75331281126167275373647265)
      ·
        refine ⟨56498460844625456530235449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75331281126167275373647265 56498460844625456530235449)
        ·
          refine ⟨42373845633469092397676587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56498460844625456530235449 42373845633469092397676587)
          ·
            refine ⟨63560768450203638596514881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42373845633469092397676587 63560768450203638596514881)
            ·
              refine ⟨47670576337652728947386161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63560768450203638596514881 47670576337652728947386161)
              ·
                refine ⟨35752932253239546710539621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47670576337652728947386161 35752932253239546710539621)
                ·
                  refine ⟨6703674797482415008226179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35752932253239546710539621 6703674797482415008226179)
                  ·
                    refine ⟨10055512196223622512339269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6703674797482415008226179 10055512196223622512339269)
                    ·
                      refine ⟨1885408536791929221063613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10055512196223622512339269 1885408536791929221063613)
                      ·
                        rfl

theorem cell23_3671820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3671820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671820 prefixEnd_3671820 := by exact prefixLift 3671820
  have htrace : WordTrace (prefixWord ++ tailWord_3671820) baseStart_3671820 baseEnd_3671820 := by
    simpa [prefixWord, tailWord_3671820, baseEnd_3671820] using wordTrace_append hprefix tailTrace_3671820
  have hstable : (prefixWord ++ tailWord_3671820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671820).length < 2 ^ (prefixWord ++ tailWord_3671820).sum := by decide
  have hdescent : baseEnd_3671820 < baseStart_3671820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671838 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3671838 : Nat := 118140960795 + 3671838 * 2 ^ 59
def prefixEnd_3671838 : Nat := 4983230072969 + 3 ^ 40 * 3671838 * 2
def baseEnd_3671838 : Nat := 209490864382634461182059

theorem tailTrace_3671838 : CollatzResearch.WordTrace tailWord_3671838 prefixEnd_3671838 209490864382634461182059 := by
  unfold tailWord_3671838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740366758945687606191021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89281956047710333899685445 16740366758945687606191021)
  ·
    refine ⟨6277637534604632852321633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16740366758945687606191021 6277637534604632852321633)
    ·
      refine ⟨4708228150953474639241225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6277637534604632852321633 4708228150953474639241225)
      ·
        refine ⟨3531171113215105979430919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708228150953474639241225 3531171113215105979430919)
        ·
          refine ⟨5296756669822658969146379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531171113215105979430919 5296756669822658969146379)
          ·
            refine ⟨7945135004733988453719569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296756669822658969146379 7945135004733988453719569)
            ·
              refine ⟨5958851253550491340289677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945135004733988453719569 5958851253550491340289677)
              ·
                refine ⟨2234569220081434252608629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958851253550491340289677 2234569220081434252608629)
                ·
                  refine ⟨209490864382634461182059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234569220081434252608629 209490864382634461182059)
                  ·
                    rfl

theorem cell23_3671838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3671838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671838 prefixEnd_3671838 := by exact prefixLift 3671838
  have htrace : WordTrace (prefixWord ++ tailWord_3671838) baseStart_3671838 baseEnd_3671838 := by
    simpa [prefixWord, tailWord_3671838, baseEnd_3671838] using wordTrace_append hprefix tailTrace_3671838
  have hstable : (prefixWord ++ tailWord_3671838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671838).length < 2 ^ (prefixWord ++ tailWord_3671838).sum := by decide
  have hdescent : baseEnd_3671838 < baseStart_3671838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671864 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 1, 4]
def baseStart_3671864 : Nat := 118140960795 + 3671864 * 2 ^ 59
def prefixEnd_3671864 : Nat := 4983230072969 + 3 ^ 40 * 3671864 * 2
def baseEnd_3671864 : Nat := 628477043313575682971137

theorem tailTrace_3671864 : CollatzResearch.WordTrace tailWord_3671864 prefixEnd_3671864 628477043313575682971137 := by
  unfold tailWord_3671864
  simp only [CollatzResearch.WordTrace]
  refine ⟨66961941184735653644987323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89282588246314204859983097 66961941184735653644987323)
  ·
    refine ⟨100442911777103480467480985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66961941184735653644987323 100442911777103480467480985)
    ·
      refine ⟨75332183832827610350610739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100442911777103480467480985 75332183832827610350610739)
      ·
        refine ⟨112998275749241415525916109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75332183832827610350610739 112998275749241415525916109)
        ·
          refine ⟨42374353405965530822218541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112998275749241415525916109 42374353405965530822218541)
          ·
            refine ⟨15890382527237074058331953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42374353405965530822218541 15890382527237074058331953)
            ·
              refine ⟨11917786895427805543748965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15890382527237074058331953 11917786895427805543748965)
              ·
                refine ⟨2234585042892713539452931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11917786895427805543748965 2234585042892713539452931)
                ·
                  refine ⟨3351877564339070309179397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234585042892713539452931 3351877564339070309179397)
                  ·
                    refine ⟨628477043313575682971137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351877564339070309179397 628477043313575682971137)
                    ·
                      rfl

theorem cell23_3671864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_3671864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671864 prefixEnd_3671864 := by exact prefixLift 3671864
  have htrace : WordTrace (prefixWord ++ tailWord_3671864) baseStart_3671864 baseEnd_3671864 := by
    simpa [prefixWord, tailWord_3671864, baseEnd_3671864] using wordTrace_append hprefix tailTrace_3671864
  have hstable : (prefixWord ++ tailWord_3671864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671864).length < 2 ^ (prefixWord ++ tailWord_3671864).sum := by decide
  have hdescent : baseEnd_3671864 < baseStart_3671864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671877 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 6]
def baseStart_3671877 : Nat := 118140960795 + 3671877 * 2 ^ 59
def prefixEnd_3671877 : Nat := 4983230072969 + 3 ^ 40 * 3671877 * 2
def baseEnd_3671877 : Nat := 209493089465470610894539

theorem tailTrace_3671877 : CollatzResearch.WordTrace tailWord_3671877 prefixEnd_3671877 209493089465470610894539 := by
  unfold tailWord_3671877
  simp only [CollatzResearch.WordTrace]
  refine ⟨133924356518424210510197885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89282904345616140340131923 133924356518424210510197885)
  ·
    refine ⟨50221633694409078941324207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133924356518424210510197885 50221633694409078941324207)
    ·
      refine ⟨75332450541613618411986311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50221633694409078941324207 75332450541613618411986311)
      ·
        refine ⟨112998675812420427617979467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75332450541613618411986311 112998675812420427617979467)
        ·
          refine ⟨169498013718630641426969201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112998675812420427617979467 169498013718630641426969201)
          ·
            refine ⟨127123510288972981070226901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169498013718630641426969201 127123510288972981070226901)
            ·
              refine ⟨2979457272397804243833443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127123510288972981070226901 2979457272397804243833443)
              ·
                refine ⟨4469185908596706365750165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979457272397804243833443 4469185908596706365750165)
                ·
                  refine ⟨209493089465470610894539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4469185908596706365750165 209493089465470610894539)
                  ·
                    rfl

theorem cell23_3671877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_3671877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671877 prefixEnd_3671877 := by exact prefixLift 3671877
  have htrace : WordTrace (prefixWord ++ tailWord_3671877) baseStart_3671877 baseEnd_3671877 := by
    simpa [prefixWord, tailWord_3671877, baseEnd_3671877] using wordTrace_append hprefix tailTrace_3671877
  have hstable : (prefixWord ++ tailWord_3671877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671877).length < 2 ^ (prefixWord ++ tailWord_3671877).sum := by decide
  have hdescent : baseEnd_3671877 < baseStart_3671877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671897 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 5, 2]
def baseStart_3671897 : Nat := 118140960795 + 3671897 * 2 ^ 59
def prefixEnd_3671897 : Nat := 4983230072969 + 3 ^ 40 * 3671897 * 2
def baseEnd_3671897 : Nat := 1885448074802325419800759

theorem tailTrace_3671897 : CollatzResearch.WordTrace tailWord_3671897 prefixEnd_3671897 1885448074802325419800759 := by
  unfold tailWord_3671897
  simp only [CollatzResearch.WordTrace]
  refine ⟨133925085978351753925925945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89283390652234502617283963 133925085978351753925925945)
  ·
    refine ⟨100443814483763815444444459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133925085978351753925925945 100443814483763815444444459)
    ·
      refine ⟨150665721725645723166666689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100443814483763815444444459 150665721725645723166666689)
      ·
        refine ⟨112999291294234292375000017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150665721725645723166666689 112999291294234292375000017)
        ·
          refine ⟨84749468470675719281250013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112999291294234292375000017 84749468470675719281250013)
          ·
            refine ⟨31781050676503394730468755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84749468470675719281250013 31781050676503394730468755)
            ·
              refine ⟨47671576014755092095703133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31781050676503394730468755 47671576014755092095703133)
              ·
                refine ⟨17876841005533159535888675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47671576014755092095703133 17876841005533159535888675)
                ·
                  refine ⟨26815261508299739303833013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17876841005533159535888675 26815261508299739303833013)
                  ·
                    refine ⟨2513930766403100559734345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26815261508299739303833013 2513930766403100559734345)
                    ·
                      refine ⟨1885448074802325419800759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2513930766403100559734345 1885448074802325419800759)
                      ·
                        rfl

theorem cell23_3671897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_3671897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671897 prefixEnd_3671897 := by exact prefixLift 3671897
  have htrace : WordTrace (prefixWord ++ tailWord_3671897) baseStart_3671897 baseEnd_3671897 := by
    simpa [prefixWord, tailWord_3671897, baseEnd_3671897] using wordTrace_append hprefix tailTrace_3671897
  have hstable : (prefixWord ++ tailWord_3671897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671897).length < 2 ^ (prefixWord ++ tailWord_3671897).sum := by decide
  have hdescent : baseEnd_3671897 < baseStart_3671897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671944 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3671944 : Nat := 118140960795 + 3671944 * 2 ^ 59
def prefixEnd_3671944 : Nat := 4983230072969 + 3 ^ 40 * 3671944 * 2
def baseEnd_3671944 : Nat := 1885472208393086735913043

theorem tailTrace_3671944 : CollatzResearch.WordTrace tailWord_3671944 prefixEnd_3671944 1885472208393086735913043 := by
  unfold tailWord_3671944
  simp only [CollatzResearch.WordTrace]
  refine ⟨66963400104590740476443443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89284533472787653968591257 66963400104590740476443443)
  ·
    refine ⟨100445100156886110714665165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66963400104590740476443443 100445100156886110714665165)
    ·
      refine ⟨37666912558832291517999437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100445100156886110714665165 37666912558832291517999437)
      ·
        refine ⟨14125092209562109319249789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37666912558832291517999437 14125092209562109319249789)
        ·
          refine ⟨5296909578585790994718671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14125092209562109319249789 5296909578585790994718671)
          ·
            refine ⟨7945364367878686492078007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296909578585790994718671 7945364367878686492078007)
            ·
              refine ⟨11918046551818029738117011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945364367878686492078007 11918046551818029738117011)
              ·
                refine ⟨17877069827727044607175517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918046551818029738117011 17877069827727044607175517)
                ·
                  refine ⟨6703901185397641727690819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17877069827727044607175517 6703901185397641727690819)
                  ·
                    refine ⟨10055851778096462591536229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6703901185397641727690819 10055851778096462591536229)
                    ·
                      refine ⟨1885472208393086735913043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10055851778096462591536229 1885472208393086735913043)
                      ·
                        rfl

theorem cell23_3671944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3671944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671944 prefixEnd_3671944 := by exact prefixLift 3671944
  have htrace : WordTrace (prefixWord ++ tailWord_3671944) baseStart_3671944 baseEnd_3671944 := by
    simpa [prefixWord, tailWord_3671944, baseEnd_3671944] using wordTrace_append hprefix tailTrace_3671944
  have hstable : (prefixWord ++ tailWord_3671944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671944).length < 2 ^ (prefixWord ++ tailWord_3671944).sum := by decide
  have hdescent : baseEnd_3671944 < baseStart_3671944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671954 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3671954 : Nat := 118140960795 + 3671954 * 2 ^ 59
def prefixEnd_3671954 : Nat := 4983230072969 + 3 ^ 40 * 3671954 * 2
def baseEnd_3671954 : Nat := 628492447733210565595999

theorem tailTrace_3671954 : CollatzResearch.WordTrace tailWord_3671954 prefixEnd_3671954 628492447733210565595999 := by
  unfold tailWord_3671954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33481791234786313165187729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89284776626096835107167277 33481791234786313165187729)
  ·
    refine ⟨25111343426089734873890797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33481791234786313165187729 25111343426089734873890797)
    ·
      refine ⟨9416753784783650577709049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25111343426089734873890797 9416753784783650577709049)
      ·
        refine ⟨7062565338587737933281787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9416753784783650577709049 7062565338587737933281787)
        ·
          refine ⟨10593848007881606899922681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7062565338587737933281787 10593848007881606899922681)
          ·
            refine ⟨7945386005911205174942011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10593848007881606899922681 7945386005911205174942011)
            ·
              refine ⟨11918079008866807762413017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945386005911205174942011 11918079008866807762413017)
              ·
                refine ⟨8938559256650105821809763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11918079008866807762413017 8938559256650105821809763)
                ·
                  refine ⟨13407838884975158732714645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938559256650105821809763 13407838884975158732714645)
                  ·
                    refine ⟨628492447733210565595999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13407838884975158732714645 628492447733210565595999)
                    ·
                      rfl

theorem cell23_3671954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3671954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671954 prefixEnd_3671954 := by exact prefixLift 3671954
  have htrace : WordTrace (prefixWord ++ tailWord_3671954) baseStart_3671954 baseEnd_3671954 := by
    simpa [prefixWord, tailWord_3671954, baseEnd_3671954] using wordTrace_append hprefix tailTrace_3671954
  have hstable : (prefixWord ++ tailWord_3671954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671954).length < 2 ^ (prefixWord ++ tailWord_3671954).sum := by decide
  have hdescent : baseEnd_3671954 < baseStart_3671954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671957 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3671957 : Nat := 118140960795 + 3671957 * 2 ^ 59
def prefixEnd_3671957 : Nat := 4983230072969 + 3 ^ 40 * 3671957 * 2
def baseEnd_3671957 : Nat := 1885478883641595185050483

theorem tailTrace_3671957 : CollatzResearch.WordTrace tailWord_3671957 prefixEnd_3671957 1885478883641595185050483 := by
  unfold tailWord_3671957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133927274358134384173110125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89284849572089589448740083 133927274358134384173110125)
  ·
    refine ⟨50222727884300394064916297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133927274358134384173110125 50222727884300394064916297)
    ·
      refine ⟨37667045913225295548687223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50222727884300394064916297 37667045913225295548687223)
      ·
        refine ⟨56500568869837943323030835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37667045913225295548687223 56500568869837943323030835)
        ·
          refine ⟨84750853304756914984546253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56500568869837943323030835 84750853304756914984546253)
          ·
            refine ⟨31781569989283843119204845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84750853304756914984546253 31781569989283843119204845)
            ·
              refine ⟨11918088745981441169701817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31781569989283843119204845 11918088745981441169701817)
              ·
                refine ⟨8938566559486080877276363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11918088745981441169701817 8938566559486080877276363)
                ·
                  refine ⟨13407849839229121315914545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938566559486080877276363 13407849839229121315914545)
                  ·
                    refine ⟨10055887379421840986935909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13407849839229121315914545 10055887379421840986935909)
                    ·
                      refine ⟨1885478883641595185050483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10055887379421840986935909 1885478883641595185050483)
                      ·
                        rfl

theorem cell23_3671957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3671957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671957 prefixEnd_3671957 := by exact prefixLift 3671957
  have htrace : WordTrace (prefixWord ++ tailWord_3671957) baseStart_3671957 baseEnd_3671957 := by
    simpa [prefixWord, tailWord_3671957, baseEnd_3671957] using wordTrace_append hprefix tailTrace_3671957
  have hstable : (prefixWord ++ tailWord_3671957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671957).length < 2 ^ (prefixWord ++ tailWord_3671957).sum := by decide
  have hdescent : baseEnd_3671957 < baseStart_3671957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671964 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3671964 : Nat := 118140960795 + 3671964 * 2 ^ 59
def prefixEnd_3671964 : Nat := 4983230072969 + 3 ^ 40 * 3671964 * 2
def baseEnd_3671964 : Nat := 1885482478006176657662951

theorem tailTrace_3671964 : CollatzResearch.WordTrace tailWord_3671964 prefixEnd_3671964 1885482478006176657662951 := by
  unfold tailWord_3671964
  simp only [CollatzResearch.WordTrace]
  refine ⟨66963764834554512184307473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89285019779406016245743297 66963764834554512184307473)
  ·
    refine ⟨50222823625915884138230605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66963764834554512184307473 50222823625915884138230605)
    ·
      refine ⟨18833558859718456551836477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50222823625915884138230605 18833558859718456551836477)
      ·
        refine ⟨7062584572394421206938679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18833558859718456551836477 7062584572394421206938679)
        ·
          refine ⟨10593876858591631810408019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7062584572394421206938679 10593876858591631810408019)
          ·
            refine ⟨15890815287887447715612029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10593876858591631810408019 15890815287887447715612029)
            ·
              refine ⟨5959055732957792893354511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15890815287887447715612029 5959055732957792893354511)
              ·
                refine ⟨8938583599436689340031767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959055732957792893354511 8938583599436689340031767)
                ·
                  refine ⟨13407875399155034010047651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938583599436689340031767 13407875399155034010047651)
                  ·
                    refine ⟨20111813098732551015071477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13407875399155034010047651 20111813098732551015071477)
                    ·
                      refine ⟨1885482478006176657662951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20111813098732551015071477 1885482478006176657662951)
                      ·
                        rfl

theorem cell23_3671964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3671964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671964 prefixEnd_3671964 := by exact prefixLift 3671964
  have htrace : WordTrace (prefixWord ++ tailWord_3671964) baseStart_3671964 baseEnd_3671964 := by
    simpa [prefixWord, tailWord_3671964, baseEnd_3671964] using wordTrace_append hprefix tailTrace_3671964
  have hstable : (prefixWord ++ tailWord_3671964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671964).length < 2 ^ (prefixWord ++ tailWord_3671964).sum := by decide
  have hdescent : baseEnd_3671964 < baseStart_3671964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671967 : List Nat := [1, 1, 2, 5, 4, 10]
def baseStart_3671967 : Nat := 118140960795 + 3671967 * 2 ^ 59
def prefixEnd_3671967 : Nat := 4983230072969 + 3 ^ 40 * 3671967 * 2
def baseEnd_3671967 : Nat := 7759193491556132287759

theorem tailTrace_3671967 : CollatzResearch.WordTrace tailWord_3671967 prefixEnd_3671967 7759193491556132287759 := by
  unfold tailWord_3671967
  simp only [CollatzResearch.WordTrace]
  refine ⟨133927639088098155880974155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89285092725398770587316103 133927639088098155880974155)
  ·
    refine ⟨200891458632147233821461233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133927639088098155880974155 200891458632147233821461233)
    ·
      refine ⟨150668593974110425366095925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200891458632147233821461233 150668593974110425366095925)
      ·
        refine ⟨14125180685072852378071493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150668593974110425366095925 14125180685072852378071493)
        ·
          refine ⟨2648471378451159820888405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14125180685072852378071493 2648471378451159820888405)
          ·
            refine ⟨7759193491556132287759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2648471378451159820888405 7759193491556132287759)
            ·
              rfl

theorem cell23_3671967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 10].length) (baseStart_3671967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3671967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3671967 prefixEnd_3671967 := by exact prefixLift 3671967
  have htrace : WordTrace (prefixWord ++ tailWord_3671967) baseStart_3671967 baseEnd_3671967 := by
    simpa [prefixWord, tailWord_3671967, baseEnd_3671967] using wordTrace_append hprefix tailTrace_3671967
  have hstable : (prefixWord ++ tailWord_3671967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671967).length < 2 ^ (prefixWord ++ tailWord_3671967).sum := by decide
  have hdescent : baseEnd_3671967 < baseStart_3671967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672045 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3672045 : Nat := 118140960795 + 3672045 * 2 ^ 59
def prefixEnd_3672045 : Nat := 4983230072969 + 3 ^ 40 * 3672045 * 2
def baseEnd_3672045 : Nat := 1885524069939190840750079

theorem tailTrace_3672045 : CollatzResearch.WordTrace tailWord_3672045 prefixEnd_3672045 1885524069939190840750079 := by
  unfold tailWord_3672045
  simp only [CollatzResearch.WordTrace]
  refine ⟨133930483981815575202313589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89286989321210383468209059 133930483981815575202313589)
  ·
    refine ⟨12555982873295210175216899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133930483981815575202313589 12555982873295210175216899)
    ·
      refine ⟨18833974309942815262825349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12555982873295210175216899 18833974309942815262825349)
      ·
        refine ⟨3531370183114277861779753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18833974309942815262825349 3531370183114277861779753)
        ·
          refine ⟨2648527637335708396334815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531370183114277861779753 2648527637335708396334815)
          ·
            refine ⟨3972791456003562594502223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648527637335708396334815 3972791456003562594502223)
            ·
              refine ⟨5959187184005343891753335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972791456003562594502223 5959187184005343891753335)
              ·
                refine ⟨8938780776008015837630003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959187184005343891753335 8938780776008015837630003)
                ·
                  refine ⟨13408171164012023756445005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938780776008015837630003 13408171164012023756445005)
                  ·
                    refine ⟨5028064186504508908666877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13408171164012023756445005 5028064186504508908666877)
                    ·
                      refine ⟨1885524069939190840750079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028064186504508908666877 1885524069939190840750079)
                      ·
                        rfl

theorem cell23_3672045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3672045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672045 prefixEnd_3672045 := by exact prefixLift 3672045
  have htrace : WordTrace (prefixWord ++ tailWord_3672045) baseStart_3672045 baseEnd_3672045 := by
    simpa [prefixWord, tailWord_3672045, baseEnd_3672045] using wordTrace_append hprefix tailTrace_3672045
  have hstable : (prefixWord ++ tailWord_3672045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672045).length < 2 ^ (prefixWord ++ tailWord_3672045).sum := by decide
  have hdescent : baseEnd_3672045 < baseStart_3672045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672047 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_3672047 : Nat := 118140960795 + 3672047 * 2 ^ 59
def prefixEnd_3672047 : Nat := 4983230072969 + 3 ^ 40 * 3672047 * 2
def baseEnd_3672047 : Nat := 1885525096900499832925069

theorem tailTrace_3672047 : CollatzResearch.WordTrace tailWord_3672047 prefixEnd_3672047 1885525096900499832925069 := by
  unfold tailWord_3672047
  simp only [CollatzResearch.WordTrace]
  refine ⟨133930556927808329543886395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89287037951872219695924263 133930556927808329543886395)
  ·
    refine ⟨200895835391712494315829593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133930556927808329543886395 200895835391712494315829593)
    ·
      refine ⟨150671876543784370736872195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200895835391712494315829593 150671876543784370736872195)
      ·
        refine ⟨226007814815676556105308293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150671876543784370736872195 226007814815676556105308293)
        ·
          refine ⟨42376465277939354269745305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226007814815676556105308293 42376465277939354269745305)
          ·
            refine ⟨31782348958454515702308979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42376465277939354269745305 31782348958454515702308979)
            ·
              refine ⟨47673523437681773553463469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782348958454515702308979 47673523437681773553463469)
              ·
                refine ⟨17877571289130665082548801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47673523437681773553463469 17877571289130665082548801)
                ·
                  refine ⟨13408178466847998811911601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17877571289130665082548801 13408178466847998811911601)
                  ·
                    refine ⟨10056133850135999108933701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13408178466847998811911601 10056133850135999108933701)
                    ·
                      refine ⟨1885525096900499832925069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10056133850135999108933701 1885525096900499832925069)
                      ·
                        rfl

theorem cell23_3672047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_3672047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672047 prefixEnd_3672047 := by exact prefixLift 3672047
  have htrace : WordTrace (prefixWord ++ tailWord_3672047) baseStart_3672047 baseEnd_3672047 := by
    simpa [prefixWord, tailWord_3672047, baseEnd_3672047] using wordTrace_append hprefix tailTrace_3672047
  have hstable : (prefixWord ++ tailWord_3672047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672047).length < 2 ^ (prefixWord ++ tailWord_3672047).sum := by decide
  have hdescent : baseEnd_3672047 < baseStart_3672047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672051 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 2, 2, 2]
def baseStart_3672051 : Nat := 118140960795 + 3672051 * 2 ^ 59
def prefixEnd_3672051 : Nat := 4983230072969 + 3 ^ 40 * 3672051 * 2
def baseEnd_3672051 : Nat := 1885527150823117817275051

theorem tailTrace_3672051 : CollatzResearch.WordTrace tailWord_3672051 prefixEnd_3672051 1885527150823117817275051 := by
  unfold tailWord_3672051
  simp only [CollatzResearch.WordTrace]
  refine ⟨133930702819793838227032007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89287135213195892151354671 133930702819793838227032007)
  ·
    refine ⟨200896054229690757340548011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133930702819793838227032007 200896054229690757340548011)
    ·
      refine ⟨301344081344536136010822017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200896054229690757340548011 301344081344536136010822017)
      ·
        refine ⟨226008061008402102008116513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301344081344536136010822017 226008061008402102008116513)
        ·
          refine ⟨169506045756301576506087385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226008061008402102008116513 169506045756301576506087385)
          ·
            refine ⟨127129534317226182379565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169506045756301576506087385 127129534317226182379565539)
            ·
              refine ⟨190694301475839273569348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127129534317226182379565539 190694301475839273569348309)
              ·
                refine ⟨4469397690839982974281601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190694301475839273569348309 4469397690839982974281601)
                ·
                  refine ⟨3352048268129987230711201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4469397690839982974281601 3352048268129987230711201)
                  ·
                    refine ⟨2514036201097490423033401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3352048268129987230711201 2514036201097490423033401)
                    ·
                      refine ⟨1885527150823117817275051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514036201097490423033401 1885527150823117817275051)
                      ·
                        rfl

theorem cell23_3672051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2, 2].length) (baseStart_3672051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672051 prefixEnd_3672051 := by exact prefixLift 3672051
  have htrace : WordTrace (prefixWord ++ tailWord_3672051) baseStart_3672051 baseEnd_3672051 := by
    simpa [prefixWord, tailWord_3672051, baseEnd_3672051] using wordTrace_append hprefix tailTrace_3672051
  have hstable : (prefixWord ++ tailWord_3672051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672051).length < 2 ^ (prefixWord ++ tailWord_3672051).sum := by decide
  have hdescent : baseEnd_3672051 < baseStart_3672051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672057 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 7]
def baseStart_3672057 : Nat := 118140960795 + 3672057 * 2 ^ 59
def prefixEnd_3672057 : Nat := 4983230072969 + 3 ^ 40 * 3672057 * 2
def baseEnd_3672057 : Nat := 209503359078560532644447

theorem tailTrace_3672057 : CollatzResearch.WordTrace tailWord_3672057 prefixEnd_3672057 209503359078560532644447 := by
  unfold tailWord_3672057
  simp only [CollatzResearch.WordTrace]
  refine ⟨133930921657772101251750425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89287281105181400834500283 133930921657772101251750425)
  ·
    refine ⟨100448191243329075938812819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133930921657772101251750425 100448191243329075938812819)
    ·
      refine ⟨150672286864993613908219229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100448191243329075938812819 150672286864993613908219229)
      ·
        refine ⟨56502107574372605215582211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150672286864993613908219229 56502107574372605215582211)
        ·
          refine ⟨84753161361558907823373317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56502107574372605215582211 84753161361558907823373317)
          ·
            refine ⟨15891217755292295216882497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84753161361558907823373317 15891217755292295216882497)
            ·
              refine ⟨11918413316469221412661873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15891217755292295216882497 11918413316469221412661873)
              ·
                refine ⟨8938809987351916059496405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11918413316469221412661873 8938809987351916059496405)
                ·
                  refine ⟨209503359078560532644447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8938809987351916059496405 209503359078560532644447)
                  ·
                    rfl

theorem cell23_3672057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_3672057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672057 prefixEnd_3672057 := by exact prefixLift 3672057
  have htrace : WordTrace (prefixWord ++ tailWord_3672057) baseStart_3672057 baseEnd_3672057 := by
    simpa [prefixWord, tailWord_3672057, baseEnd_3672057] using wordTrace_append hprefix tailTrace_3672057
  have hstable : (prefixWord ++ tailWord_3672057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672057).length < 2 ^ (prefixWord ++ tailWord_3672057).sum := by decide
  have hdescent : baseEnd_3672057 < baseStart_3672057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672067 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3]
def baseStart_3672067 : Nat := 118140960795 + 3672067 * 2 ^ 59
def prefixEnd_3672067 : Nat := 4983230072969 + 3 ^ 40 * 3672067 * 2
def baseEnd_3672067 : Nat := 1885535366513589754674977

theorem tailTrace_3672067 : CollatzResearch.WordTrace tailWord_3672067 prefixEnd_3672067 1885535366513589754674977 := by
  unfold tailWord_3672067
  simp only [CollatzResearch.WordTrace]
  refine ⟨133931286387735872959614455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89287524258490581973076303 133931286387735872959614455)
  ·
    refine ⟨200896929581603809439421683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133931286387735872959614455 200896929581603809439421683)
    ·
      refine ⟨301345394372405714159132525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200896929581603809439421683 301345394372405714159132525)
      ·
        refine ⟨113004522889652142809674697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301345394372405714159132525 113004522889652142809674697)
        ·
          refine ⟨84753392167239107107256023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113004522889652142809674697 84753392167239107107256023)
          ·
            refine ⟨127130088250858660660884035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84753392167239107107256023 127130088250858660660884035)
            ·
              refine ⟨190695132376287990991326053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127130088250858660660884035 190695132376287990991326053)
              ·
                refine ⟨35755337320553998310873635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190695132376287990991326053 35755337320553998310873635)
                ·
                  refine ⟨53633005980830997466310453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35755337320553998310873635 53633005980830997466310453)
                  ·
                    refine ⟨5028094310702906012466605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53633005980830997466310453 5028094310702906012466605)
                    ·
                      refine ⟨1885535366513589754674977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028094310702906012466605 1885535366513589754674977)
                      ·
                        rfl

theorem cell23_3672067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_3672067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672067 prefixEnd_3672067 := by exact prefixLift 3672067
  have htrace : WordTrace (prefixWord ++ tailWord_3672067) baseStart_3672067 baseEnd_3672067 := by
    simpa [prefixWord, tailWord_3672067, baseEnd_3672067] using wordTrace_append hprefix tailTrace_3672067
  have hstable : (prefixWord ++ tailWord_3672067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672067).length < 2 ^ (prefixWord ++ tailWord_3672067).sum := by decide
  have hdescent : baseEnd_3672067 < baseStart_3672067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672107 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_3672107 : Nat := 118140960795 + 3672107 * 2 ^ 59
def prefixEnd_3672107 : Nat := 4983230072969 + 3 ^ 40 * 3672107 * 2
def baseEnd_3672107 : Nat := 1885555905739769598174793

theorem tailTrace_3672107 : CollatzResearch.WordTrace tailWord_3672107 prefixEnd_3672107 1885555905739769598174793 := by
  unfold tailWord_3672107
  simp only [CollatzResearch.WordTrace]
  refine ⟨133932745307590959791070575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89288496871727306527380383 133932745307590959791070575)
  ·
    refine ⟨200899117961386439686605863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133932745307590959791070575 200899117961386439686605863)
    ·
      refine ⟨301348676942079659529908795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200899117961386439686605863 301348676942079659529908795)
      ·
        refine ⟨452023015413119489294863193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301348676942079659529908795 452023015413119489294863193)
        ·
          refine ⟨339017261559839616971147395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452023015413119489294863193 339017261559839616971147395)
          ·
            refine ⟨508525892339759425456721093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339017261559839616971147395 508525892339759425456721093)
            ·
              refine ⟨95348604813704892273135205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508525892339759425456721093 95348604813704892273135205)
              ·
                refine ⟨17877863402569667301212851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95348604813704892273135205 17877863402569667301212851)
                ·
                  refine ⟨26816795103854500951819277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17877863402569667301212851 26816795103854500951819277)
                  ·
                    refine ⟨10056298163945437856932229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26816795103854500951819277 10056298163945437856932229)
                    ·
                      refine ⟨1885555905739769598174793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10056298163945437856932229 1885555905739769598174793)
                      ·
                        rfl

theorem cell23_3672107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_3672107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672107 prefixEnd_3672107 := by exact prefixLift 3672107
  have htrace : WordTrace (prefixWord ++ tailWord_3672107) baseStart_3672107 baseEnd_3672107 := by
    simpa [prefixWord, tailWord_3672107, baseEnd_3672107] using wordTrace_append hprefix tailTrace_3672107
  have hstable : (prefixWord ++ tailWord_3672107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672107).length < 2 ^ (prefixWord ++ tailWord_3672107).sum := by decide
  have hdescent : baseEnd_3672107 < baseStart_3672107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672117 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3672117 : Nat := 118140960795 + 3672117 * 2 ^ 59
def prefixEnd_3672117 : Nat := 4983230072969 + 3 ^ 40 * 3672117 * 2
def baseEnd_3672117 : Nat := 628520346848771519683249

theorem tailTrace_3672117 : CollatzResearch.WordTrace tailWord_3672117 prefixEnd_3672117 628520346848771519683249 := by
  unfold tailWord_3672117
  simp only [CollatzResearch.WordTrace]
  refine ⟨133933110037554731498934605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89288740025036487665956403 133933110037554731498934605)
  ·
    refine ⟨50224916264083024312100477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133933110037554731498934605 50224916264083024312100477)
    ·
      refine ⟨18834343599031134117037679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50224916264083024312100477 18834343599031134117037679)
      ·
        refine ⟨28251515398546701175556519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18834343599031134117037679 28251515398546701175556519)
        ·
          refine ⟨42377273097820051763334779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28251515398546701175556519 42377273097820051763334779)
          ·
            refine ⟨63565909646730077645002169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377273097820051763334779 63565909646730077645002169)
            ·
              refine ⟨47674432235047558233751627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63565909646730077645002169 47674432235047558233751627)
              ·
                refine ⟨71511648352571337350627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47674432235047558233751627 71511648352571337350627441)
                ·
                  refine ⟨53633736264428503012970581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71511648352571337350627441 53633736264428503012970581)
                  ·
                    refine ⟨628520346848771519683249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53633736264428503012970581 628520346848771519683249)
                    ·
                      rfl

theorem cell23_3672117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3672117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672117 prefixEnd_3672117 := by exact prefixLift 3672117
  have htrace : WordTrace (prefixWord ++ tailWord_3672117) baseStart_3672117 baseEnd_3672117 := by
    simpa [prefixWord, tailWord_3672117, baseEnd_3672117] using wordTrace_append hprefix tailTrace_3672117
  have hstable : (prefixWord ++ tailWord_3672117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672117).length < 2 ^ (prefixWord ++ tailWord_3672117).sum := by decide
  have hdescent : baseEnd_3672117 < baseStart_3672117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672121 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_3672121 : Nat := 118140960795 + 3672121 * 2 ^ 59
def prefixEnd_3672121 : Nat := 4983230072969 + 3 ^ 40 * 3672121 * 2
def baseEnd_3672121 : Nat := 628521031489644181133243

theorem tailTrace_3672121 : CollatzResearch.WordTrace tailWord_3672121 prefixEnd_3672121 628521031489644181133243 := by
  unfold tailWord_3672121
  simp only [CollatzResearch.WordTrace]
  refine ⟨133933255929540240182080217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89288837286360160121386811 133933255929540240182080217)
  ·
    refine ⟨100449941947155180136560163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133933255929540240182080217 100449941947155180136560163)
    ·
      refine ⟨150674912920732770204840245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100449941947155180136560163 150674912920732770204840245)
      ·
        refine ⟨14125773086318697206703773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150674912920732770204840245 14125773086318697206703773)
        ·
          refine ⟨5297164907369511452513915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14125773086318697206703773 5297164907369511452513915)
          ·
            refine ⟨7945747361054267178770873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297164907369511452513915 7945747361054267178770873)
            ·
              refine ⟨5959310520790700384078155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945747361054267178770873 5959310520790700384078155)
              ·
                refine ⟨8938965781186050576117233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959310520790700384078155 8938965781186050576117233)
                ·
                  refine ⟨6704224335889537932087925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938965781186050576117233 6704224335889537932087925)
                  ·
                    refine ⟨628521031489644181133243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6704224335889537932087925 628521031489644181133243)
                    ·
                      rfl

theorem cell23_3672121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_3672121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672121 prefixEnd_3672121 := by exact prefixLift 3672121
  have htrace : WordTrace (prefixWord ++ tailWord_3672121) baseStart_3672121 baseEnd_3672121 := by
    simpa [prefixWord, tailWord_3672121, baseEnd_3672121] using wordTrace_append hprefix tailTrace_3672121
  have hstable : (prefixWord ++ tailWord_3672121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672121).length < 2 ^ (prefixWord ++ tailWord_3672121).sum := by decide
  have hdescent : baseEnd_3672121 < baseStart_3672121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672137 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_3672137 : Nat := 118140960795 + 3672137 * 2 ^ 59
def prefixEnd_3672137 : Nat := 4983230072969 + 3 ^ 40 * 3672137 * 2
def baseEnd_3672137 : Nat := 1885571310159404480799655

theorem tailTrace_3672137 : CollatzResearch.WordTrace tailWord_3672137 prefixEnd_3672137 1885571310159404480799655 := by
  unfold tailWord_3672137
  simp only [CollatzResearch.WordTrace]
  refine ⟨133933839497482274914662665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89289226331654849943108443 133933839497482274914662665)
  ·
    refine ⟨100450379623111706185996999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133933839497482274914662665 100450379623111706185996999)
    ·
      refine ⟨150675569434667559278995499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100450379623111706185996999 150675569434667559278995499)
      ·
        refine ⟨226013354152001338918493249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150675569434667559278995499 226013354152001338918493249)
        ·
          refine ⟨169510015614001004188869937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226013354152001338918493249 169510015614001004188869937)
          ·
            refine ⟨127132511710500753141652453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169510015614001004188869937 127132511710500753141652453)
            ·
              refine ⟨23837345945718891214059835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127132511710500753141652453 23837345945718891214059835)
              ·
                refine ⟨35756018918578336821089753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23837345945718891214059835 35756018918578336821089753)
                ·
                  refine ⟨26817014188933752615817315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35756018918578336821089753 26817014188933752615817315)
                  ·
                    refine ⟨40225521283400628923725973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26817014188933752615817315 40225521283400628923725973)
                    ·
                      refine ⟨1885571310159404480799655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40225521283400628923725973 1885571310159404480799655)
                      ·
                        rfl

theorem cell23_3672137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_3672137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672137 prefixEnd_3672137 := by exact prefixLift 3672137
  have htrace : WordTrace (prefixWord ++ tailWord_3672137) baseStart_3672137 baseEnd_3672137 := by
    simpa [prefixWord, tailWord_3672137, baseEnd_3672137] using wordTrace_append hprefix tailTrace_3672137
  have hstable : (prefixWord ++ tailWord_3672137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672137).length < 2 ^ (prefixWord ++ tailWord_3672137).sum := by decide
  have hdescent : baseEnd_3672137 < baseStart_3672137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672141 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3672141 : Nat := 118140960795 + 3672141 * 2 ^ 59
def prefixEnd_3672141 : Nat := 4983230072969 + 3 ^ 40 * 3672141 * 2
def baseEnd_3672141 : Nat := 1885573364082022465149637

theorem tailTrace_3672141 : CollatzResearch.WordTrace tailWord_3672141 prefixEnd_3672141 1885573364082022465149637 := by
  unfold tailWord_3672141
  simp only [CollatzResearch.WordTrace]
  refine ⟨133933985389467783597808277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89289323592978522398538851 133933985389467783597808277)
  ·
    refine ⟨6278155565131302356147263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133933985389467783597808277 6278155565131302356147263)
    ·
      refine ⟨9417233347696953534220895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278155565131302356147263 9417233347696953534220895)
      ·
        refine ⟨14125850021545430301331343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417233347696953534220895 14125850021545430301331343)
        ·
          refine ⟨21188775032318145451997015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14125850021545430301331343 21188775032318145451997015)
          ·
            refine ⟨31783162548477218177995523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21188775032318145451997015 31783162548477218177995523)
            ·
              refine ⟨47674743822715827266993285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31783162548477218177995523 47674743822715827266993285)
              ·
                refine ⟨8939014466759217612561241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47674743822715827266993285 8939014466759217612561241)
                ·
                  refine ⟨6704260850069413209420931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8939014466759217612561241 6704260850069413209420931)
                  ·
                    refine ⟨10056391275104119814131397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704260850069413209420931 10056391275104119814131397)
                    ·
                      refine ⟨1885573364082022465149637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10056391275104119814131397 1885573364082022465149637)
                      ·
                        rfl

theorem cell23_3672141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3672141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672141 prefixEnd_3672141 := by exact prefixLift 3672141
  have htrace : WordTrace (prefixWord ++ tailWord_3672141) baseStart_3672141 baseEnd_3672141 := by
    simpa [prefixWord, tailWord_3672141, baseEnd_3672141] using wordTrace_append hprefix tailTrace_3672141
  have hstable : (prefixWord ++ tailWord_3672141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672141).length < 2 ^ (prefixWord ++ tailWord_3672141).sum := by decide
  have hdescent : baseEnd_3672141 < baseStart_3672141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672164 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 6]
def baseStart_3672164 : Nat := 118140960795 + 3672164 * 2 ^ 59
def prefixEnd_3672164 : Nat := 4983230072969 + 3 ^ 40 * 3672164 * 2
def baseEnd_3672164 : Nat := 209509463793008430573559

theorem tailTrace_3672164 : CollatzResearch.WordTrace tailWord_3672164 prefixEnd_3672164 209509463793008430573559 := by
  unfold tailWord_3672164
  simp only [CollatzResearch.WordTrace]
  refine ⟨66967412134192229262947773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89289882845589639017263697 66967412134192229262947773)
  ·
    refine ⟨25112779550322085973605415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66967412134192229262947773 25112779550322085973605415)
    ·
      refine ⟨37669169325483128960408123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25112779550322085973605415 37669169325483128960408123)
      ·
        refine ⟨56503753988224693440612185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37669169325483128960408123 56503753988224693440612185)
        ·
          refine ⟨42377815491168520080459139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56503753988224693440612185 42377815491168520080459139)
          ·
            refine ⟨63566723236752780120688709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377815491168520080459139 63566723236752780120688709)
            ·
              refine ⟨11918760606891146272629133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63566723236752780120688709 11918760606891146272629133)
              ·
                refine ⟨4469535227584179852235925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11918760606891146272629133 4469535227584179852235925)
                ·
                  refine ⟨209509463793008430573559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4469535227584179852235925 209509463793008430573559)
                  ·
                    rfl

theorem cell23_3672164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_3672164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672164 prefixEnd_3672164 := by exact prefixLift 3672164
  have htrace : WordTrace (prefixWord ++ tailWord_3672164) baseStart_3672164 baseEnd_3672164 := by
    simpa [prefixWord, tailWord_3672164, baseEnd_3672164] using wordTrace_append hprefix tailTrace_3672164
  have hstable : (prefixWord ++ tailWord_3672164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672164).length < 2 ^ (prefixWord ++ tailWord_3672164).sum := by decide
  have hdescent : baseEnd_3672164 < baseStart_3672164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672178 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3672178 : Nat := 118140960795 + 3672178 * 2 ^ 59
def prefixEnd_3672178 : Nat := 4983230072969 + 3 ^ 40 * 3672178 * 2
def baseEnd_3672178 : Nat := 1885592362866238820386967

theorem tailTrace_3672178 : CollatzResearch.WordTrace tailWord_3672178 prefixEnd_3672178 1885592362866238820386967 := by
  unfold tailWord_3672178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33483833722583434729226297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89290223260222492611270125 33483833722583434729226297)
  ·
    refine ⟨25112875291937576046919723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33483833722583434729226297 25112875291937576046919723)
    ·
      refine ⟨37669312937906364070379585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25112875291937576046919723 37669312937906364070379585)
      ·
        refine ⟨28251984703429773052784689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37669312937906364070379585 28251984703429773052784689)
        ·
          refine ⟨21188988527572329789588517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28251984703429773052784689 21188988527572329789588517)
          ·
            refine ⟨3972935348919811835547847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21188988527572329789588517 3972935348919811835547847)
            ·
              refine ⟨5959403023379717753321771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972935348919811835547847 5959403023379717753321771)
              ·
                refine ⟨8939104535069576629982657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959403023379717753321771 8939104535069576629982657)
                ·
                  refine ⟨6704328401302182472486993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8939104535069576629982657 6704328401302182472486993)
                  ·
                    refine ⟨5028246300976636854365245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704328401302182472486993 5028246300976636854365245)
                    ·
                      refine ⟨1885592362866238820386967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028246300976636854365245 1885592362866238820386967)
                      ·
                        rfl

theorem cell23_3672178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3672178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672178 prefixEnd_3672178 := by exact prefixLift 3672178
  have htrace : WordTrace (prefixWord ++ tailWord_3672178) baseStart_3672178 baseEnd_3672178 := by
    simpa [prefixWord, tailWord_3672178, baseEnd_3672178] using wordTrace_append hprefix tailTrace_3672178
  have hstable : (prefixWord ++ tailWord_3672178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672178).length < 2 ^ (prefixWord ++ tailWord_3672178).sum := by decide
  have hdescent : baseEnd_3672178 < baseStart_3672178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672187 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_3672187 : Nat := 118140960795 + 3672187 * 2 ^ 59
def prefixEnd_3672187 : Nat := 4983230072969 + 3 ^ 40 * 3672187 * 2
def baseEnd_3672187 : Nat := 1885596984192129285174425

theorem tailTrace_3672187 : CollatzResearch.WordTrace tailWord_3672187 prefixEnd_3672187 1885596984192129285174425 := by
  unfold tailWord_3672187
  simp only [CollatzResearch.WordTrace]
  refine ⟨133935663147301133453982815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89290442098200755635988543 133935663147301133453982815)
  ·
    refine ⟨200903494720951700180974223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133935663147301133453982815 200903494720951700180974223)
    ·
      refine ⟨301355242081427550271461335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200903494720951700180974223 301355242081427550271461335)
      ·
        refine ⟨452032863122141325407192003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301355242081427550271461335 452032863122141325407192003)
        ·
          refine ⟨678049294683211988110788005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452032863122141325407192003 678049294683211988110788005)
          ·
            refine ⟨127134242753102247770772751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 678049294683211988110788005 127134242753102247770772751)
            ·
              refine ⟨190701364129653371656159127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127134242753102247770772751 190701364129653371656159127)
              ·
                refine ⟨286052046194480057484238691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190701364129653371656159127 286052046194480057484238691)
                ·
                  refine ⟨429078069291720086226358037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286052046194480057484238691 429078069291720086226358037)
                  ·
                    refine ⟨20113034498049379041860533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 429078069291720086226358037 20113034498049379041860533)
                    ·
                      refine ⟨1885596984192129285174425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20113034498049379041860533 1885596984192129285174425)
                      ·
                        rfl

theorem cell23_3672187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_3672187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672187 prefixEnd_3672187 := by exact prefixLift 3672187
  have htrace : WordTrace (prefixWord ++ tailWord_3672187) baseStart_3672187 baseEnd_3672187 := by
    simpa [prefixWord, tailWord_3672187, baseEnd_3672187] using wordTrace_append hprefix tailTrace_3672187
  have hstable : (prefixWord ++ tailWord_3672187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672187).length < 2 ^ (prefixWord ++ tailWord_3672187).sum := by decide
  have hdescent : baseEnd_3672187 < baseStart_3672187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672201 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 4, 3, 2]
def baseStart_3672201 : Nat := 118140960795 + 3672201 * 2 ^ 59
def prefixEnd_3672201 : Nat := 4983230072969 + 3 ^ 40 * 3672201 * 2
def baseEnd_3672201 : Nat := 1885604172921292230399361

theorem tailTrace_3672201 : CollatzResearch.WordTrace tailWord_3672201 prefixEnd_3672201 1885604172921292230399361 := by
  unfold tailWord_3672201
  simp only [CollatzResearch.WordTrace]
  refine ⟨133936173769250413844992457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89290782512833609229994971 133936173769250413844992457)
  ·
    refine ⟨100452130326937810383744343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133936173769250413844992457 100452130326937810383744343)
    ·
      refine ⟨150678195490406715575616515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100452130326937810383744343 150678195490406715575616515)
      ·
        refine ⟨226017293235610073363424773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150678195490406715575616515 226017293235610073363424773)
        ·
          refine ⟨42378242481676888755642145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226017293235610073363424773 42378242481676888755642145)
          ·
            refine ⟨31783681861257666566731609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42378242481676888755642145 31783681861257666566731609)
            ·
              refine ⟨23837761395943249925048707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31783681861257666566731609 23837761395943249925048707)
              ·
                refine ⟨35756642093914874887573061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23837761395943249925048707 35756642093914874887573061)
                ·
                  refine ⟨6704370392609039041419949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35756642093914874887573061 6704370392609039041419949)
                  ·
                    refine ⟨2514138897228389640532481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6704370392609039041419949 2514138897228389640532481)
                    ·
                      refine ⟨1885604172921292230399361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514138897228389640532481 1885604172921292230399361)
                      ·
                        rfl

theorem cell23_3672201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3, 2].length) (baseStart_3672201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672201 prefixEnd_3672201 := by exact prefixLift 3672201
  have htrace : WordTrace (prefixWord ++ tailWord_3672201) baseStart_3672201 baseEnd_3672201 := by
    simpa [prefixWord, tailWord_3672201, baseEnd_3672201] using wordTrace_append hprefix tailTrace_3672201
  have hstable : (prefixWord ++ tailWord_3672201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672201).length < 2 ^ (prefixWord ++ tailWord_3672201).sum := by decide
  have hdescent : baseEnd_3672201 < baseStart_3672201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672208 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 1, 1, 3]
def baseStart_3672208 : Nat := 118140960795 + 3672208 * 2 ^ 59
def prefixEnd_3672208 : Nat := 4983230072969 + 3 ^ 40 * 3672208 * 2
def baseEnd_3672208 : Nat := 1885607767285873703011829

theorem tailTrace_3672208 : CollatzResearch.WordTrace tailWord_3672208 prefixEnd_3672208 1885607767285873703011829 := by
  unfold tailWord_3672208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66968214540112527020248639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89290952720150036026998185 66968214540112527020248639)
  ·
    refine ⟨100452321810168790530372959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66968214540112527020248639 100452321810168790530372959)
    ·
      refine ⟨150678482715253185795559439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100452321810168790530372959 150678482715253185795559439)
      ·
        refine ⟨226017724072879778693339159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150678482715253185795559439 226017724072879778693339159)
        ·
          refine ⟨339026586109319668040008739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226017724072879778693339159 339026586109319668040008739)
          ·
            refine ⟨508539879163979502060013109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339026586109319668040008739 508539879163979502060013109)
            ·
              refine ⟨47675613671623078318126229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508539879163979502060013109 47675613671623078318126229)
              ·
                refine ⟨2234794390857331796162167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47675613671623078318126229 2234794390857331796162167)
                ·
                  refine ⟨3352191586285997694243251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234794390857331796162167 3352191586285997694243251)
                  ·
                    refine ⟨5028287379428996541364877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3352191586285997694243251 5028287379428996541364877)
                    ·
                      refine ⟨1885607767285873703011829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028287379428996541364877 1885607767285873703011829)
                      ·
                        rfl

theorem cell23_3672208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 1, 3].length) (baseStart_3672208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672208 prefixEnd_3672208 := by exact prefixLift 3672208
  have htrace : WordTrace (prefixWord ++ tailWord_3672208) baseStart_3672208 baseEnd_3672208 := by
    simpa [prefixWord, tailWord_3672208, baseEnd_3672208] using wordTrace_append hprefix tailTrace_3672208
  have hstable : (prefixWord ++ tailWord_3672208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672208).length < 2 ^ (prefixWord ++ tailWord_3672208).sum := by decide
  have hdescent : baseEnd_3672208 < baseStart_3672208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672228 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3672228 : Nat := 118140960795 + 3672228 * 2 ^ 59
def prefixEnd_3672228 : Nat := 4983230072969 + 3 ^ 40 * 3672228 * 2
def baseEnd_3672228 : Nat := 628539345632987874920579

theorem tailTrace_3672228 : CollatzResearch.WordTrace tailWord_3672228 prefixEnd_3672228 628539345632987874920579 := by
  unfold tailWord_3672228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66968579270076298728112669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89291439026768398304150225 66968579270076298728112669)
  ·
    refine ⟨25113217226278612023042251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66968579270076298728112669 25113217226278612023042251)
    ·
      refine ⟨37669825839417918034563377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25113217226278612023042251 37669825839417918034563377)
      ·
        refine ⟨28252369379563438525922533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37669825839417918034563377 28252369379563438525922533)
        ·
          refine ⟨5297319258668144723610475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28252369379563438525922533 5297319258668144723610475)
          ·
            refine ⟨7945978888002217085415713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297319258668144723610475 7945978888002217085415713)
            ·
              refine ⟨5959484166001662814061785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945978888002217085415713 5959484166001662814061785)
              ·
                refine ⟨4469613124501247110546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959484166001662814061785 4469613124501247110546339)
                ·
                  refine ⟨6704419686751870665819509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469613124501247110546339 6704419686751870665819509)
                  ·
                    refine ⟨628539345632987874920579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6704419686751870665819509 628539345632987874920579)
                    ·
                      rfl

theorem cell23_3672228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3672228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672228 prefixEnd_3672228 := by exact prefixLift 3672228
  have htrace : WordTrace (prefixWord ++ tailWord_3672228) baseStart_3672228 baseEnd_3672228 := by
    simpa [prefixWord, tailWord_3672228, baseEnd_3672228] using wordTrace_append hprefix tailTrace_3672228
  have hstable : (prefixWord ++ tailWord_3672228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672228).length < 2 ^ (prefixWord ++ tailWord_3672228).sum := by decide
  have hdescent : baseEnd_3672228 < baseStart_3672228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672251 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 3]
def baseStart_3672251 : Nat := 118140960795 + 3672251 * 2 ^ 59
def prefixEnd_3672251 : Nat := 4983230072969 + 3 ^ 40 * 3672251 * 2
def baseEnd_3672251 : Nat := 1885629846954017034774131

theorem tailTrace_3672251 : CollatzResearch.WordTrace tailWord_3672251 prefixEnd_3672251 1885629846954017034774131 := by
  unfold tailWord_3672251
  simp only [CollatzResearch.WordTrace]
  refine ⟨133937997419069272384312607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89291998279379514922875071 133937997419069272384312607)
  ·
    refine ⟨200906996128603908576468911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133937997419069272384312607 200906996128603908576468911)
    ·
      refine ⟨301360494192905862864703367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200906996128603908576468911 301360494192905862864703367)
      ·
        refine ⟨452040741289358794297055051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301360494192905862864703367 452040741289358794297055051)
        ·
          refine ⟨678061111934038191445582577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452040741289358794297055051 678061111934038191445582577)
          ·
            refine ⟨508545833950528643584186933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678061111934038191445582577 508545833950528643584186933)
            ·
              refine ⟨47676171932862060336017525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508545833950528643584186933 47676171932862060336017525)
              ·
                refine ⟨4469641118705818156501643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47676171932862060336017525 4469641118705818156501643)
                ·
                  refine ⟨6704461678058727234752465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469641118705818156501643 6704461678058727234752465)
                  ·
                    refine ⟨5028346258544045426064349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704461678058727234752465 5028346258544045426064349)
                    ·
                      refine ⟨1885629846954017034774131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028346258544045426064349 1885629846954017034774131)
                      ·
                        rfl

theorem cell23_3672251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 3].length) (baseStart_3672251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672251 prefixEnd_3672251 := by exact prefixLift 3672251
  have htrace : WordTrace (prefixWord ++ tailWord_3672251) baseStart_3672251 baseEnd_3672251 := by
    simpa [prefixWord, tailWord_3672251, baseEnd_3672251] using wordTrace_append hprefix tailTrace_3672251
  have hstable : (prefixWord ++ tailWord_3672251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672251).length < 2 ^ (prefixWord ++ tailWord_3672251).sum := by decide
  have hdescent : baseEnd_3672251 < baseStart_3672251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672278 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3672278 : Nat := 118140960795 + 3672278 * 2 ^ 59
def prefixEnd_3672278 : Nat := 4983230072969 + 3 ^ 40 * 3672278 * 2
def baseEnd_3672278 : Nat := 1885643710931688429136507

theorem tailTrace_3672278 : CollatzResearch.WordTrace tailWord_3672278 prefixEnd_3672278 1885643710931688429136507 := by
  unfold tailWord_3672278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371186386873215999721593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89292654793314303997030325 8371186386873215999721593)
  ·
    refine ⟨6278389790154911999791195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8371186386873215999721593 6278389790154911999791195)
    ·
      refine ⟨9417584685232367999686793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278389790154911999791195 9417584685232367999686793)
      ·
        refine ⟨7063188513924275999765095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9417584685232367999686793 7063188513924275999765095)
        ·
          refine ⟨10594782770886413999647643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063188513924275999765095 10594782770886413999647643)
          ·
            refine ⟨15892174156329620999471465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594782770886413999647643 15892174156329620999471465)
            ·
              refine ⟨11919130617247215749603599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15892174156329620999471465 11919130617247215749603599)
              ·
                refine ⟨17878695925870823624405399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919130617247215749603599 17878695925870823624405399)
                ·
                  refine ⟨26818043888806235436608099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17878695925870823624405399 26818043888806235436608099)
                  ·
                    refine ⟨40227065833209353154912149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26818043888806235436608099 40227065833209353154912149)
                    ·
                      refine ⟨1885643710931688429136507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40227065833209353154912149 1885643710931688429136507)
                      ·
                        rfl

theorem cell23_3672278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3672278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672278 prefixEnd_3672278 := by exact prefixLift 3672278
  have htrace : WordTrace (prefixWord ++ tailWord_3672278) baseStart_3672278 baseEnd_3672278 := by
    simpa [prefixWord, tailWord_3672278, baseEnd_3672278] using wordTrace_append hprefix tailTrace_3672278
  have hstable : (prefixWord ++ tailWord_3672278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672278).length < 2 ^ (prefixWord ++ tailWord_3672278).sum := by decide
  have hdescent : baseEnd_3672278 < baseStart_3672278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
