import V185TrunkScan23Chunk0550

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3256524 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3256524 : Nat := 118140960795 + 3256524 * 2 ^ 59
def prefixEnd_3256524 : Nat := 4983230072969 + 3 ^ 40 * 3256524 * 2
def baseEnd_3256524 : Nat := 1672162074902322068573525

theorem tailTrace_3256524 : CollatzResearch.WordTrace tailWord_3256524 prefixEnd_3256524 1672162074902322068573525 := by
  unfold tailWord_3256524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59387594027088596432676313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79183458702784795243568417 59387594027088596432676313)
  ·
    refine ⟨44540695520316447324507235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59387594027088596432676313 44540695520316447324507235)
    ·
      refine ⟨66811043280474670986760853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44540695520316447324507235 66811043280474670986760853)
      ·
        refine ⟨3131767653772250202504415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66811043280474670986760853 3131767653772250202504415)
        ·
          refine ⟨4697651480658375303756623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131767653772250202504415 4697651480658375303756623)
          ·
            refine ⟨7046477220987562955634935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697651480658375303756623 7046477220987562955634935)
            ·
              refine ⟨10569715831481344433452403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046477220987562955634935 10569715831481344433452403)
              ·
                refine ⟨15854573747222016650178605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569715831481344433452403 15854573747222016650178605)
                ·
                  refine ⟨5945465155208256243816977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15854573747222016650178605 5945465155208256243816977)
                  ·
                    refine ⟨4459098866406192182862733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945465155208256243816977 4459098866406192182862733)
                    ·
                      refine ⟨1672162074902322068573525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459098866406192182862733 1672162074902322068573525)
                      ·
                        rfl

theorem cell23_3256524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3256524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256524 prefixEnd_3256524 := by exact prefixLift 3256524
  have htrace : WordTrace (prefixWord ++ tailWord_3256524) baseStart_3256524 baseEnd_3256524 := by
    simpa [prefixWord, tailWord_3256524, baseEnd_3256524] using wordTrace_append hprefix tailTrace_3256524
  have hstable : (prefixWord ++ tailWord_3256524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256524).length < 2 ^ (prefixWord ++ tailWord_3256524).sum := by decide
  have hdescent : baseEnd_3256524 < baseStart_3256524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256534 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3256534 : Nat := 118140960795 + 3256534 * 2 ^ 59
def prefixEnd_3256534 : Nat := 4983230072969 + 3 ^ 40 * 3256534 * 2
def baseEnd_3256534 : Nat := 1672167209708867029448479

theorem tailTrace_3256534 : CollatzResearch.WordTrace tailWord_3256534 prefixEnd_3256534 1672167209708867029448479 := by
  unfold tailWord_3256534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423472049008810285826041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79183701856093976382144437 7423472049008810285826041)
  ·
    refine ⟨5567604036756607714369531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7423472049008810285826041 5567604036756607714369531)
    ·
      refine ⟨8351406055134911571554297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5567604036756607714369531 8351406055134911571554297)
      ·
        refine ⟨6263554541351183678665723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8351406055134911571554297 6263554541351183678665723)
        ·
          refine ⟨9395331812026775517998585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263554541351183678665723 9395331812026775517998585)
          ·
            refine ⟨7046498859020081638498939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9395331812026775517998585 7046498859020081638498939)
            ·
              refine ⟨10569748288530122457748409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046498859020081638498939 10569748288530122457748409)
              ·
                refine ⟨7927311216397591843311307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10569748288530122457748409 7927311216397591843311307)
                ·
                  refine ⟨11890966824596387764966961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927311216397591843311307 11890966824596387764966961)
                  ·
                    refine ⟨8918225118447290823725221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11890966824596387764966961 8918225118447290823725221)
                    ·
                      refine ⟨1672167209708867029448479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8918225118447290823725221 1672167209708867029448479)
                      ·
                        rfl

theorem cell23_3256534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3256534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256534 prefixEnd_3256534 := by exact prefixLift 3256534
  have htrace : WordTrace (prefixWord ++ tailWord_3256534) baseStart_3256534 baseEnd_3256534 := by
    simpa [prefixWord, tailWord_3256534, baseEnd_3256534] using wordTrace_append hprefix tailTrace_3256534
  have hstable : (prefixWord ++ tailWord_3256534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256534).length < 2 ^ (prefixWord ++ tailWord_3256534).sum := by decide
  have hdescent : baseEnd_3256534 < baseStart_3256534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256541 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3256541 : Nat := 118140960795 + 3256541 * 2 ^ 59
def prefixEnd_3256541 : Nat := 4983230072969 + 3 ^ 40 * 3256541 * 2
def baseEnd_3256541 : Nat := 1672170804073448502060947

theorem tailTrace_3256541 : CollatzResearch.WordTrace tailWord_3256541 prefixEnd_3256541 1672170804073448502060947 := by
  unfold tailWord_3256541
  simp only [CollatzResearch.WordTrace]
  refine ⟨118775808095115604768721477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79183872063410403179147651 118775808095115604768721477)
  ·
    refine ⟨22270464017834175894135277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118775808095115604768721477 22270464017834175894135277)
    ·
      refine ⟨8351424006687815960300729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22270464017834175894135277 8351424006687815960300729)
      ·
        refine ⟨6263568005015861970225547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8351424006687815960300729 6263568005015861970225547)
        ·
          refine ⟨9395352007523792955338321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263568005015861970225547 9395352007523792955338321)
          ·
            refine ⟨7046514005642844716503741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9395352007523792955338321 7046514005642844716503741)
            ·
              refine ⟨2642442752116066768688903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7046514005642844716503741 2642442752116066768688903)
              ·
                refine ⟨3963664128174100153033355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642442752116066768688903 3963664128174100153033355)
                ·
                  refine ⟨5945496192261150229550033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963664128174100153033355 5945496192261150229550033)
                  ·
                    refine ⟨4459122144195862672162525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945496192261150229550033 4459122144195862672162525)
                    ·
                      refine ⟨1672170804073448502060947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459122144195862672162525 1672170804073448502060947)
                      ·
                        rfl

theorem cell23_3256541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3256541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256541 prefixEnd_3256541 := by exact prefixLift 3256541
  have htrace : WordTrace (prefixWord ++ tailWord_3256541) baseStart_3256541 baseEnd_3256541 := by
    simpa [prefixWord, tailWord_3256541, baseEnd_3256541] using wordTrace_append hprefix tailTrace_3256541
  have hstable : (prefixWord ++ tailWord_3256541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256541).length < 2 ^ (prefixWord ++ tailWord_3256541).sum := by decide
  have hdescent : baseEnd_3256541 < baseStart_3256541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256553 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_3256553 : Nat := 118140960795 + 3256553 * 2 ^ 59
def prefixEnd_3256553 : Nat := 4983230072969 + 3 ^ 40 * 3256553 * 2
def baseEnd_3256553 : Nat := 557392321947100818370297

theorem tailTrace_3256553 : CollatzResearch.WordTrace tailWord_3256553 prefixEnd_3256553 557392321947100818370297 := by
  unfold tailWord_3256553
  simp only [CollatzResearch.WordTrace]
  refine ⟨118776245771072130818158313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79184163847381420545438875 118776245771072130818158313)
  ·
    refine ⟨89082184328304098113618735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118776245771072130818158313 89082184328304098113618735)
    ·
      refine ⟨133623276492456147170428103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89082184328304098113618735 133623276492456147170428103)
      ·
        refine ⟨200434914738684220755642155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133623276492456147170428103 200434914738684220755642155)
        ·
          refine ⟨300652372108026331133463233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200434914738684220755642155 300652372108026331133463233)
          ·
            refine ⟨225489279081019748350097425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300652372108026331133463233 225489279081019748350097425)
            ·
              refine ⟨169116959310764811262573069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225489279081019748350097425 169116959310764811262573069)
              ·
                refine ⟨63418859741536804223464901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169116959310764811262573069 63418859741536804223464901)
                ·
                  refine ⟨11891036201538150791899669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63418859741536804223464901 11891036201538150791899669)
                  ·
                    refine ⟨557392321947100818370297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11891036201538150791899669 557392321947100818370297)
                    ·
                      rfl

theorem cell23_3256553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_3256553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256553 prefixEnd_3256553 := by exact prefixLift 3256553
  have htrace : WordTrace (prefixWord ++ tailWord_3256553) baseStart_3256553 baseEnd_3256553 := by
    simpa [prefixWord, tailWord_3256553, baseEnd_3256553] using wordTrace_append hprefix tailTrace_3256553
  have hstable : (prefixWord ++ tailWord_3256553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256553).length < 2 ^ (prefixWord ++ tailWord_3256553).sum := by decide
  have hdescent : baseEnd_3256553 < baseStart_3256553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256554 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3256554 : Nat := 118140960795 + 3256554 * 2 ^ 59
def prefixEnd_3256554 : Nat := 4983230072969 + 3 ^ 40 * 3256554 * 2
def baseEnd_3256554 : Nat := 1672177479321956951198387

theorem tailTrace_3256554 : CollatzResearch.WordTrace tailWord_3256554 prefixEnd_3256554 1672177479321956951198387 := by
  unfold tailWord_3256554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29694070561017126997236179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79184188162712338659296477 29694070561017126997236179)
  ·
    refine ⟨44541105841525690495854269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29694070561017126997236179 44541105841525690495854269)
    ·
      refine ⟨16702914690572133935945351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44541105841525690495854269 16702914690572133935945351)
      ·
        refine ⟨25054372035858200903918027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16702914690572133935945351 25054372035858200903918027)
        ·
          refine ⟨37581558053787301355877041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25054372035858200903918027 37581558053787301355877041)
          ·
            refine ⟨28186168540340476016907781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37581558053787301355877041 28186168540340476016907781)
            ·
              refine ⟨5284906601313839253170209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28186168540340476016907781 5284906601313839253170209)
              ·
                refine ⟨3963679950985379439877657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5284906601313839253170209 3963679950985379439877657)
                ·
                  refine ⟨2972759963239034579908243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963679950985379439877657 2972759963239034579908243)
                  ·
                    refine ⟨4459139944858551869862365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972759963239034579908243 4459139944858551869862365)
                    ·
                      refine ⟨1672177479321956951198387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459139944858551869862365 1672177479321956951198387)
                      ·
                        rfl

theorem cell23_3256554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3256554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256554 prefixEnd_3256554 := by exact prefixLift 3256554
  have htrace : WordTrace (prefixWord ++ tailWord_3256554) baseStart_3256554 baseEnd_3256554 := by
    simpa [prefixWord, tailWord_3256554, baseEnd_3256554] using wordTrace_append hprefix tailTrace_3256554
  have hstable : (prefixWord ++ tailWord_3256554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256554).length < 2 ^ (prefixWord ++ tailWord_3256554).sum := by decide
  have hdescent : baseEnd_3256554 < baseStart_3256554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256570 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3256570 : Nat := 118140960795 + 3256570 * 2 ^ 59
def prefixEnd_3256570 : Nat := 4983230072969 + 3 ^ 40 * 3256570 * 2
def baseEnd_3256570 : Nat := 557395231670809629532771

theorem tailTrace_3256570 : CollatzResearch.WordTrace tailWord_3256570 prefixEnd_3256570 557395231670809629532771 := by
  unfold tailWord_3256570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29694216453002635680381791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79184577208007028481018109 29694216453002635680381791)
  ·
    refine ⟨44541324679503953520572687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29694216453002635680381791 44541324679503953520572687)
    ·
      refine ⟨66811987019255930280859031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44541324679503953520572687 66811987019255930280859031)
      ·
        refine ⟨100217980528883895421288547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66811987019255930280859031 100217980528883895421288547)
        ·
          refine ⟨150326970793325843131932821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100217980528883895421288547 150326970793325843131932821)
          ·
            refine ⟨7046576755937148896809351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150326970793325843131932821 7046576755937148896809351)
            ·
              refine ⟨10569865133905723345214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046576755937148896809351 10569865133905723345214027)
              ·
                refine ⟨15854797700858585017821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569865133905723345214027 15854797700858585017821041)
                ·
                  refine ⟨11891098275643938763365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15854797700858585017821041 11891098275643938763365781)
                  ·
                    refine ⟨557395231670809629532771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11891098275643938763365781 557395231670809629532771)
                    ·
                      rfl

theorem cell23_3256570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3256570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256570 prefixEnd_3256570 := by exact prefixLift 3256570
  have htrace : WordTrace (prefixWord ++ tailWord_3256570) baseStart_3256570 baseEnd_3256570 := by
    simpa [prefixWord, tailWord_3256570, baseEnd_3256570] using wordTrace_append hprefix tailTrace_3256570
  have hstable : (prefixWord ++ tailWord_3256570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256570).length < 2 ^ (prefixWord ++ tailWord_3256570).sum := by decide
  have hdescent : baseEnd_3256570 < baseStart_3256570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256590 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3256590 : Nat := 118140960795 + 3256590 * 2 ^ 59
def prefixEnd_3256590 : Nat := 4983230072969 + 3 ^ 40 * 3256590 * 2
def baseEnd_3256590 : Nat := 1672195964625518810348221

theorem tailTrace_3256590 : CollatzResearch.WordTrace tailWord_3256590 prefixEnd_3256590 1672195964625518810348221 := by
  unfold tailWord_3256590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847199408992260767156903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79185063514625390758170149 14847199408992260767156903)
  ·
    refine ⟨22270799113488391150735355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14847199408992260767156903 22270799113488391150735355)
    ·
      refine ⟨33406198670232586726103033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22270799113488391150735355 33406198670232586726103033)
      ·
        refine ⟨25054649002674440044577275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33406198670232586726103033 25054649002674440044577275)
        ·
          refine ⟨37581973504011660066865913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25054649002674440044577275 37581973504011660066865913)
          ·
            refine ⟨28186480128008745050149435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37581973504011660066865913 28186480128008745050149435)
            ·
              refine ⟨42279720192013117575224153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28186480128008745050149435 42279720192013117575224153)
              ·
                refine ⟨31709790144009838181418115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42279720192013117575224153 31709790144009838181418115)
                ·
                  refine ⟨47564685216014757272127173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31709790144009838181418115 47564685216014757272127173)
                  ·
                    refine ⟨8918378478002766988523845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47564685216014757272127173 8918378478002766988523845)
                    ·
                      refine ⟨1672195964625518810348221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8918378478002766988523845 1672195964625518810348221)
                      ·
                        rfl

theorem cell23_3256590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3256590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256590 prefixEnd_3256590 := by exact prefixLift 3256590
  have htrace : WordTrace (prefixWord ++ tailWord_3256590) baseStart_3256590 baseEnd_3256590 := by
    simpa [prefixWord, tailWord_3256590, baseEnd_3256590] using wordTrace_append hprefix tailTrace_3256590
  have hstable : (prefixWord ++ tailWord_3256590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256590).length < 2 ^ (prefixWord ++ tailWord_3256590).sum := by decide
  have hdescent : baseEnd_3256590 < baseStart_3256590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256668 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 5]
def baseStart_3256668 : Nat := 118140960795 + 3256668 * 2 ^ 59
def prefixEnd_3256668 : Nat := 4983230072969 + 3 ^ 40 * 3256668 * 2
def baseEnd_3256668 : Nat := 185804001790729945019207

theorem tailTrace_3256668 : CollatzResearch.WordTrace tailWord_3256668 prefixEnd_3256668 185804001790729945019207 := by
  unfold tailWord_3256668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390220082827752729297329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79186960110437003639063105 59390220082827752729297329)
  ·
    refine ⟨44542665062120814546972997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59390220082827752729297329 44542665062120814546972997)
    ·
      refine ⟨8351749699147652727557437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44542665062120814546972997 8351749699147652727557437)
      ·
        refine ⟨3131906137180369772834039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8351749699147652727557437 3131906137180369772834039)
        ·
          refine ⟨4697859205770554659251059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131906137180369772834039 4697859205770554659251059)
          ·
            refine ⟨7046788808655831988876589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697859205770554659251059 7046788808655831988876589)
            ·
              refine ⟨2642545803245936995828721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7046788808655831988876589 2642545803245936995828721)
              ·
                refine ⟨1981909352434452746871541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642545803245936995828721 1981909352434452746871541)
                ·
                  refine ⟨185804001790729945019207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981909352434452746871541 185804001790729945019207)
                  ·
                    rfl

theorem cell23_3256668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_3256668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256668 prefixEnd_3256668 := by exact prefixLift 3256668
  have htrace : WordTrace (prefixWord ++ tailWord_3256668) baseStart_3256668 baseEnd_3256668 := by
    simpa [prefixWord, tailWord_3256668, baseEnd_3256668] using wordTrace_append hprefix tailTrace_3256668
  have hstable : (prefixWord ++ tailWord_3256668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256668).length < 2 ^ (prefixWord ++ tailWord_3256668).sum := by decide
  have hdescent : baseEnd_3256668 < baseStart_3256668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256728 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 1, 4]
def baseStart_3256728 : Nat := 118140960795 + 3256728 * 2 ^ 59
def prefixEnd_3256728 : Nat := 4983230072969 + 3 ^ 40 * 3256728 * 2
def baseEnd_3256728 : Nat := 557422274985279756807529

theorem tailTrace_3256728 : CollatzResearch.WordTrace tailWord_3256728 prefixEnd_3256728 557422274985279756807529 := by
  unfold tailWord_3256728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59391314272719067852889419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79188419030292090470519225 59391314272719067852889419)
  ·
    refine ⟨89086971409078601779334129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59391314272719067852889419 89086971409078601779334129)
    ·
      refine ⟨66815228556808951334500597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89086971409078601779334129 66815228556808951334500597)
      ·
        refine ⟨6263927677200839187609431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66815228556808951334500597 6263927677200839187609431)
        ·
          refine ⟨9395891515801258781414147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263927677200839187609431 9395891515801258781414147)
          ·
            refine ⟨14093837273701888172121221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395891515801258781414147 14093837273701888172121221)
            ·
              refine ⟨2642594488819104032272729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14093837273701888172121221 2642594488819104032272729)
              ·
                refine ⟨1981945866614328024204547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642594488819104032272729 1981945866614328024204547)
                ·
                  refine ⟨2972918799921492036306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981945866614328024204547 2972918799921492036306821)
                  ·
                    refine ⟨557422274985279756807529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972918799921492036306821 557422274985279756807529)
                    ·
                      rfl

theorem cell23_3256728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_3256728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256728 prefixEnd_3256728 := by exact prefixLift 3256728
  have htrace : WordTrace (prefixWord ++ tailWord_3256728) baseStart_3256728 baseEnd_3256728 := by
    simpa [prefixWord, tailWord_3256728, baseEnd_3256728] using wordTrace_append hprefix tailTrace_3256728
  have hstable : (prefixWord ++ tailWord_3256728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256728).length < 2 ^ (prefixWord ++ tailWord_3256728).sum := by decide
  have hdescent : baseEnd_3256728 < baseStart_3256728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256761 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3256761 : Nat := 118140960795 + 3256761 * 2 ^ 59
def prefixEnd_3256761 : Nat := 4983230072969 + 3 ^ 40 * 3256761 * 2
def baseEnd_3256761 : Nat := 1672283769817437641309935

theorem tailTrace_3256761 : CollatzResearch.WordTrace tailWord_3256761 prefixEnd_3256761 1672283769817437641309935 := by
  unfold tailWord_3256761
  simp only [CollatzResearch.WordTrace]
  refine ⟨118783832154318582341730137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79189221436212388227820091 118783832154318582341730137)
  ·
    refine ⟨89087874115738936756297603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118783832154318582341730137 89087874115738936756297603)
    ·
      refine ⟨133631811173608405134446405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89087874115738936756297603 133631811173608405134446405)
      ·
        refine ⟨25055964595051575962708701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133631811173608405134446405 25055964595051575962708701)
        ·
          refine ⟨9395986723144340986015763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25055964595051575962708701 9395986723144340986015763)
          ·
            refine ⟨14093980084716511479023645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395986723144340986015763 14093980084716511479023645)
            ·
              refine ⟨5285242531768691804633867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14093980084716511479023645 5285242531768691804633867)
              ·
                refine ⟨7927863797653037706950801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285242531768691804633867 7927863797653037706950801)
                ·
                  refine ⟨5945897848239778280213101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927863797653037706950801 5945897848239778280213101)
                  ·
                    refine ⟨2229711693089916855079913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5945897848239778280213101 2229711693089916855079913)
                    ·
                      refine ⟨1672283769817437641309935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229711693089916855079913 1672283769817437641309935)
                      ·
                        rfl

theorem cell23_3256761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3256761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256761 prefixEnd_3256761 := by exact prefixLift 3256761
  have htrace : WordTrace (prefixWord ++ tailWord_3256761) baseStart_3256761 baseEnd_3256761 := by
    simpa [prefixWord, tailWord_3256761, baseEnd_3256761] using wordTrace_append hprefix tailTrace_3256761
  have hstable : (prefixWord ++ tailWord_3256761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256761).length < 2 ^ (prefixWord ++ tailWord_3256761).sum := by decide
  have hdescent : baseEnd_3256761 < baseStart_3256761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256797 : List Nat := [1, 4, 3, 1, 1, 1, 2, 10]
def baseStart_3256797 : Nat := 118140960795 + 3256797 * 2 ^ 59
def prefixEnd_3256797 : Nat := 4983230072969 + 3 ^ 40 * 3256797 * 2
def baseEnd_3256797 : Nat := 61937120560037018535547

theorem tailTrace_3256797 : CollatzResearch.WordTrace tailWord_3256797 prefixEnd_3256797 61937120560037018535547 := by
  unfold tailWord_3256797
  simp only [CollatzResearch.WordTrace]
  refine ⟨118785145182188160490040645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79190096788125440326693763 118785145182188160490040645)
  ·
    refine ⟨22272214721660280091882621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118785145182188160490040645 22272214721660280091882621)
    ·
      refine ⟨8352080520622605034455983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22272214721660280091882621 8352080520622605034455983)
      ·
        refine ⟨12528120780933907551683975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352080520622605034455983 12528120780933907551683975)
        ·
          refine ⟨18792181171400861327525963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528120780933907551683975 18792181171400861327525963)
          ·
            refine ⟨28188271757101291991288945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792181171400861327525963 28188271757101291991288945)
            ·
              refine ⟨21141203817825968993466709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28188271757101291991288945 21141203817825968993466709)
              ·
                refine ⟨61937120560037018535547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21141203817825968993466709 61937120560037018535547)
                ·
                  rfl

theorem cell23_3256797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 10].length) (baseStart_3256797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256797 prefixEnd_3256797 := by exact prefixLift 3256797
  have htrace : WordTrace (prefixWord ++ tailWord_3256797) baseStart_3256797 baseEnd_3256797 := by
    simpa [prefixWord, tailWord_3256797, baseEnd_3256797] using wordTrace_append hprefix tailTrace_3256797
  have hstable : (prefixWord ++ tailWord_3256797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256797).length < 2 ^ (prefixWord ++ tailWord_3256797).sum := by decide
  have hdescent : baseEnd_3256797 < baseStart_3256797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256801 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_3256801 : Nat := 118140960795 + 3256801 * 2 ^ 59
def prefixEnd_3256801 : Nat := 4983230072969 + 3 ^ 40 * 3256801 * 2
def baseEnd_3256801 : Nat := 557434769681205828269917

theorem tailTrace_3256801 : CollatzResearch.WordTrace tailWord_3256801 prefixEnd_3256801 557434769681205828269917 := by
  unfold tailWord_3256801
  simp only [CollatzResearch.WordTrace]
  refine ⟨118785291074173669173186257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79190194049449112782124171 118785291074173669173186257)
  ·
    refine ⟨89088968305630251879889693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118785291074173669173186257 89088968305630251879889693)
    ·
      refine ⟨33408363114611344454958635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89088968305630251879889693 33408363114611344454958635)
      ·
        refine ⟨50112544671917016682437953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33408363114611344454958635 50112544671917016682437953)
        ·
          refine ⟨37584408503937762511828465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50112544671917016682437953 37584408503937762511828465)
          ·
            refine ⟨28188306377953321883871349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37584408503937762511828465 28188306377953321883871349)
            ·
              refine ⟨2642653722933123926612939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28188306377953321883871349 2642653722933123926612939)
              ·
                refine ⟨3963980584399685889919409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642653722933123926612939 3963980584399685889919409)
                ·
                  refine ⟨2972985438299764417439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963980584399685889919409 2972985438299764417439557)
                  ·
                    refine ⟨557434769681205828269917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972985438299764417439557 557434769681205828269917)
                    ·
                      rfl

theorem cell23_3256801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_3256801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256801 prefixEnd_3256801 := by exact prefixLift 3256801
  have htrace : WordTrace (prefixWord ++ tailWord_3256801) baseStart_3256801 baseEnd_3256801 := by
    simpa [prefixWord, tailWord_3256801, baseEnd_3256801] using wordTrace_append hprefix tailTrace_3256801
  have hstable : (prefixWord ++ tailWord_3256801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256801).length < 2 ^ (prefixWord ++ tailWord_3256801).sum := by decide
  have hdescent : baseEnd_3256801 < baseStart_3256801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256814 : List Nat := [4, 1, 2, 1, 2, 2, 4, 7]
def baseStart_3256814 : Nat := 118140960795 + 3256814 * 2 ^ 59
def prefixEnd_3256814 : Nat := 4983230072969 + 3 ^ 40 * 3256814 * 2
def baseEnd_3256814 : Nat := 61937443862671330886933

theorem tailTrace_3256814 : CollatzResearch.WordTrace tailWord_3256814 prefixEnd_3256814 61937443862671330886933 := by
  unfold tailWord_3256814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848220652890821549176187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79190510148751048262272997 14848220652890821549176187)
  ·
    refine ⟨22272330979336232323764281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848220652890821549176187 22272330979336232323764281)
    ·
      refine ⟨16704248234502174242823211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22272330979336232323764281 16704248234502174242823211)
      ·
        refine ⟨25056372351753261364234817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16704248234502174242823211 25056372351753261364234817)
        ·
          refine ⟨18792279263814946023176113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25056372351753261364234817 18792279263814946023176113)
          ·
            refine ⟨14094209447861209517382085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18792279263814946023176113 14094209447861209517382085)
            ·
              refine ⟨2642664271473976784509141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14094209447861209517382085 2642664271473976784509141)
              ·
                refine ⟨61937443862671330886933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2642664271473976784509141 61937443862671330886933)
                ·
                  rfl

theorem cell23_3256814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_3256814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256814 prefixEnd_3256814 := by exact prefixLift 3256814
  have htrace : WordTrace (prefixWord ++ tailWord_3256814) baseStart_3256814 baseEnd_3256814 := by
    simpa [prefixWord, tailWord_3256814, baseEnd_3256814] using wordTrace_append hprefix tailTrace_3256814
  have hstable : (prefixWord ++ tailWord_3256814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256814).length < 2 ^ (prefixWord ++ tailWord_3256814).sum := by decide
  have hdescent : baseEnd_3256814 < baseStart_3256814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256824 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_3256824 : Nat := 118140960795 + 3256824 * 2 ^ 59
def prefixEnd_3256824 : Nat := 4983230072969 + 3 ^ 40 * 3256824 * 2
def baseEnd_3256824 : Nat := 1672316119098670894822145

theorem tailTrace_3256824 : CollatzResearch.WordTrace tailWord_3256824 prefixEnd_3256824 1672316119098670894822145 := by
  unfold tailWord_3256824
  simp only [CollatzResearch.WordTrace]
  refine ⟨59393064976545172050636763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79190753302060229400849017 59393064976545172050636763)
  ·
    refine ⟨89089597464817758075955145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59393064976545172050636763 89089597464817758075955145)
    ·
      refine ⟨66817198098613318556966359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89089597464817758075955145 66817198098613318556966359)
      ·
        refine ⟨100225797147919977835449539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66817198098613318556966359 100225797147919977835449539)
        ·
          refine ⟨150338695721879966753174309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100225797147919977835449539 150338695721879966753174309)
          ·
            refine ⟨28188505447852493766220183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150338695721879966753174309 28188505447852493766220183)
            ·
              refine ⟨42282758171778740649330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28188505447852493766220183 42282758171778740649330275)
              ·
                refine ⟨63424137257668110973995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42282758171778740649330275 63424137257668110973995413)
                ·
                  refine ⟨2973006433953192701906035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63424137257668110973995413 2973006433953192701906035)
                  ·
                    refine ⟨4459509650929789052859053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2973006433953192701906035 4459509650929789052859053)
                    ·
                      refine ⟨1672316119098670894822145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459509650929789052859053 1672316119098670894822145)
                      ·
                        rfl

theorem cell23_3256824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_3256824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256824 prefixEnd_3256824 := by exact prefixLift 3256824
  have htrace : WordTrace (prefixWord ++ tailWord_3256824) baseStart_3256824 baseEnd_3256824 := by
    simpa [prefixWord, tailWord_3256824, baseEnd_3256824] using wordTrace_append hprefix tailTrace_3256824
  have hstable : (prefixWord ++ tailWord_3256824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256824).length < 2 ^ (prefixWord ++ tailWord_3256824).sum := by decide
  have hdescent : baseEnd_3256824 < baseStart_3256824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256838 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3256838 : Nat := 118140960795 + 3256838 * 2 ^ 59
def prefixEnd_3256838 : Nat := 4983230072969 + 3 ^ 40 * 3256838 * 2
def baseEnd_3256838 : Nat := 1672323307827833840047081

theorem tailTrace_3256838 : CollatzResearch.WordTrace tailWord_3256838 prefixEnd_3256838 1672323307827833840047081 := by
  unfold tailWord_3256838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712082517969988265383849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79191093716693082994855445 3712082517969988265383849)
  ·
    refine ⟨2784061888477491199037887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3712082517969988265383849 2784061888477491199037887)
    ·
      refine ⟨4176092832716236798556831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784061888477491199037887 4176092832716236798556831)
      ·
        refine ⟨6264139249074355197835247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176092832716236798556831 6264139249074355197835247)
        ·
          refine ⟨9396208873611532796752871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264139249074355197835247 9396208873611532796752871)
          ·
            refine ⟨14094313310417299195129307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396208873611532796752871 14094313310417299195129307)
            ·
              refine ⟨21141469965625948792693961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14094313310417299195129307 21141469965625948792693961)
              ·
                refine ⟨15856102474219461594520471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21141469965625948792693961 15856102474219461594520471)
                ·
                  refine ⟨23784153711329192391780707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15856102474219461594520471 23784153711329192391780707)
                  ·
                    refine ⟨35676230566993788587671061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23784153711329192391780707 35676230566993788587671061)
                    ·
                      refine ⟨1672323307827833840047081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35676230566993788587671061 1672323307827833840047081)
                      ·
                        rfl

theorem cell23_3256838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3256838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256838 prefixEnd_3256838 := by exact prefixLift 3256838
  have htrace : WordTrace (prefixWord ++ tailWord_3256838) baseStart_3256838 baseEnd_3256838 := by
    simpa [prefixWord, tailWord_3256838, baseEnd_3256838] using wordTrace_append hprefix tailTrace_3256838
  have hstable : (prefixWord ++ tailWord_3256838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256838).length < 2 ^ (prefixWord ++ tailWord_3256838).sum := by decide
  have hdescent : baseEnd_3256838 < baseStart_3256838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256858 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_3256858 : Nat := 118140960795 + 3256858 * 2 ^ 59
def prefixEnd_3256858 : Nat := 4983230072969 + 3 ^ 40 * 3256858 * 2
def baseEnd_3256858 : Nat := 1672333577440923761796989

theorem tailTrace_3256858 : CollatzResearch.WordTrace tailWord_3256858 prefixEnd_3256858 1672333577440923761796989 := by
  unfold tailWord_3256858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29696842508741791977002807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79191580023311445272007485 29696842508741791977002807)
  ·
    refine ⟨44545263763112687965504211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29696842508741791977002807 44545263763112687965504211)
    ·
      refine ⟨66817895644669031948256317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44545263763112687965504211 66817895644669031948256317)
      ·
        refine ⟨25056710866750886980596119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66817895644669031948256317 25056710866750886980596119)
        ·
          refine ⟨37585066300126330470894179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25056710866750886980596119 37585066300126330470894179)
          ·
            refine ⟨56377599450189495706341269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37585066300126330470894179 56377599450189495706341269)
            ·
              refine ⟨2642699974227632611234747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56377599450189495706341269 2642699974227632611234747)
              ·
                refine ⟨3964049961341448916852121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642699974227632611234747 3964049961341448916852121)
                ·
                  refine ⟨2973037471006086687639091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964049961341448916852121 2973037471006086687639091)
                  ·
                    refine ⟨4459556206509130031458637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2973037471006086687639091 4459556206509130031458637)
                    ·
                      refine ⟨1672333577440923761796989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459556206509130031458637 1672333577440923761796989)
                      ·
                        rfl

theorem cell23_3256858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_3256858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256858 prefixEnd_3256858 := by exact prefixLift 3256858
  have htrace : WordTrace (prefixWord ++ tailWord_3256858) baseStart_3256858 baseEnd_3256858 := by
    simpa [prefixWord, tailWord_3256858, baseEnd_3256858] using wordTrace_append hprefix tailTrace_3256858
  have hstable : (prefixWord ++ tailWord_3256858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256858).length < 2 ^ (prefixWord ++ tailWord_3256858).sum := by decide
  have hdescent : baseEnd_3256858 < baseStart_3256858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256881 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_3256881 : Nat := 118140960795 + 3256881 * 2 ^ 59
def prefixEnd_3256881 : Nat := 4983230072969 + 3 ^ 40 * 3256881 * 2
def baseEnd_3256881 : Nat := 1672345387495977171809383

theorem tailTrace_3256881 : CollatzResearch.WordTrace tailWord_3256881 prefixEnd_3256881 1672345387495977171809383 := by
  unfold tailWord_3256881
  simp only [CollatzResearch.WordTrace]
  refine ⟨118788208913883842836098497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79192139275922561890732331 118788208913883842836098497)
  ·
    refine ⟨89091156685412882127073873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118788208913883842836098497 89091156685412882127073873)
    ·
      refine ⟨66818367514059661595305405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89091156685412882127073873 66818367514059661595305405)
      ·
        refine ⟨25056887817772373098239527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66818367514059661595305405 25056887817772373098239527)
        ·
          refine ⟨37585331726658559647359291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25056887817772373098239527 37585331726658559647359291)
          ·
            refine ⟨56377997589987839471038937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37585331726658559647359291 56377997589987839471038937)
            ·
              refine ⟨42283498192490879603279203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56377997589987839471038937 42283498192490879603279203)
              ·
                refine ⟨63425247288736319404918805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42283498192490879603279203 63425247288736319404918805)
                ·
                  refine ⟨2973058466659514972105569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63425247288736319404918805 2973058466659514972105569)
                  ·
                    refine ⟨2229793849994636229079177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973058466659514972105569 2229793849994636229079177)
                    ·
                      refine ⟨1672345387495977171809383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229793849994636229079177 1672345387495977171809383)
                      ·
                        rfl

theorem cell23_3256881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_3256881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256881 prefixEnd_3256881 := by exact prefixLift 3256881
  have htrace : WordTrace (prefixWord ++ tailWord_3256881) baseStart_3256881 baseEnd_3256881 := by
    simpa [prefixWord, tailWord_3256881, baseEnd_3256881] using wordTrace_append hprefix tailTrace_3256881
  have hstable : (prefixWord ++ tailWord_3256881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256881).length < 2 ^ (prefixWord ++ tailWord_3256881).sum := by decide
  have hdescent : baseEnd_3256881 < baseStart_3256881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256927 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3256927 : Nat := 118140960795 + 3256927 * 2 ^ 59
def prefixEnd_3256927 : Nat := 4983230072969 + 3 ^ 40 * 3256927 * 2
def baseEnd_3256927 : Nat := 1672369007606083991834171

theorem tailTrace_3256927 : CollatzResearch.WordTrace tailWord_3256927 prefixEnd_3256927 1672369007606083991834171 := by
  unfold tailWord_3256927
  simp only [CollatzResearch.WordTrace]
  refine ⟨118789886671717192692273035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79193257781144795128182023 118789886671717192692273035)
  ·
    refine ⟨178184830007575789038409553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118789886671717192692273035 178184830007575789038409553)
    ·
      refine ⟨133638622505681841778807165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178184830007575789038409553 133638622505681841778807165)
      ·
        refine ⟨50114483439630690667052687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133638622505681841778807165 50114483439630690667052687)
        ·
          refine ⟨75171725159446036000579031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50114483439630690667052687 75171725159446036000579031)
          ·
            refine ⟨112757587739169054000868547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75171725159446036000579031 112757587739169054000868547)
            ·
              refine ⟨169136381608753581001302821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112757587739169054000868547 169136381608753581001302821)
              ·
                refine ⟨31713071551641296437744279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169136381608753581001302821 31713071551641296437744279)
                ·
                  refine ⟨47569607327461944656616419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31713071551641296437744279 47569607327461944656616419)
                  ·
                    refine ⟨71354410991192916984924629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47569607327461944656616419 71354410991192916984924629)
                    ·
                      refine ⟨1672369007606083991834171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71354410991192916984924629 1672369007606083991834171)
                      ·
                        rfl

theorem cell23_3256927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3256927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256927 prefixEnd_3256927 := by exact prefixLift 3256927
  have htrace : WordTrace (prefixWord ++ tailWord_3256927) baseStart_3256927 baseEnd_3256927 := by
    simpa [prefixWord, tailWord_3256927, baseEnd_3256927] using wordTrace_append hprefix tailTrace_3256927
  have hstable : (prefixWord ++ tailWord_3256927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256927).length < 2 ^ (prefixWord ++ tailWord_3256927).sum := by decide
  have hdescent : baseEnd_3256927 < baseStart_3256927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256949 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3256949 : Nat := 118140960795 + 3256949 * 2 ^ 59
def prefixEnd_3256949 : Nat := 4983230072969 + 3 ^ 40 * 3256949 * 2
def baseEnd_3256949 : Nat := 1672380304180482905759071

theorem tailTrace_3256949 : CollatzResearch.WordTrace tailWord_3256949 prefixEnd_3256949 1672380304180482905759071 := by
  unfold tailWord_3256949
  simp only [CollatzResearch.WordTrace]
  refine ⟨118790689077637490449573901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79193792718424993633049267 118790689077637490449573901)
  ·
    refine ⟨44546508404114058918590213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118790689077637490449573901 44546508404114058918590213)
    ·
      refine ⟨8352470325771386047235665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44546508404114058918590213 8352470325771386047235665)
      ·
        refine ⟨6264352744328539535426749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8352470325771386047235665 6264352744328539535426749)
        ·
          refine ⟨2349132279123202325785031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6264352744328539535426749 2349132279123202325785031)
          ·
            refine ⟨3523698418684803488677547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349132279123202325785031 3523698418684803488677547)
            ·
              refine ⟨5285547628027205233016321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523698418684803488677547 5285547628027205233016321)
              ·
                refine ⟨3964160721020403924762241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285547628027205233016321 3964160721020403924762241)
                ·
                  refine ⟨2973120540765302943571681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964160721020403924762241 2973120540765302943571681)
                  ·
                    refine ⟨2229840405573977207678761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973120540765302943571681 2229840405573977207678761)
                    ·
                      refine ⟨1672380304180482905759071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229840405573977207678761 1672380304180482905759071)
                      ·
                        rfl

theorem cell23_3256949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3256949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256949 prefixEnd_3256949 := by exact prefixLift 3256949
  have htrace : WordTrace (prefixWord ++ tailWord_3256949) baseStart_3256949 baseEnd_3256949 := by
    simpa [prefixWord, tailWord_3256949, baseEnd_3256949] using wordTrace_append hprefix tailTrace_3256949
  have hstable : (prefixWord ++ tailWord_3256949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256949).length < 2 ^ (prefixWord ++ tailWord_3256949).sum := by decide
  have hdescent : baseEnd_3256949 < baseStart_3256949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256984 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3256984 : Nat := 118140960795 + 3256984 * 2 ^ 59
def prefixEnd_3256984 : Nat := 4983230072969 + 3 ^ 40 * 3256984 * 2
def baseEnd_3256984 : Nat := 1672398276003390268821409

theorem tailTrace_3256984 : CollatzResearch.WordTrace tailWord_3256984 prefixEnd_3256984 1672398276003390268821409 := by
  unfold tailWord_3256984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59395982816255345713549003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79194643755007127618065337 59395982816255345713549003)
  ·
    refine ⟨89093974224383018570323505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59395982816255345713549003 89093974224383018570323505)
    ·
      refine ⟨66820480668287263927742629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89093974224383018570323505 66820480668287263927742629)
      ·
        refine ⟨12528840125303861986451743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66820480668287263927742629 12528840125303861986451743)
        ·
          refine ⟨18793260187955792979677615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528840125303861986451743 18793260187955792979677615)
          ·
            refine ⟨28189890281933689469516423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18793260187955792979677615 28189890281933689469516423)
            ·
              refine ⟨42284835422900534204274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28189890281933689469516423 42284835422900534204274635)
              ·
                refine ⟨63427253134350801306411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42284835422900534204274635 63427253134350801306411953)
                ·
                  refine ⟨47570439850763100979808965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63427253134350801306411953 47570439850763100979808965)
                  ·
                    refine ⟨8919457472018081433714181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47570439850763100979808965 8919457472018081433714181)
                    ·
                      refine ⟨1672398276003390268821409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8919457472018081433714181 1672398276003390268821409)
                      ·
                        rfl

theorem cell23_3256984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3256984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256984 prefixEnd_3256984 := by exact prefixLift 3256984
  have htrace : WordTrace (prefixWord ++ tailWord_3256984) baseStart_3256984 baseEnd_3256984 := by
    simpa [prefixWord, tailWord_3256984, baseEnd_3256984] using wordTrace_append hprefix tailTrace_3256984
  have hstable : (prefixWord ++ tailWord_3256984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256984).length < 2 ^ (prefixWord ++ tailWord_3256984).sum := by decide
  have hdescent : baseEnd_3256984 < baseStart_3256984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257015 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 3, 4]
def baseStart_3257015 : Nat := 118140960795 + 3257015 * 2 ^ 59
def prefixEnd_3257015 : Nat := 4983230072969 + 3 ^ 40 * 3257015 * 2
def baseEnd_3257015 : Nat := 557471397967893215844589

theorem tailTrace_3257015 : CollatzResearch.WordTrace tailWord_3257015 prefixEnd_3257015 557471397967893215844589 := by
  unfold tailWord_3257015
  simp only [CollatzResearch.WordTrace]
  refine ⟨118793096295398383721476499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79195397530265589147650999 118793096295398383721476499)
  ·
    refine ⟨178189644443097575582214749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118793096295398383721476499 178189644443097575582214749)
    ·
      refine ⟨66821116666161590843330531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178189644443097575582214749 66821116666161590843330531)
      ·
        refine ⟨100231674999242386264995797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66821116666161590843330531 100231674999242386264995797)
        ·
          refine ⟨2349179882794743428085839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100231674999242386264995797 2349179882794743428085839)
          ·
            refine ⟨3523769824192115142128759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349179882794743428085839 3523769824192115142128759)
            ·
              refine ⟨5285654736288172713193139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523769824192115142128759 5285654736288172713193139)
              ·
                refine ⟨7928482104432259069789709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285654736288172713193139 7928482104432259069789709)
                ·
                  refine ⟨2973180789162097151171141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7928482104432259069789709 2973180789162097151171141)
                  ·
                    refine ⟨557471397967893215844589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973180789162097151171141 557471397967893215844589)
                    ·
                      rfl

theorem cell23_3257015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_3257015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257015 prefixEnd_3257015 := by exact prefixLift 3257015
  have htrace : WordTrace (prefixWord ++ tailWord_3257015) baseStart_3257015 baseEnd_3257015 := by
    simpa [prefixWord, tailWord_3257015, baseEnd_3257015] using wordTrace_append hprefix tailTrace_3257015
  have hstable : (prefixWord ++ tailWord_3257015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257015).length < 2 ^ (prefixWord ++ tailWord_3257015).sum := by decide
  have hdescent : baseEnd_3257015 < baseStart_3257015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257028 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 6]
def baseStart_3257028 : Nat := 118140960795 + 3257028 * 2 ^ 59
def prefixEnd_3257028 : Nat := 4983230072969 + 3 ^ 40 * 3257028 * 2
def baseEnd_3257028 : Nat := 185824541016909788519023

theorem tailTrace_3257028 : CollatzResearch.WordTrace tailWord_3257028 prefixEnd_3257028 185824541016909788519023 := by
  unfold tailWord_3257028
  simp only [CollatzResearch.WordTrace]
  refine ⟨59396785222175643470849869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79195713629567524627799825 59396785222175643470849869)
  ·
    refine ⟨22273794458315866301568701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59396785222175643470849869 22273794458315866301568701)
    ·
      refine ⟨8352672921868449863088263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22273794458315866301568701 8352672921868449863088263)
      ·
        refine ⟨12529009382802674794632395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352672921868449863088263 12529009382802674794632395)
        ·
          refine ⟨18793514074204012191948593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12529009382802674794632395 18793514074204012191948593)
          ·
            refine ⟨14095135555653009143961445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18793514074204012191948593 14095135555653009143961445)
            ·
              refine ⟨2642837916684939214492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14095135555653009143961445 2642837916684939214492771)
              ·
                refine ⟨3964256875027408821739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642837916684939214492771 3964256875027408821739157)
                ·
                  refine ⟨185824541016909788519023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3964256875027408821739157 185824541016909788519023)
                  ·
                    rfl

theorem cell23_3257028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_3257028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257028 prefixEnd_3257028 := by exact prefixLift 3257028
  have htrace : WordTrace (prefixWord ++ tailWord_3257028) baseStart_3257028 baseEnd_3257028 := by
    simpa [prefixWord, tailWord_3257028, baseEnd_3257028] using wordTrace_append hprefix tailTrace_3257028
  have hstable : (prefixWord ++ tailWord_3257028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257028).length < 2 ^ (prefixWord ++ tailWord_3257028).sum := by decide
  have hdescent : baseEnd_3257028 < baseStart_3257028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257031 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_3257031 : Nat := 118140960795 + 3257031 * 2 ^ 59
def prefixEnd_3257031 : Nat := 4983230072969 + 3 ^ 40 * 3257031 * 2
def baseEnd_3257031 : Nat := 1672422409594151584933693

theorem tailTrace_3257031 : CollatzResearch.WordTrace tailWord_3257031 prefixEnd_3257031 1672422409594151584933693 := by
  unfold tailWord_3257031
  simp only [CollatzResearch.WordTrace]
  refine ⟨118793679863340418454058947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79195786575560278969372631 118793679863340418454058947)
  ·
    refine ⟨178190519795010627681088421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118793679863340418454058947 178190519795010627681088421)
    ·
      refine ⟨33410722461564492690204079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178190519795010627681088421 33410722461564492690204079)
      ·
        refine ⟨50116083692346739035306119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33410722461564492690204079 50116083692346739035306119)
        ·
          refine ⟨75174125538520108552959179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50116083692346739035306119 75174125538520108552959179)
          ·
            refine ⟨112761188307780162829438769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75174125538520108552959179 112761188307780162829438769)
            ·
              refine ⟨84570891230835122122079077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112761188307780162829438769 84570891230835122122079077)
              ·
                refine ⟨15857042105781585397889827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84570891230835122122079077 15857042105781585397889827)
                ·
                  refine ⟨23785563158672378096834741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15857042105781585397889827 23785563158672378096834741)
                  ·
                    refine ⟨2229896546125535446578257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23785563158672378096834741 2229896546125535446578257)
                    ·
                      refine ⟨1672422409594151584933693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229896546125535446578257 1672422409594151584933693)
                      ·
                        rfl

theorem cell23_3257031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_3257031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257031 prefixEnd_3257031 := by exact prefixLift 3257031
  have htrace : WordTrace (prefixWord ++ tailWord_3257031) baseStart_3257031 baseEnd_3257031 := by
    simpa [prefixWord, tailWord_3257031, baseEnd_3257031] using wordTrace_append hprefix tailTrace_3257031
  have hstable : (prefixWord ++ tailWord_3257031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257031).length < 2 ^ (prefixWord ++ tailWord_3257031).sum := by decide
  have hdescent : baseEnd_3257031 < baseStart_3257031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257048 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_3257048 : Nat := 118140960795 + 3257048 * 2 ^ 59
def prefixEnd_3257048 : Nat := 4983230072969 + 3 ^ 40 * 3257048 * 2
def baseEnd_3257048 : Nat := 1672431138765278018421115

theorem tailTrace_3257048 : CollatzResearch.WordTrace tailWord_3257048 prefixEnd_3257048 1672431138765278018421115 := by
  unfold tailWord_3257048
  simp only [CollatzResearch.WordTrace]
  refine ⟨59397149952139415178713899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79196199936185886904951865 59397149952139415178713899)
  ·
    refine ⟨89095724928209122768070849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59397149952139415178713899 89095724928209122768070849)
    ·
      refine ⟨66821793696156842076053137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89095724928209122768070849 66821793696156842076053137)
      ·
        refine ⟨50116345272117631557039853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66821793696156842076053137 50116345272117631557039853)
        ·
          refine ⟨18793629477044111833889945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50116345272117631557039853 18793629477044111833889945)
          ·
            refine ⟨14095222107783083875417459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18793629477044111833889945 14095222107783083875417459)
            ·
              refine ⟨21142833161674625813126189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14095222107783083875417459 21142833161674625813126189)
              ·
                refine ⟨7928562435627984679922321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21142833161674625813126189 7928562435627984679922321)
                ·
                  refine ⟨5946421826720988509941741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7928562435627984679922321 5946421826720988509941741)
                  ·
                    refine ⟨2229908185020370691228153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5946421826720988509941741 2229908185020370691228153)
                    ·
                      refine ⟨1672431138765278018421115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229908185020370691228153 1672431138765278018421115)
                      ·
                        rfl

theorem cell23_3257048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_3257048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257048 prefixEnd_3257048 := by exact prefixLift 3257048
  have htrace : WordTrace (prefixWord ++ tailWord_3257048) baseStart_3257048 baseEnd_3257048 := by
    simpa [prefixWord, tailWord_3257048, baseEnd_3257048] using wordTrace_append hprefix tailTrace_3257048
  have hstable : (prefixWord ++ tailWord_3257048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257048).length < 2 ^ (prefixWord ++ tailWord_3257048).sum := by decide
  have hdescent : baseEnd_3257048 < baseStart_3257048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257095 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3257095 : Nat := 118140960795 + 3257095 * 2 ^ 59
def prefixEnd_3257095 : Nat := 4983230072969 + 3 ^ 40 * 3257095 * 2
def baseEnd_3257095 : Nat := 1672455272356039334533399

theorem tailTrace_3257095 : CollatzResearch.WordTrace tailWord_3257095 prefixEnd_3257095 1672455272356039334533399 := by
  unfold tailWord_3257095
  simp only [CollatzResearch.WordTrace]
  refine ⟨118796014135108557384388739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79197342756739038256259159 118796014135108557384388739)
  ·
    refine ⟨178194021202662836076583109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118796014135108557384388739 178194021202662836076583109)
    ·
      refine ⟨33411378975499281764359333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178194021202662836076583109 33411378975499281764359333)
      ·
        refine ⟨6264633557906115330817375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33411378975499281764359333 6264633557906115330817375)
        ·
          refine ⟨9396950336859172996226063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264633557906115330817375 9396950336859172996226063)
          ·
            refine ⟨14095425505288759494339095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396950336859172996226063 14095425505288759494339095)
            ·
              refine ⟨21143138257933139241508643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14095425505288759494339095 21143138257933139241508643)
              ·
                refine ⟨31714707386899708862262965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21143138257933139241508643 31714707386899708862262965)
                ·
                  refine ⟨2973253817521847705837153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31714707386899708862262965 2973253817521847705837153)
                  ·
                    refine ⟨2229940363141385779377865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973253817521847705837153 2229940363141385779377865)
                    ·
                      refine ⟨1672455272356039334533399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229940363141385779377865 1672455272356039334533399)
                      ·
                        rfl

theorem cell23_3257095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3257095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257095 prefixEnd_3257095 := by exact prefixLift 3257095
  have htrace : WordTrace (prefixWord ++ tailWord_3257095) baseStart_3257095 baseEnd_3257095 := by
    simpa [prefixWord, tailWord_3257095, baseEnd_3257095] using wordTrace_append hprefix tailTrace_3257095
  have hstable : (prefixWord ++ tailWord_3257095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257095).length < 2 ^ (prefixWord ++ tailWord_3257095).sum := by decide
  have hdescent : baseEnd_3257095 < baseStart_3257095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257098 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3257098 : Nat := 118140960795 + 3257098 * 2 ^ 59
def prefixEnd_3257098 : Nat := 4983230072969 + 3 ^ 40 * 3257098 * 2
def baseEnd_3257098 : Nat := 1672456812798002822795885

theorem tailTrace_3257098 : CollatzResearch.WordTrace tailWord_3257098 prefixEnd_3257098 1672456812798002822795885 := by
  unfold tailWord_3257098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29699030888524422224186987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79197415702731792597831965 29699030888524422224186987)
  ·
    refine ⟨44548546332786633336280481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29699030888524422224186987 44548546332786633336280481)
    ·
      refine ⟨33411409749589975002210361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44548546332786633336280481 33411409749589975002210361)
      ·
        refine ⟨25058557312192481251657771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33411409749589975002210361 25058557312192481251657771)
        ·
          refine ⟨37587835968288721877486657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25058557312192481251657771 37587835968288721877486657)
          ·
            refine ⟨28190876976216541408114993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37587835968288721877486657 28190876976216541408114993)
            ·
              refine ⟨21143157732162406056086245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28190876976216541408114993 21143157732162406056086245)
              ·
                refine ⟨3964342074780451135516171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21143157732162406056086245 3964342074780451135516171)
                ·
                  refine ⟨5946513112170676703274257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964342074780451135516171 5946513112170676703274257)
                  ·
                    refine ⟨4459884834128007527455693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5946513112170676703274257 4459884834128007527455693)
                    ·
                      refine ⟨1672456812798002822795885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459884834128007527455693 1672456812798002822795885)
                      ·
                        rfl

theorem cell23_3257098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3257098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257098 prefixEnd_3257098 := by exact prefixLift 3257098
  have htrace : WordTrace (prefixWord ++ tailWord_3257098) baseStart_3257098 baseEnd_3257098 := by
    simpa [prefixWord, tailWord_3257098, baseEnd_3257098] using wordTrace_append hprefix tailTrace_3257098
  have hstable : (prefixWord ++ tailWord_3257098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257098).length < 2 ^ (prefixWord ++ tailWord_3257098).sum := by decide
  have hdescent : baseEnd_3257098 < baseStart_3257098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257142 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3257142 : Nat := 118140960795 + 3257142 * 2 ^ 59
def prefixEnd_3257142 : Nat := 4983230072969 + 3 ^ 40 * 3257142 * 2
def baseEnd_3257142 : Nat := 1672479405946800650645683

theorem tailTrace_3257142 : CollatzResearch.WordTrace tailWord_3257142 prefixEnd_3257142 1672479405946800650645683 := by
  unfold tailWord_3257142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424858022871142775709355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79198485577292189607566453 7424858022871142775709355)
  ·
    refine ⟨11137287034306714163564033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424858022871142775709355 11137287034306714163564033)
    ·
      refine ⟨8352965275730035622673025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11137287034306714163564033 8352965275730035622673025)
      ·
        refine ⟨6264723956797526717004769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8352965275730035622673025 6264723956797526717004769)
        ·
          refine ⟨4698542967598145037753577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264723956797526717004769 4698542967598145037753577)
          ·
            refine ⟨3523907225698608778315183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698542967598145037753577 3523907225698608778315183)
            ·
              refine ⟨5285860838547913167472775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523907225698608778315183 5285860838547913167472775)
              ·
                refine ⟨7928791257821869751209163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285860838547913167472775 7928791257821869751209163)
                ·
                  refine ⟨11893186886732804626813745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928791257821869751209163 11893186886732804626813745)
                  ·
                    refine ⟨8919890165049603470110309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11893186886732804626813745 8919890165049603470110309)
                    ·
                      refine ⟨1672479405946800650645683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8919890165049603470110309 1672479405946800650645683)
                      ·
                        rfl

theorem cell23_3257142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3257142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257142 prefixEnd_3257142 := by exact prefixLift 3257142
  have htrace : WordTrace (prefixWord ++ tailWord_3257142) baseStart_3257142 baseEnd_3257142 := by
    simpa [prefixWord, tailWord_3257142, baseEnd_3257142] using wordTrace_append hprefix tailTrace_3257142
  have hstable : (prefixWord ++ tailWord_3257142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257142).length < 2 ^ (prefixWord ++ tailWord_3257142).sum := by decide
  have hdescent : baseEnd_3257142 < baseStart_3257142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257155 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 1, 3, 2]
def baseStart_3257155 : Nat := 118140960795 + 3257155 * 2 ^ 59
def prefixEnd_3257155 : Nat := 4983230072969 + 3 ^ 40 * 3257155 * 2
def baseEnd_3257155 : Nat := 1672486081195309099783123

theorem tailTrace_3257155 : CollatzResearch.WordTrace tailWord_3257155 prefixEnd_3257155 1672486081195309099783123 := by
  unfold tailWord_3257155
  simp only [CollatzResearch.WordTrace]
  refine ⟨118798202514891187631572919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79198801676594125087715279 118798202514891187631572919)
  ·
    refine ⟨178197303772336781447359379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118798202514891187631572919 178197303772336781447359379)
    ·
      refine ⟨267295955658505172171039069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178197303772336781447359379 267295955658505172171039069)
      ·
        refine ⟨100235983371939439564139651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267295955658505172171039069 100235983371939439564139651)
        ·
          refine ⟨150353975057909159346209477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100235983371939439564139651 150353975057909159346209477)
          ·
            refine ⟨28191370323357967377414277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150353975057909159346209477 28191370323357967377414277)
            ·
              refine ⟨5285881935629618883265177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28191370323357967377414277 5285881935629618883265177)
              ·
                refine ⟨3964411451722214162448883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285881935629618883265177 3964411451722214162448883)
                ·
                  refine ⟨5946617177583321243673325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964411451722214162448883 5946617177583321243673325)
                  ·
                    refine ⟨2229981441593745466377497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5946617177583321243673325 2229981441593745466377497)
                    ·
                      refine ⟨1672486081195309099783123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229981441593745466377497 1672486081195309099783123)
                      ·
                        rfl

theorem cell23_3257155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_3257155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257155 prefixEnd_3257155 := by exact prefixLift 3257155
  have htrace : WordTrace (prefixWord ++ tailWord_3257155) baseStart_3257155 baseEnd_3257155 := by
    simpa [prefixWord, tailWord_3257155, baseEnd_3257155] using wordTrace_append hprefix tailTrace_3257155
  have hstable : (prefixWord ++ tailWord_3257155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257155).length < 2 ^ (prefixWord ++ tailWord_3257155).sum := by decide
  have hdescent : baseEnd_3257155 < baseStart_3257155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257168 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2]
def baseStart_3257168 : Nat := 118140960795 + 3257168 * 2 ^ 59
def prefixEnd_3257168 : Nat := 4983230072969 + 3 ^ 40 * 3257168 * 2
def baseEnd_3257168 : Nat := 1672492756443817548920563

theorem tailTrace_3257168 : CollatzResearch.WordTrace tailWord_3257168 prefixEnd_3257168 1672492756443817548920563 := by
  unfold tailWord_3257168
  simp only [CollatzResearch.WordTrace]
  refine ⟨59399338331922045425898079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79199117775896060567864105 59399338331922045425898079)
  ·
    refine ⟨89099007497883068138847119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59399338331922045425898079 89099007497883068138847119)
    ·
      refine ⟨133648511246824602208270679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89099007497883068138847119 133648511246824602208270679)
      ·
        refine ⟨200472766870236903312406019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133648511246824602208270679 200472766870236903312406019)
        ·
          refine ⟨300709150305355354968609029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200472766870236903312406019 300709150305355354968609029)
          ·
            refine ⟨56382965682254129056614193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300709150305355354968609029 56382965682254129056614193)
            ·
              refine ⟨42287224261690596792460645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56382965682254129056614193 42287224261690596792460645)
              ·
                refine ⟨7928854549066986898586371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42287224261690596792460645 7928854549066986898586371)
                ·
                  refine ⟨11893281823600480347879557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928854549066986898586371 11893281823600480347879557)
                  ·
                    refine ⟨2229990341925090065227417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11893281823600480347879557 2229990341925090065227417)
                    ·
                      refine ⟨1672492756443817548920563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229990341925090065227417 1672492756443817548920563)
                      ·
                        rfl

theorem cell23_3257168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2].length) (baseStart_3257168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257168 prefixEnd_3257168 := by exact prefixLift 3257168
  have htrace : WordTrace (prefixWord ++ tailWord_3257168) baseStart_3257168 baseEnd_3257168 := by
    simpa [prefixWord, tailWord_3257168, baseEnd_3257168] using wordTrace_append hprefix tailTrace_3257168
  have hstable : (prefixWord ++ tailWord_3257168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257168).length < 2 ^ (prefixWord ++ tailWord_3257168).sum := by decide
  have hdescent : baseEnd_3257168 < baseStart_3257168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257241 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3257241 : Nat := 118140960795 + 3257241 * 2 ^ 59
def prefixEnd_3257241 : Nat := 4983230072969 + 3 ^ 40 * 3257241 * 2
def baseEnd_3257241 : Nat := 1672530240531595763307727

theorem tailTrace_3257241 : CollatzResearch.WordTrace tailWord_3257241 prefixEnd_3257241 1672530240531595763307727 := by
  unfold tailWord_3257241
  simp only [CollatzResearch.WordTrace]
  refine ⟨118801339192579624319203577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79200892795053082879469051 118801339192579624319203577)
  ·
    refine ⟨89101004394434718239402683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118801339192579624319203577 89101004394434718239402683)
    ·
      refine ⟨133651506591652077359104025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89101004394434718239402683 133651506591652077359104025)
      ·
        refine ⟨100238629943739058019328019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133651506591652077359104025 100238629943739058019328019)
        ·
          refine ⟨150357944915608587028992029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100238629943739058019328019 150357944915608587028992029)
          ·
            refine ⟨56384229343353220135872011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150357944915608587028992029 56384229343353220135872011)
            ·
              refine ⟨84576344015029830203808017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56384229343353220135872011 84576344015029830203808017)
              ·
                refine ⟨63432258011272372652856013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84576344015029830203808017 63432258011272372652856013)
                ·
                  refine ⟨23787096754227139744821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63432258011272372652856013 23787096754227139744821005)
                  ·
                    refine ⟨8920161282835177404307877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23787096754227139744821005 8920161282835177404307877)
                    ·
                      refine ⟨1672530240531595763307727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8920161282835177404307877 1672530240531595763307727)
                      ·
                        rfl

theorem cell23_3257241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3257241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257241 prefixEnd_3257241 := by exact prefixLift 3257241
  have htrace : WordTrace (prefixWord ++ tailWord_3257241) baseStart_3257241 baseEnd_3257241 := by
    simpa [prefixWord, tailWord_3257241, baseEnd_3257241] using wordTrace_append hprefix tailTrace_3257241
  have hstable : (prefixWord ++ tailWord_3257241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257241).length < 2 ^ (prefixWord ++ tailWord_3257241).sum := by decide
  have hdescent : baseEnd_3257241 < baseStart_3257241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257302 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3257302 : Nat := 118140960795 + 3257302 * 2 ^ 59
def prefixEnd_3257302 : Nat := 4983230072969 + 3 ^ 40 * 3257302 * 2
def baseEnd_3257302 : Nat := 557520520950506674881649

theorem tailTrace_3257302 : CollatzResearch.WordTrace tailWord_3257302 prefixEnd_3257302 557520520950506674881649 := by
  unfold tailWord_3257302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425222752834914483573385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79202376030239087824782773 7425222752834914483573385)
  ·
    refine ⟨5568917064626185862680039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7425222752834914483573385 5568917064626185862680039)
    ·
      refine ⟨8353375596939278794020059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568917064626185862680039 8353375596939278794020059)
      ·
        refine ⟨12530063395408918191030089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353375596939278794020059 12530063395408918191030089)
        ·
          refine ⟨9397547546556688643272567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12530063395408918191030089 9397547546556688643272567)
          ·
            refine ⟨14096321319835032964908851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397547546556688643272567 14096321319835032964908851)
            ·
              refine ⟨21144481979752549447363277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14096321319835032964908851 21144481979752549447363277)
              ·
                refine ⟨7929180742407206042761229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21144481979752549447363277 7929180742407206042761229)
                ·
                  refine ⟨2973442778402702266035461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7929180742407206042761229 2973442778402702266035461)
                  ·
                    refine ⟨557520520950506674881649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973442778402702266035461 557520520950506674881649)
                    ·
                      rfl

theorem cell23_3257302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3257302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257302 prefixEnd_3257302 := by exact prefixLift 3257302
  have htrace : WordTrace (prefixWord ++ tailWord_3257302) baseStart_3257302 baseEnd_3257302 := by
    simpa [prefixWord, tailWord_3257302, baseEnd_3257302] using wordTrace_append hprefix tailTrace_3257302
  have hstable : (prefixWord ++ tailWord_3257302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257302).length < 2 ^ (prefixWord ++ tailWord_3257302).sum := by decide
  have hdescent : baseEnd_3257302 < baseStart_3257302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257315 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 6]
def baseStart_3257315 : Nat := 118140960795 + 3257315 * 2 ^ 59
def prefixEnd_3257315 : Nat := 4983230072969 + 3 ^ 40 * 3257315 * 2
def baseEnd_3257315 : Nat := 185840915344447608198043

theorem tailTrace_3257315 : CollatzResearch.WordTrace tailWord_3257315 prefixEnd_3257315 185840915344447608198043 := by
  unfold tailWord_3257315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118804038194311534957397399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79202692129541023304931599 118804038194311534957397399)
  ·
    refine ⟨178206057291467302436096099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118804038194311534957397399 178206057291467302436096099)
    ·
      refine ⟨267309085937200953654144149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178206057291467302436096099 267309085937200953654144149)
      ·
        refine ⟨12530113403306294702538007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267309085937200953654144149 12530113403306294702538007)
        ·
          refine ⟨18795170104959442053807011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12530113403306294702538007 18795170104959442053807011)
          ·
            refine ⟨28192755157439163080710517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18795170104959442053807011 28192755157439163080710517)
            ·
              refine ⟨2643070796009921538816611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28192755157439163080710517 2643070796009921538816611)
              ·
                refine ⟨3964606194014882308224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643070796009921538816611 3964606194014882308224917)
                ·
                  refine ⟨185840915344447608198043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3964606194014882308224917 185840915344447608198043)
                  ·
                    rfl

theorem cell23_3257315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 6].length) (baseStart_3257315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257315 prefixEnd_3257315 := by exact prefixLift 3257315
  have htrace : WordTrace (prefixWord ++ tailWord_3257315) baseStart_3257315 baseEnd_3257315 := by
    simpa [prefixWord, tailWord_3257315, baseEnd_3257315] using wordTrace_append hprefix tailTrace_3257315
  have hstable : (prefixWord ++ tailWord_3257315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257315).length < 2 ^ (prefixWord ++ tailWord_3257315).sum := by decide
  have hdescent : baseEnd_3257315 < baseStart_3257315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257345 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3257345 : Nat := 118140960795 + 3257345 * 2 ^ 59
def prefixEnd_3257345 : Nat := 4983230072969 + 3 ^ 40 * 3257345 * 2
def baseEnd_3257345 : Nat := 557527880839887785469083

theorem tailTrace_3257345 : CollatzResearch.WordTrace tailWord_3257345 prefixEnd_3257345 557527880839887785469083 := by
  unfold tailWord_3257345
  simp only [CollatzResearch.WordTrace]
  refine ⟨118805132384202850080989489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79203421589468566720659659 118805132384202850080989489)
  ·
    refine ⟨89103849288152137560742117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118805132384202850080989489 89103849288152137560742117)
    ·
      refine ⟨16706971741528525792639147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89103849288152137560742117 16706971741528525792639147)
      ·
        refine ⟨25060457612292788688958721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16706971741528525792639147 25060457612292788688958721)
        ·
          refine ⟨18795343209219591516719041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25060457612292788688958721 18795343209219591516719041)
          ·
            refine ⟨14096507406914693637539281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18795343209219591516719041 14096507406914693637539281)
            ·
              refine ⟨10572380555186020228154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14096507406914693637539281 10572380555186020228154461)
              ·
                refine ⟨3964642708194757585557923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10572380555186020228154461 3964642708194757585557923)
                ·
                  refine ⟨5946964062292136378336885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964642708194757585557923 5946964062292136378336885)
                  ·
                    refine ⟨557527880839887785469083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5946964062292136378336885 557527880839887785469083)
                    ·
                      rfl

theorem cell23_3257345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3257345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257345 prefixEnd_3257345 := by exact prefixLift 3257345
  have htrace : WordTrace (prefixWord ++ tailWord_3257345) baseStart_3257345 baseEnd_3257345 := by
    simpa [prefixWord, tailWord_3257345, baseEnd_3257345] using wordTrace_append hprefix tailTrace_3257345
  have hstable : (prefixWord ++ tailWord_3257345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257345).length < 2 ^ (prefixWord ++ tailWord_3257345).sum := by decide
  have hdescent : baseEnd_3257345 < baseStart_3257345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257352 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_3257352 : Nat := 118140960795 + 3257352 * 2 ^ 59
def prefixEnd_3257352 : Nat := 4983230072969 + 3 ^ 40 * 3257352 * 2
def baseEnd_3257352 : Nat := 1672587236884244829019717

theorem tailTrace_3257352 : CollatzResearch.WordTrace tailWord_3257352 prefixEnd_3257352 1672587236884244829019717 := by
  unfold tailWord_3257352
  simp only [CollatzResearch.WordTrace]
  refine ⟨59402693847588745138247155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79203591796784993517662873 59402693847588745138247155)
  ·
    refine ⟨89104040771383117707370733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59402693847588745138247155 89104040771383117707370733)
    ·
      refine ⟨33414015289268669140264025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89104040771383117707370733 33414015289268669140264025)
      ·
        refine ⟨25060511466951501855198019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33414015289268669140264025 25060511466951501855198019)
        ·
          refine ⟨37590767200427252782797029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25060511466951501855198019 37590767200427252782797029)
          ·
            refine ⟨7048268850080109896774443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37590767200427252782797029 7048268850080109896774443)
            ·
              refine ⟨10572403275120164845161665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048268850080109896774443 10572403275120164845161665)
              ·
                refine ⟨7929302456340123633871249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572403275120164845161665 7929302456340123633871249)
                ·
                  refine ⟨5946976842255092725403437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929302456340123633871249 5946976842255092725403437)
                  ·
                    refine ⟨2230116315845659772026289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5946976842255092725403437 2230116315845659772026289)
                    ·
                      refine ⟨1672587236884244829019717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230116315845659772026289 1672587236884244829019717)
                      ·
                        rfl

theorem cell23_3257352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_3257352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257352 prefixEnd_3257352 := by exact prefixLift 3257352
  have htrace : WordTrace (prefixWord ++ tailWord_3257352) baseStart_3257352 baseEnd_3257352 := by
    simpa [prefixWord, tailWord_3257352, baseEnd_3257352] using wordTrace_append hprefix tailTrace_3257352
  have hstable : (prefixWord ++ tailWord_3257352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257352).length < 2 ^ (prefixWord ++ tailWord_3257352).sum := by decide
  have hdescent : baseEnd_3257352 < baseStart_3257352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257399 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_3257399 : Nat := 118140960795 + 3257399 * 2 ^ 59
def prefixEnd_3257399 : Nat := 4983230072969 + 3 ^ 40 * 3257399 * 2
def baseEnd_3257399 : Nat := 1672611370475006145132001

theorem tailTrace_3257399 : CollatzResearch.WordTrace tailWord_3257399 prefixEnd_3257399 1672611370475006145132001 := by
  unfold tailWord_3257399
  simp only [CollatzResearch.WordTrace]
  refine ⟨118807101926007217303455251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79204734617338144868970167 118807101926007217303455251)
  ·
    refine ⟨178210652889010825955182877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118807101926007217303455251 178210652889010825955182877)
    ·
      refine ⟨66828994833379059733193579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178210652889010825955182877 66828994833379059733193579)
      ·
        refine ⟨100243492250068589599790369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66828994833379059733193579 100243492250068589599790369)
        ·
          refine ⟨75182619187551442199842777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100243492250068589599790369 75182619187551442199842777)
          ·
            refine ⟨56386964390663581649882083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75182619187551442199842777 56386964390663581649882083)
            ·
              refine ⟨84580446585995372474823125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56386964390663581649882083 84580446585995372474823125)
              ·
                refine ⟨1982354216859266542378667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84580446585995372474823125 1982354216859266542378667)
                ·
                  refine ⟨2973531325288899813568001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982354216859266542378667 2973531325288899813568001)
                  ·
                    refine ⟨2230148493966674860176001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973531325288899813568001 2230148493966674860176001)
                    ·
                      refine ⟨1672611370475006145132001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230148493966674860176001 1672611370475006145132001)
                      ·
                        rfl

theorem cell23_3257399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_3257399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257399 prefixEnd_3257399 := by exact prefixLift 3257399
  have htrace : WordTrace (prefixWord ++ tailWord_3257399) baseStart_3257399 baseEnd_3257399 := by
    simpa [prefixWord, tailWord_3257399, baseEnd_3257399] using wordTrace_append hprefix tailTrace_3257399
  have hstable : (prefixWord ++ tailWord_3257399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257399).length < 2 ^ (prefixWord ++ tailWord_3257399).sum := by decide
  have hdescent : baseEnd_3257399 < baseStart_3257399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257409 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3257409 : Nat := 118140960795 + 3257409 * 2 ^ 59
def prefixEnd_3257409 : Nat := 4983230072969 + 3 ^ 40 * 3257409 * 2
def baseEnd_3257409 : Nat := 557538835093850368668985

theorem tailTrace_3257409 : CollatzResearch.WordTrace tailWord_3257409 prefixEnd_3257409 557538835093850368668985 := by
  unfold tailWord_3257409
  simp only [CollatzResearch.WordTrace]
  refine ⟨118807466655970989011319281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79204977770647326007546187 118807466655970989011319281)
  ·
    refine ⟨89105599991978241758489461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118807466655970989011319281 89105599991978241758489461)
    ·
      refine ⟨8353649999247960164858387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89105599991978241758489461 8353649999247960164858387)
      ·
        refine ⟨12530474998871940247287581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353649999247960164858387 12530474998871940247287581)
        ·
          refine ⟨4698928124576977592732843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12530474998871940247287581 4698928124576977592732843)
          ·
            refine ⟨7048392186865466389099265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698928124576977592732843 7048392186865466389099265)
            ·
              refine ⟨5286294140149099791824449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048392186865466389099265 5286294140149099791824449)
              ·
                refine ⟨3964720605111824843868337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5286294140149099791824449 3964720605111824843868337)
                ·
                  refine ⟨2973540453833868632901253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964720605111824843868337 2973540453833868632901253)
                  ·
                    refine ⟨557538835093850368668985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973540453833868632901253 557538835093850368668985)
                    ·
                      rfl

theorem cell23_3257409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3257409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257409 prefixEnd_3257409 := by exact prefixLift 3257409
  have htrace : WordTrace (prefixWord ++ tailWord_3257409) baseStart_3257409 baseEnd_3257409 := by
    simpa [prefixWord, tailWord_3257409, baseEnd_3257409] using wordTrace_append hprefix tailTrace_3257409
  have hstable : (prefixWord ++ tailWord_3257409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257409).length < 2 ^ (prefixWord ++ tailWord_3257409).sum := by decide
  have hdescent : baseEnd_3257409 < baseStart_3257409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257418 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3257418 : Nat := 118140960795 + 3257418 * 2 ^ 59
def prefixEnd_3257418 : Nat := 4983230072969 + 3 ^ 40 * 3257418 * 2
def baseEnd_3257418 : Nat := 557540375535813856931471

theorem tailTrace_3257418 : CollatzResearch.WordTrace tailWord_3257418 prefixEnd_3257418 557540375535813856931471 := by
  unfold tailWord_3257418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29701948728234595887099227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79205196608625589032264605 29701948728234595887099227)
  ·
    refine ⟨44552923092351893830648841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29701948728234595887099227 44552923092351893830648841)
    ·
      refine ⟨33414692319263920372986631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44552923092351893830648841 33414692319263920372986631)
      ·
        refine ⟨50122038478895880559479947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33414692319263920372986631 50122038478895880559479947)
        ·
          refine ⟨75183057718343820839219921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50122038478895880559479947 75183057718343820839219921)
          ·
            refine ⟨56387293288757865629414941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75183057718343820839219921 56387293288757865629414941)
            ·
              refine ⟨21145234983284199611030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56387293288757865629414941 21145234983284199611030603)
              ·
                refine ⟨31717852474926299416545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21145234983284199611030603 31717852474926299416545905)
                ·
                  refine ⟨23788389356194724562409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31717852474926299416545905 23788389356194724562409429)
                  ·
                    refine ⟨557540375535813856931471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23788389356194724562409429 557540375535813856931471)
                    ·
                      rfl

theorem cell23_3257418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3257418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257418 prefixEnd_3257418 := by exact prefixLift 3257418
  have htrace : WordTrace (prefixWord ++ tailWord_3257418) baseStart_3257418 baseEnd_3257418 := by
    simpa [prefixWord, tailWord_3257418, baseEnd_3257418] using wordTrace_append hprefix tailTrace_3257418
  have hstable : (prefixWord ++ tailWord_3257418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257418).length < 2 ^ (prefixWord ++ tailWord_3257418).sum := by decide
  have hdescent : baseEnd_3257418 < baseStart_3257418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257432 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3257432 : Nat := 118140960795 + 3257432 * 2 ^ 59
def prefixEnd_3257432 : Nat := 4983230072969 + 3 ^ 40 * 3257432 * 2
def baseEnd_3257432 : Nat := 1672628315336604516019349

theorem tailTrace_3257432 : CollatzResearch.WordTrace tailWord_3257432 prefixEnd_3257432 1672628315336604516019349 := by
  unfold tailWord_3257432
  simp only [CollatzResearch.WordTrace]
  refine ⟨59404152767443831969703275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79205537023258442626271033 59404152767443831969703275)
  ·
    refine ⟨89106229151165747954554913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59404152767443831969703275 89106229151165747954554913)
    ·
      refine ⟨66829671863374310965916185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89106229151165747954554913 66829671863374310965916185)
      ·
        refine ⟨50122253897530733224437139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66829671863374310965916185 50122253897530733224437139)
        ·
          refine ⟨75183380846296099836655709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50122253897530733224437139 75183380846296099836655709)
          ·
            refine ⟨28193767817361037438745891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75183380846296099836655709 28193767817361037438745891)
            ·
              refine ⟨42290651726041556158118837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28193767817361037438745891 42290651726041556158118837)
              ·
                refine ⟨3964748599316395889823641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42290651726041556158118837 3964748599316395889823641)
                ·
                  refine ⟨2973561449487296917367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964748599316395889823641 2973561449487296917367731)
                  ·
                    refine ⟨4460342174230945376051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2973561449487296917367731 4460342174230945376051597)
                    ·
                      refine ⟨1672628315336604516019349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4460342174230945376051597 1672628315336604516019349)
                      ·
                        rfl

theorem cell23_3257432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3257432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257432 prefixEnd_3257432 := by exact prefixLift 3257432
  have htrace : WordTrace (prefixWord ++ tailWord_3257432) baseStart_3257432 baseEnd_3257432 := by
    simpa [prefixWord, tailWord_3257432, baseEnd_3257432] using wordTrace_append hprefix tailTrace_3257432
  have hstable : (prefixWord ++ tailWord_3257432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257432).length < 2 ^ (prefixWord ++ tailWord_3257432).sum := by decide
  have hdescent : baseEnd_3257432 < baseStart_3257432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257495 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 7]
def baseStart_3257495 : Nat := 118140960795 + 3257495 * 2 ^ 59
def prefixEnd_3257495 : Nat := 4983230072969 + 3 ^ 40 * 3257495 * 2
def baseEnd_3257495 : Nat := 185851184957537529947951

theorem tailTrace_3257495 : CollatzResearch.WordTrace tailWord_3257495 prefixEnd_3257495 185851184957537529947951 := by
  unfold tailWord_3257495
  simp only [CollatzResearch.WordTrace]
  refine ⟨118810603333659425698949939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79207068889106283799299959 118810603333659425698949939)
  ·
    refine ⟨178215905000489138548424909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118810603333659425698949939 178215905000489138548424909)
    ·
      refine ⟨66830964375183426955659341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178215905000489138548424909 66830964375183426955659341)
      ·
        refine ⟨25061611640693785108372253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66830964375183426955659341 25061611640693785108372253)
        ·
          refine ⟨9398104365260169415639595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25061611640693785108372253 9398104365260169415639595)
          ·
            refine ⟨14097156547890254123459393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398104365260169415639595 14097156547890254123459393)
            ·
              refine ⟨10572867410917690592594545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097156547890254123459393 10572867410917690592594545)
              ·
                refine ⟨7929650558188267944445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572867410917690592594545 7929650558188267944445909)
                ·
                  refine ⟨185851184957537529947951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7929650558188267944445909 185851184957537529947951)
                  ·
                    rfl

theorem cell23_3257495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 7].length) (baseStart_3257495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257495 prefixEnd_3257495 := by exact prefixLift 3257495
  have htrace : WordTrace (prefixWord ++ tailWord_3257495) baseStart_3257495 baseEnd_3257495 := by
    simpa [prefixWord, tailWord_3257495, baseEnd_3257495] using wordTrace_append hprefix tailTrace_3257495
  have hstable : (prefixWord ++ tailWord_3257495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257495).length < 2 ^ (prefixWord ++ tailWord_3257495).sum := by decide
  have hdescent : baseEnd_3257495 < baseStart_3257495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257529 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 5]
def baseStart_3257529 : Nat := 118140960795 + 3257529 * 2 ^ 59
def prefixEnd_3257529 : Nat := 4983230072969 + 3 ^ 40 * 3257529 * 2
def baseEnd_3257529 : Nat := 185853124773343404056267

theorem tailTrace_3257529 : CollatzResearch.WordTrace tailWord_3257529 prefixEnd_3257529 185853124773343404056267 := by
  unfold tailWord_3257529
  simp only [CollatzResearch.WordTrace]
  refine ⟨118811843415536249505687641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79207895610357499670458427 118811843415536249505687641)
  ·
    refine ⟨89108882561652187129265731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118811843415536249505687641 89108882561652187129265731)
    ·
      refine ⟨133663323842478280693898597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89108882561652187129265731 133663323842478280693898597)
      ·
        refine ⟨25061873220464677630105987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133663323842478280693898597 25061873220464677630105987)
        ·
          refine ⟨37592809830697016445158981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061873220464677630105987 37592809830697016445158981)
          ·
            refine ⟨7048651843255690583467309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37592809830697016445158981 7048651843255690583467309)
            ·
              refine ⟨2643244441220883968800241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7048651843255690583467309 2643244441220883968800241)
              ·
                refine ⟨1982433330915662976600181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643244441220883968800241 1982433330915662976600181)
                ·
                  refine ⟨185853124773343404056267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1982433330915662976600181 185853124773343404056267)
                  ·
                    rfl

theorem cell23_3257529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 5].length) (baseStart_3257529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257529 prefixEnd_3257529 := by exact prefixLift 3257529
  have htrace : WordTrace (prefixWord ++ tailWord_3257529) baseStart_3257529 baseEnd_3257529 := by
    simpa [prefixWord, tailWord_3257529, baseEnd_3257529] using wordTrace_append hprefix tailTrace_3257529
  have hstable : (prefixWord ++ tailWord_3257529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257529).length < 2 ^ (prefixWord ++ tailWord_3257529).sum := by decide
  have hdescent : baseEnd_3257529 < baseStart_3257529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257540 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3257540 : Nat := 118140960795 + 3257540 * 2 ^ 59
def prefixEnd_3257540 : Nat := 4983230072969 + 3 ^ 40 * 3257540 * 2
def baseEnd_3257540 : Nat := 1672683771247290093468853

theorem tailTrace_3257540 : CollatzResearch.WordTrace tailWord_3257540 prefixEnd_3257540 1672683771247290093468853 := by
  unfold tailWord_3257540
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406122309248199192169037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79208163078997598922892049 59406122309248199192169037)
  ·
    refine ⟨22277295865968074697063389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59406122309248199192169037 22277295865968074697063389)
    ·
      refine ⟨8353985949738028011398771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22277295865968074697063389 8353985949738028011398771)
      ·
        refine ⟨12530978924607042017098157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353985949738028011398771 12530978924607042017098157)
        ·
          refine ⟨4699117096727640756411809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12530978924607042017098157 4699117096727640756411809)
          ·
            refine ⟨3524337822545730567308857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4699117096727640756411809 3524337822545730567308857)
            ·
              refine ⟨2643253366909297925481643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524337822545730567308857 2643253366909297925481643)
              ·
                refine ⟨3964880050363946888222465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643253366909297925481643 3964880050363946888222465)
                ·
                  refine ⟨2973660037772960166166849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964880050363946888222465 2973660037772960166166849)
                  ·
                    refine ⟨2230245028329720124625137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973660037772960166166849 2230245028329720124625137)
                    ·
                      refine ⟨1672683771247290093468853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230245028329720124625137 1672683771247290093468853)
                      ·
                        rfl

theorem cell23_3257540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3257540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257540 prefixEnd_3257540 := by exact prefixLift 3257540
  have htrace : WordTrace (prefixWord ++ tailWord_3257540) baseStart_3257540 baseEnd_3257540 := by
    simpa [prefixWord, tailWord_3257540, baseEnd_3257540] using wordTrace_append hprefix tailTrace_3257540
  have hstable : (prefixWord ++ tailWord_3257540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257540).length < 2 ^ (prefixWord ++ tailWord_3257540).sum := by decide
  have hdescent : baseEnd_3257540 < baseStart_3257540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_3257562 : Nat := 118140960795 + 3257562 * 2 ^ 59
def prefixEnd_3257562 : Nat := 4983230072969 + 3 ^ 40 * 3257562 * 2
def baseEnd_3257562 : Nat := 1672695067821689007393751

theorem tailTrace_3257562 : CollatzResearch.WordTrace tailWord_3257562 prefixEnd_3257562 1672695067821689007393751 := by
  unfold tailWord_3257562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703261756104174035409735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79208698016277797427759293 29703261756104174035409735)
  ·
    refine ⟨44554892634156261053114603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29703261756104174035409735 44554892634156261053114603)
    ·
      refine ⟨66832338951234391579671905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44554892634156261053114603 66832338951234391579671905)
      ·
        refine ⟨50124254213425793684753929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66832338951234391579671905 50124254213425793684753929)
        ·
          refine ⟨37593190660069345263565447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50124254213425793684753929 37593190660069345263565447)
          ·
            refine ⟨56389785990104017895348171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37593190660069345263565447 56389785990104017895348171)
            ·
              refine ⟨84584678985156026843022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56389785990104017895348171 84584678985156026843022257)
              ·
                refine ⟨63438509238867020132266693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84584678985156026843022257 63438509238867020132266693)
                ·
                  refine ⟨11894720482287566274800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63438509238867020132266693 11894720482287566274800005)
                  ·
                    refine ⟨2230260090428918676525001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11894720482287566274800005 2230260090428918676525001)
                    ·
                      refine ⟨1672695067821689007393751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230260090428918676525001 1672695067821689007393751)
                      ·
                        rfl

theorem cell23_3257562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_3257562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257562 prefixEnd_3257562 := by exact prefixLift 3257562
  have htrace : WordTrace (prefixWord ++ tailWord_3257562) baseStart_3257562 baseEnd_3257562 := by
    simpa [prefixWord, tailWord_3257562, baseEnd_3257562] using wordTrace_append hprefix tailTrace_3257562
  have hstable : (prefixWord ++ tailWord_3257562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257562).length < 2 ^ (prefixWord ++ tailWord_3257562).sum := by decide
  have hdescent : baseEnd_3257562 < baseStart_3257562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257682 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3257682 : Nat := 118140960795 + 3257682 * 2 ^ 59
def prefixEnd_3257682 : Nat := 4983230072969 + 3 ^ 40 * 3257682 * 2
def baseEnd_3257682 : Nat := 1672756685500228537893199

theorem tailTrace_3257682 : CollatzResearch.WordTrace tailWord_3257682 prefixEnd_3257682 1672756685500228537893199 := by
  unfold tailWord_3257682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29704355945995489159001825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79211615855987971090671533 29704355945995489159001825)
  ·
    refine ⟨22278266959496616869251369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29704355945995489159001825 22278266959496616869251369)
    ·
      refine ⟨16708700219622462651938527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22278266959496616869251369 16708700219622462651938527)
      ·
        refine ⟨25063050329433693977907791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16708700219622462651938527 25063050329433693977907791)
        ·
          refine ⟨37594575494150540966861687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25063050329433693977907791 37594575494150540966861687)
          ·
            refine ⟨56391863241225811450292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37594575494150540966861687 56391863241225811450292531)
            ·
              refine ⟨84587794861838717175438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56391863241225811450292531 84587794861838717175438797)
              ·
                refine ⟨31720423073189518940789549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84587794861838717175438797 31720423073189518940789549)
                ·
                  refine ⟨11895158652446069602796081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31720423073189518940789549 11895158652446069602796081)
                  ·
                    refine ⟨8921368989334552202097061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11895158652446069602796081 8921368989334552202097061)
                    ·
                      refine ⟨1672756685500228537893199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8921368989334552202097061 1672756685500228537893199)
                      ·
                        rfl

theorem cell23_3257682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3257682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257682 prefixEnd_3257682 := by exact prefixLift 3257682
  have htrace : WordTrace (prefixWord ++ tailWord_3257682) baseStart_3257682 baseEnd_3257682 := by
    simpa [prefixWord, tailWord_3257682, baseEnd_3257682] using wordTrace_append hprefix tailTrace_3257682
  have hstable : (prefixWord ++ tailWord_3257682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257682).length < 2 ^ (prefixWord ++ tailWord_3257682).sum := by decide
  have hdescent : baseEnd_3257682 < baseStart_3257682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257689 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_3257689 : Nat := 118140960795 + 3257689 * 2 ^ 59
def prefixEnd_3257689 : Nat := 4983230072969 + 3 ^ 40 * 3257689 * 2
def baseEnd_3257689 : Nat := 1672760279864810010505667

theorem tailTrace_3257689 : CollatzResearch.WordTrace tailWord_3257689 prefixEnd_3257689 1672760279864810010505667 := by
  unfold tailWord_3257689
  simp only [CollatzResearch.WordTrace]
  refine ⟨118817679094956596831512121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79211786063304397887674747 118817679094956596831512121)
  ·
    refine ⟨89113259321217447623634091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118817679094956596831512121 89113259321217447623634091)
    ·
      refine ⟨133669888981826171435451137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89113259321217447623634091 133669888981826171435451137)
      ·
        refine ⟨100252416736369628576588353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133669888981826171435451137 100252416736369628576588353)
        ·
          refine ⟨75189312552277221432441265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100252416736369628576588353 75189312552277221432441265)
          ·
            refine ⟨56391984414207916074330949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75189312552277221432441265 56391984414207916074330949)
            ·
              refine ⟨10573497077663984263937053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56391984414207916074330949 10573497077663984263937053)
              ·
                refine ⟨3965061404123994098976395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10573497077663984263937053 3965061404123994098976395)
                ·
                  refine ⟨5947592106185991148464593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965061404123994098976395 5947592106185991148464593)
                  ·
                    refine ⟨4460694079639493361348445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5947592106185991148464593 4460694079639493361348445)
                    ·
                      refine ⟨1672760279864810010505667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4460694079639493361348445 1672760279864810010505667)
                      ·
                        rfl

theorem cell23_3257689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_3257689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257689 prefixEnd_3257689 := by exact prefixLift 3257689
  have htrace : WordTrace (prefixWord ++ tailWord_3257689) baseStart_3257689 baseEnd_3257689 := by
    simpa [prefixWord, tailWord_3257689, baseEnd_3257689] using wordTrace_append hprefix tailTrace_3257689
  have hstable : (prefixWord ++ tailWord_3257689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257689).length < 2 ^ (prefixWord ++ tailWord_3257689).sum := by decide
  have hdescent : baseEnd_3257689 < baseStart_3257689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257772 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3257772 : Nat := 118140960795 + 3257772 * 2 ^ 59
def prefixEnd_3257772 : Nat := 4983230072969 + 3 ^ 40 * 3257772 * 2
def baseEnd_3257772 : Nat := 1672802898759133185767785

theorem tailTrace_3257772 : CollatzResearch.WordTrace tailWord_3257772 prefixEnd_3257772 1672802898759133185767785 := by
  unfold tailWord_3257772
  simp only [CollatzResearch.WordTrace]
  refine ⟨59410353176827951003391785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79213804235770601337855713 59410353176827951003391785)
  ·
    refine ⟨44557764882620963252543839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59410353176827951003391785 44557764882620963252543839)
    ·
      refine ⟨66836647323931444878815759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44557764882620963252543839 66836647323931444878815759)
      ·
        refine ⟨100254970985897167318223639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66836647323931444878815759 100254970985897167318223639)
        ·
          refine ⟨150382456478845750977335459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100254970985897167318223639 150382456478845750977335459)
          ·
            refine ⟨225573684718268626466003189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150382456478845750977335459 225573684718268626466003189)
            ·
              refine ⟨21147532942337683731187799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225573684718268626466003189 21147532942337683731187799)
              ·
                refine ⟨31721299413506525596781699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21147532942337683731187799 31721299413506525596781699)
                ·
                  refine ⟨47581949120259788395172549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31721299413506525596781699 47581949120259788395172549)
                  ·
                    refine ⟨8921615460048710324094853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47581949120259788395172549 8921615460048710324094853)
                    ·
                      refine ⟨1672802898759133185767785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8921615460048710324094853 1672802898759133185767785)
                      ·
                        rfl

theorem cell23_3257772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3257772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257772 prefixEnd_3257772 := by exact prefixLift 3257772
  have htrace : WordTrace (prefixWord ++ tailWord_3257772) baseStart_3257772 baseEnd_3257772 := by
    simpa [prefixWord, tailWord_3257772, baseEnd_3257772] using wordTrace_append hprefix tailTrace_3257772
  have hstable : (prefixWord ++ tailWord_3257772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257772).length < 2 ^ (prefixWord ++ tailWord_3257772).sum := by decide
  have hdescent : baseEnd_3257772 < baseStart_3257772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257829 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_3257829 : Nat := 118140960795 + 3257829 * 2 ^ 59
def prefixEnd_3257829 : Nat := 4983230072969 + 3 ^ 40 * 3257829 * 2
def baseEnd_3257829 : Nat := 557610722385479820918341

theorem tailTrace_3257829 : CollatzResearch.WordTrace tailWord_3257829 prefixEnd_3257829 557610722385479820918341 := by
  unfold tailWord_3257829
  simp only [CollatzResearch.WordTrace]
  refine ⟨118822785314449400741608541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79215190209632933827739027 118822785314449400741608541)
  ·
    refine ⟨44558544492918525278103203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118822785314449400741608541 44558544492918525278103203)
    ·
      refine ⟨66837816739377787917154805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44558544492918525278103203 66837816739377787917154805)
      ·
        refine ⟨6266045319316667617233263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66837816739377787917154805 6266045319316667617233263)
        ·
          refine ⟨9399067978975001425849895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266045319316667617233263 9399067978975001425849895)
          ·
            refine ⟨14098601968462502138774843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9399067978975001425849895 14098601968462502138774843)
            ·
              refine ⟨21147902952693753208162265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14098601968462502138774843 21147902952693753208162265)
              ·
                refine ⟨15860927214520314906121699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21147902952693753208162265 15860927214520314906121699)
                ·
                  refine ⟨23791390821780472359182549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15860927214520314906121699 23791390821780472359182549)
                  ·
                    refine ⟨557610722385479820918341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23791390821780472359182549 557610722385479820918341)
                    ·
                      rfl

theorem cell23_3257829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_3257829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257829 prefixEnd_3257829 := by exact prefixLift 3257829
  have htrace : WordTrace (prefixWord ++ tailWord_3257829) baseStart_3257829 baseEnd_3257829 := by
    simpa [prefixWord, tailWord_3257829, baseEnd_3257829] using wordTrace_append hprefix tailTrace_3257829
  have hstable : (prefixWord ++ tailWord_3257829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257829).length < 2 ^ (prefixWord ++ tailWord_3257829).sum := by decide
  have hdescent : baseEnd_3257829 < baseStart_3257829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257849 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3257849 : Nat := 118140960795 + 3257849 * 2 ^ 59
def prefixEnd_3257849 : Nat := 4983230072969 + 3 ^ 40 * 3257849 * 2
def baseEnd_3257849 : Nat := 1672842436769529384504931

theorem tailTrace_3257849 : CollatzResearch.WordTrace tailWord_3257849 prefixEnd_3257849 1672842436769529384504931 := by
  unfold tailWord_3257849
  simp only [CollatzResearch.WordTrace]
  refine ⟨118823514774376944157336601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79215676516251296104891067 118823514774376944157336601)
  ·
    refine ⟨89117636080782708118002451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118823514774376944157336601 89117636080782708118002451)
    ·
      refine ⟨133676454121174062177003677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89117636080782708118002451 133676454121174062177003677)
      ·
        refine ⟨50128670295440273316376379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133676454121174062177003677 50128670295440273316376379)
        ·
          refine ⟨75193005443160409974564569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50128670295440273316376379 75193005443160409974564569)
          ·
            refine ⟨56394754082370307480923427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75193005443160409974564569 56394754082370307480923427)
            ·
              refine ⟨84592131123555461221385141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56394754082370307480923427 84592131123555461221385141)
              ·
                refine ⟨7930512292833324489504857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84592131123555461221385141 7930512292833324489504857)
                ·
                  refine ⟨5947884219624993367128643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930512292833324489504857 5947884219624993367128643)
                  ·
                    refine ⟨8921826329437490050692965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947884219624993367128643 8921826329437490050692965)
                    ·
                      refine ⟨1672842436769529384504931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8921826329437490050692965 1672842436769529384504931)
                      ·
                        rfl

theorem cell23_3257849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3257849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257849 prefixEnd_3257849 := by exact prefixLift 3257849
  have htrace : WordTrace (prefixWord ++ tailWord_3257849) baseStart_3257849 baseEnd_3257849 := by
    simpa [prefixWord, tailWord_3257849, baseEnd_3257849] using wordTrace_append hprefix tailTrace_3257849
  have hstable : (prefixWord ++ tailWord_3257849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257849).length < 2 ^ (prefixWord ++ tailWord_3257849).sum := by decide
  have hdescent : baseEnd_3257849 < baseStart_3257849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257866 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3257866 : Nat := 118140960795 + 3257866 * 2 ^ 59
def prefixEnd_3257866 : Nat := 4983230072969 + 3 ^ 40 * 3257866 * 2
def baseEnd_3257866 : Nat := 1672851165940655817992353

theorem tailTrace_3257866 : CollatzResearch.WordTrace tailWord_3257866 prefixEnd_3257866 1672851165940655817992353 := by
  unfold tailWord_3257866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706033703828839015176363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79216089876876904040470301 29706033703828839015176363)
  ·
    refine ⟨44559050555743258522764545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29706033703828839015176363 44559050555743258522764545)
    ·
      refine ⟨33419287916807443892073409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44559050555743258522764545 33419287916807443892073409)
      ·
        refine ⟨25064465937605582919055057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33419287916807443892073409 25064465937605582919055057)
        ·
          refine ⟨18798349453204187189291293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25064465937605582919055057 18798349453204187189291293)
          ·
            refine ⟨7049381044951570195984235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18798349453204187189291293 7049381044951570195984235)
            ·
              refine ⟨10574071567427355293976353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049381044951570195984235 10574071567427355293976353)
              ·
                refine ⟨7930553675570516470482265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10574071567427355293976353 7930553675570516470482265)
                ·
                  refine ⟨5947915256677887352861699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930553675570516470482265 5947915256677887352861699)
                  ·
                    refine ⟨8921872885016831029292549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947915256677887352861699 8921872885016831029292549)
                    ·
                      refine ⟨1672851165940655817992353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8921872885016831029292549 1672851165940655817992353)
                      ·
                        rfl

theorem cell23_3257866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3257866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257866 prefixEnd_3257866 := by exact prefixLift 3257866
  have htrace : WordTrace (prefixWord ++ tailWord_3257866) baseStart_3257866 baseEnd_3257866 := by
    simpa [prefixWord, tailWord_3257866, baseEnd_3257866] using wordTrace_append hprefix tailTrace_3257866
  have hstable : (prefixWord ++ tailWord_3257866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257866).length < 2 ^ (prefixWord ++ tailWord_3257866).sum := by decide
  have hdescent : baseEnd_3257866 < baseStart_3257866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257927 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 1, 4]
def baseStart_3257927 : Nat := 118140960795 + 3257927 * 2 ^ 59
def prefixEnd_3257927 : Nat := 4983230072969 + 3 ^ 40 * 3257927 * 2
def baseEnd_3257927 : Nat := 557627496086860026443191

theorem tailTrace_3257927 : CollatzResearch.WordTrace tailWord_3257927 prefixEnd_3257927 557627496086860026443191 := by
  unfold tailWord_3257927
  simp only [CollatzResearch.WordTrace]
  refine ⟨118826359668094363478676035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79217573112062908985784023 118826359668094363478676035)
  ·
    refine ⟨178239539502141545218014053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118826359668094363478676035 178239539502141545218014053)
    ·
      refine ⟨33419913656651539728377635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178239539502141545218014053 33419913656651539728377635)
      ·
        refine ⟨50129870484977309592566453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33419913656651539728377635 50129870484977309592566453)
        ·
          refine ⟨4699675357966622774303105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50129870484977309592566453 4699675357966622774303105)
          ·
            refine ⟨3524756518474967080727329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4699675357966622774303105 3524756518474967080727329)
            ·
              refine ⟨2643567388856225310545497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524756518474967080727329 2643567388856225310545497)
              ·
                refine ⟨1982675541642168982909123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643567388856225310545497 1982675541642168982909123)
                ·
                  refine ⟨2974013312463253474363685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982675541642168982909123 2974013312463253474363685)
                  ·
                    refine ⟨557627496086860026443191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974013312463253474363685 557627496086860026443191)
                    ·
                      rfl

theorem cell23_3257927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_3257927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257927 prefixEnd_3257927 := by exact prefixLift 3257927
  have htrace : WordTrace (prefixWord ++ tailWord_3257927) baseStart_3257927 baseEnd_3257927 := by
    simpa [prefixWord, tailWord_3257927, baseEnd_3257927] using wordTrace_append hprefix tailTrace_3257927
  have hstable : (prefixWord ++ tailWord_3257927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257927).length < 2 ^ (prefixWord ++ tailWord_3257927).sum := by decide
  have hdescent : baseEnd_3257927 < baseStart_3257927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257956 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_3257956 : Nat := 118140960795 + 3257956 * 2 ^ 59
def prefixEnd_3257956 : Nat := 4983230072969 + 3 ^ 40 * 3257956 * 2
def baseEnd_3257956 : Nat := 1672897379199560465866939

theorem tailTrace_3257956 : CollatzResearch.WordTrace tailWord_3257956 prefixEnd_3257956 1672897379199560465866939 := by
  unfold tailWord_3257956
  simp only [CollatzResearch.WordTrace]
  refine ⟨59413708692494650715740861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79218278256659534287654481 59413708692494650715740861)
  ·
    refine ⟨22280140759685494018402823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59413708692494650715740861 22280140759685494018402823)
    ·
      refine ⟨33420211139528241027604235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22280140759685494018402823 33420211139528241027604235)
      ·
        refine ⟨50130316709292361541406353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33420211139528241027604235 50130316709292361541406353)
        ·
          refine ⟨37597737531969271156054765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50130316709292361541406353 37597737531969271156054765)
          ·
            refine ⟨14099151574488476683520537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37597737531969271156054765 14099151574488476683520537)
            ·
              refine ⟨10574363680866357512640403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14099151574488476683520537 10574363680866357512640403)
              ·
                refine ⟨15861545521299536268960605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574363680866357512640403 15861545521299536268960605)
                ·
                  refine ⟨5948079570487326100860227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15861545521299536268960605 5948079570487326100860227)
                  ·
                    refine ⟨8922119355730989151290341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948079570487326100860227 8922119355730989151290341)
                    ·
                      refine ⟨1672897379199560465866939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8922119355730989151290341 1672897379199560465866939)
                      ·
                        rfl

theorem cell23_3257956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_3257956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257956 prefixEnd_3257956 := by exact prefixLift 3257956
  have htrace : WordTrace (prefixWord ++ tailWord_3257956) baseStart_3257956 baseEnd_3257956 := by
    simpa [prefixWord, tailWord_3257956, baseEnd_3257956] using wordTrace_append hprefix tailTrace_3257956
  have hstable : (prefixWord ++ tailWord_3257956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257956).length < 2 ^ (prefixWord ++ tailWord_3257956).sum := by decide
  have hdescent : baseEnd_3257956 < baseStart_3257956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257960 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3257960 : Nat := 118140960795 + 3257960 * 2 ^ 59
def prefixEnd_3257960 : Nat := 4983230072969 + 3 ^ 40 * 3257960 * 2
def baseEnd_3257960 : Nat := 1672899433122178450216921

theorem tailTrace_3257960 : CollatzResearch.WordTrace tailWord_3257960 prefixEnd_3257960 1672899433122178450216921 := by
  unfold tailWord_3257960
  simp only [CollatzResearch.WordTrace]
  refine ⟨59413781638487405057313667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79218375517983206743084889 59413781638487405057313667)
  ·
    refine ⟨89120672457731107585970501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59413781638487405057313667 89120672457731107585970501)
    ·
      refine ⟨16710126085824582672369469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89120672457731107585970501 16710126085824582672369469)
      ·
        refine ⟨6266297282184218502138551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16710126085824582672369469 6266297282184218502138551)
        ·
          refine ⟨9399445923276327753207827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266297282184218502138551 9399445923276327753207827)
          ·
            refine ⟨14099168884914491629811741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9399445923276327753207827 14099168884914491629811741)
            ·
              refine ⟨5287188331842934361179403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14099168884914491629811741 5287188331842934361179403)
              ·
                refine ⟨7930782497764401541769105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287188331842934361179403 7930782497764401541769105)
                ·
                  refine ⟨5948086873323301156326829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930782497764401541769105 5948086873323301156326829)
                  ·
                    refine ⟨2230532577496237933622561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5948086873323301156326829 2230532577496237933622561)
                    ·
                      refine ⟨1672899433122178450216921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230532577496237933622561 1672899433122178450216921)
                      ·
                        rfl

theorem cell23_3257960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3257960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257960 prefixEnd_3257960 := by exact prefixLift 3257960
  have htrace : WordTrace (prefixWord ++ tailWord_3257960) baseStart_3257960 baseEnd_3257960 := by
    simpa [prefixWord, tailWord_3257960, baseEnd_3257960] using wordTrace_append hprefix tailTrace_3257960
  have hstable : (prefixWord ++ tailWord_3257960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257960).length < 2 ^ (prefixWord ++ tailWord_3257960).sum := by decide
  have hdescent : baseEnd_3257960 < baseStart_3257960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3257970 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3257970 : Nat := 118140960795 + 3257970 * 2 ^ 59
def prefixEnd_3257970 : Nat := 4983230072969 + 3 ^ 40 * 3257970 * 2
def baseEnd_3257970 : Nat := 557634855976241137030625

theorem tailTrace_3257970 : CollatzResearch.WordTrace tailWord_3257970 prefixEnd_3257970 557634855976241137030625 := by
  unfold tailWord_3257970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706982001734645455622841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79218618671292387881660909 29706982001734645455622841)
  ·
    refine ⟨22280236501300984091717131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29706982001734645455622841 22280236501300984091717131)
    ·
      refine ⟨33420354751951476137575697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22280236501300984091717131 33420354751951476137575697)
      ·
        refine ⟨25065266063963607103181773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33420354751951476137575697 25065266063963607103181773)
        ·
          refine ⟨9399474773986352663693165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25065266063963607103181773 9399474773986352663693165)
          ·
            refine ⟨3524803040244882248884937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399474773986352663693165 3524803040244882248884937)
            ·
              refine ⟨2643602280183661686663703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524803040244882248884937 2643602280183661686663703)
              ·
                refine ⟨3965403420275492529995555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643602280183661686663703 3965403420275492529995555)
                ·
                  refine ⟨5948105130413238794993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965403420275492529995555 5948105130413238794993333)
                  ·
                    refine ⟨557634855976241137030625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5948105130413238794993333 557634855976241137030625)
                    ·
                      rfl

theorem cell23_3257970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3257970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3257970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3257970 prefixEnd_3257970 := by exact prefixLift 3257970
  have htrace : WordTrace (prefixWord ++ tailWord_3257970) baseStart_3257970 baseEnd_3257970 := by
    simpa [prefixWord, tailWord_3257970, baseEnd_3257970] using wordTrace_append hprefix tailTrace_3257970
  have hstable : (prefixWord ++ tailWord_3257970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3257970).length < 2 ^ (prefixWord ++ tailWord_3257970).sum := by decide
  have hdescent : baseEnd_3257970 < baseStart_3257970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3257970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258019 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3258019 : Nat := 118140960795 + 3258019 * 2 ^ 59
def prefixEnd_3258019 : Nat := 4983230072969 + 3 ^ 40 * 3258019 * 2
def baseEnd_3258019 : Nat := 1672929728480793719379149

theorem tailTrace_3258019 : CollatzResearch.WordTrace tailWord_3258019 prefixEnd_3258019 1672929728480793719379149 := by
  unfold tailWord_3258019
  simp only [CollatzResearch.WordTrace]
  refine ⟨118829715183761063191025111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79219810122507375460683407 118829715183761063191025111)
  ·
    refine ⟨178244572775641594786537667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118829715183761063191025111 178244572775641594786537667)
    ·
      refine ⟨267366859163462392179806501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178244572775641594786537667 267366859163462392179806501)
      ·
        refine ⟨50131286093149198533713719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267366859163462392179806501 50131286093149198533713719)
        ·
          refine ⟨75196929139723797800570579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50131286093149198533713719 75196929139723797800570579)
          ·
            refine ⟨112795393709585696700855869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75196929139723797800570579 112795393709585696700855869)
            ·
              refine ⟨42298272641094636262820951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112795393709585696700855869 42298272641094636262820951)
              ·
                refine ⟨63447408961641954394231427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42298272641094636262820951 63447408961641954394231427)
                ·
                  refine ⟨95171113442462931591347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63447408961641954394231427 95171113442462931591347141)
                  ·
                    refine ⟨17844583770461799673377589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95171113442462931591347141 17844583770461799673377589)
                    ·
                      refine ⟨1672929728480793719379149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17844583770461799673377589 1672929728480793719379149)
                      ·
                        rfl

theorem cell23_3258019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3258019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258019 prefixEnd_3258019 := by exact prefixLift 3258019
  have htrace : WordTrace (prefixWord ++ tailWord_3258019) baseStart_3258019 baseEnd_3258019 := by
    simpa [prefixWord, tailWord_3258019, baseEnd_3258019] using wordTrace_append hprefix tailTrace_3258019
  have hstable : (prefixWord ++ tailWord_3258019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258019).length < 2 ^ (prefixWord ++ tailWord_3258019).sum := by decide
  have hdescent : baseEnd_3258019 < baseStart_3258019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258030 : List Nat := [4, 1, 4, 1, 3, 1, 9]
def baseStart_3258030 : Nat := 118140960795 + 3258030 * 2 ^ 59
def prefixEnd_3258030 : Nat := 4983230072969 + 3 ^ 40 * 3258030 * 2
def baseEnd_3258030 : Nat := 20653523169975224399279

theorem tailTrace_3258030 : CollatzResearch.WordTrace tailWord_3258030 prefixEnd_3258030 20653523169975224399279 := by
  unfold tailWord_3258030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853764548340151508709443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79220077591147474713117029 14853764548340151508709443)
  ·
    refine ⟨22280646822510227263064165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14853764548340151508709443 22280646822510227263064165)
    ·
      refine ⟨4177621279220667611824531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22280646822510227263064165 4177621279220667611824531)
      ·
        refine ⟨6266431918831001417736797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177621279220667611824531 6266431918831001417736797)
        ·
          refine ⟨2349911969561625531651299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6266431918831001417736797 2349911969561625531651299)
          ·
            refine ⟨3524867954342438297476949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349911969561625531651299 3524867954342438297476949)
            ·
              refine ⟨20653523169975224399279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3524867954342438297476949 20653523169975224399279)
              ·
                rfl

theorem cell23_3258030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 9].length) (baseStart_3258030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258030 prefixEnd_3258030 := by exact prefixLift 3258030
  have htrace : WordTrace (prefixWord ++ tailWord_3258030) baseStart_3258030 baseEnd_3258030 := by
    simpa [prefixWord, tailWord_3258030, baseEnd_3258030] using wordTrace_append hprefix tailTrace_3258030
  have hstable : (prefixWord ++ tailWord_3258030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258030).length < 2 ^ (prefixWord ++ tailWord_3258030).sum := by decide
  have hdescent : baseEnd_3258030 < baseStart_3258030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258059 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_3258059 : Nat := 118140960795 + 3258059 * 2 ^ 59
def prefixEnd_3258059 : Nat := 4983230072969 + 3 ^ 40 * 3258059 * 2
def baseEnd_3258059 : Nat := 1672950267706973562878965

theorem tailTrace_3258059 : CollatzResearch.WordTrace tailWord_3258059 prefixEnd_3258059 1672950267706973562878965 := by
  unfold tailWord_3258059
  simp only [CollatzResearch.WordTrace]
  refine ⟨118831174103616150022481231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79220782735744100014987487 118831174103616150022481231)
  ·
    refine ⟨178246761155424225033721847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118831174103616150022481231 178246761155424225033721847)
    ·
      refine ⟨267370141733136337550582771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178246761155424225033721847 267370141733136337550582771)
      ·
        refine ⟨401055212599704506325874157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267370141733136337550582771 401055212599704506325874157)
        ·
          refine ⟨150395704724889189872202809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401055212599704506325874157 150395704724889189872202809)
          ·
            refine ⟨112796778543666892404152107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150395704724889189872202809 112796778543666892404152107)
            ·
              refine ⟨169195167815500338606228161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112796778543666892404152107 169195167815500338606228161)
              ·
                refine ⟨126896375861625253954671121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169195167815500338606228161 126896375861625253954671121)
                ·
                  refine ⟨95172281896218940466003341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126896375861625253954671121 95172281896218940466003341)
                  ·
                    refine ⟨35689605711082102674751253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95172281896218940466003341 35689605711082102674751253)
                    ·
                      refine ⟨1672950267706973562878965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35689605711082102674751253 1672950267706973562878965)
                      ·
                        rfl

theorem cell23_3258059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_3258059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258059 prefixEnd_3258059 := by exact prefixLift 3258059
  have htrace : WordTrace (prefixWord ++ tailWord_3258059) baseStart_3258059 baseEnd_3258059 := by
    simpa [prefixWord, tailWord_3258059, baseEnd_3258059] using wordTrace_append hprefix tailTrace_3258059
  have hstable : (prefixWord ++ tailWord_3258059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258059).length < 2 ^ (prefixWord ++ tailWord_3258059).sum := by decide
  have hdescent : baseEnd_3258059 < baseStart_3258059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258097 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_3258097 : Nat := 118140960795 + 3258097 * 2 ^ 59
def prefixEnd_3258097 : Nat := 4983230072969 + 3 ^ 40 * 3258097 * 2
def baseEnd_3258097 : Nat := 1672969779971844414203791

theorem tailTrace_3258097 : CollatzResearch.WordTrace tailWord_3258097 prefixEnd_3258097 1672969779971844414203791 := by
  unfold tailWord_3258097
  simp only [CollatzResearch.WordTrace]
  refine ⟨118832560077478482512364545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79221706718318988341576363 118832560077478482512364545)
  ·
    refine ⟨89124420058108861884273409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118832560077478482512364545 89124420058108861884273409)
    ·
      refine ⟨66843315043581646413205057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89124420058108861884273409 66843315043581646413205057)
      ·
        refine ⟨50132486282686234809903793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66843315043581646413205057 50132486282686234809903793)
        ·
          refine ⟨37599364712014676107427845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50132486282686234809903793 37599364712014676107427845)
          ·
            refine ⟨7049880883502751770142721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37599364712014676107427845 7049880883502751770142721)
            ·
              refine ⟨5287410662627063827607041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049880883502751770142721 5287410662627063827607041)
              ·
                refine ⟨3965557996970297870705281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5287410662627063827607041 3965557996970297870705281)
                ·
                  refine ⟨2974168497727723403028961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3965557996970297870705281 2974168497727723403028961)
                  ·
                    refine ⟨2230626373295792552271721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974168497727723403028961 2230626373295792552271721)
                    ·
                      refine ⟨1672969779971844414203791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230626373295792552271721 1672969779971844414203791)
                      ·
                        rfl

theorem cell23_3258097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_3258097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258097 prefixEnd_3258097 := by exact prefixLift 3258097
  have htrace : WordTrace (prefixWord ++ tailWord_3258097) baseStart_3258097 baseEnd_3258097 := by
    simpa [prefixWord, tailWord_3258097, baseEnd_3258097] using wordTrace_append hprefix tailTrace_3258097
  have hstable : (prefixWord ++ tailWord_3258097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258097).length < 2 ^ (prefixWord ++ tailWord_3258097).sum := by decide
  have hdescent : baseEnd_3258097 < baseStart_3258097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258110 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3258110 : Nat := 118140960795 + 3258110 * 2 ^ 59
def prefixEnd_3258110 : Nat := 4983230072969 + 3 ^ 40 * 3258110 * 2
def baseEnd_3258110 : Nat := 1672976455220352863341231

theorem tailTrace_3258110 : CollatzResearch.WordTrace tailWord_3258110 prefixEnd_3258110 1672976455220352863341231 := by
  unfold tailWord_3258110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854129278303923216573473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79222022817620923821725189 14854129278303923216573473)
  ·
    refine ⟨11140596958727942412430105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14854129278303923216573473 11140596958727942412430105)
    ·
      refine ⟨8355447719045956809322579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11140596958727942412430105 8355447719045956809322579)
      ·
        refine ⟨12533171578568935213983869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8355447719045956809322579 12533171578568935213983869)
        ·
          refine ⟨4699939341963350705243951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12533171578568935213983869 4699939341963350705243951)
          ·
            refine ⟨7049909012945026057865927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699939341963350705243951 7049909012945026057865927)
            ·
              refine ⟨10574863519417539086798891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049909012945026057865927 10574863519417539086798891)
              ·
                refine ⟨15862295279126308630198337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574863519417539086798891 15862295279126308630198337)
                ·
                  refine ⟨11896721459344731472648753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15862295279126308630198337 11896721459344731472648753)
                  ·
                    refine ⟨8922541094508548604486565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11896721459344731472648753 8922541094508548604486565)
                    ·
                      refine ⟨1672976455220352863341231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8922541094508548604486565 1672976455220352863341231)
                      ·
                        rfl

theorem cell23_3258110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3258110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258110 prefixEnd_3258110 := by exact prefixLift 3258110
  have htrace : WordTrace (prefixWord ++ tailWord_3258110) baseStart_3258110 baseEnd_3258110 := by
    simpa [prefixWord, tailWord_3258110, baseEnd_3258110] using wordTrace_append hprefix tailTrace_3258110
  have hstable : (prefixWord ++ tailWord_3258110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258110).length < 2 ^ (prefixWord ++ tailWord_3258110).sum := by decide
  have hdescent : baseEnd_3258110 < baseStart_3258110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258126 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3258126 : Nat := 118140960795 + 3258126 * 2 ^ 59
def prefixEnd_3258126 : Nat := 4983230072969 + 3 ^ 40 * 3258126 * 2
def baseEnd_3258126 : Nat := 1672984670910824800741157

theorem tailTrace_3258126 : CollatzResearch.WordTrace tailWord_3258126 prefixEnd_3258126 1672984670910824800741157 := by
  unfold tailWord_3258126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854202224296677558146279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79222411862915613643446821 14854202224296677558146279)
  ·
    refine ⟨22281303336445016337219419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14854202224296677558146279 22281303336445016337219419)
    ·
      refine ⟨33421955004667524505829129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22281303336445016337219419 33421955004667524505829129)
      ·
        refine ⟨25066466253500643379371847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33421955004667524505829129 25066466253500643379371847)
        ·
          refine ⟨37599699380250965069057771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25066466253500643379371847 37599699380250965069057771)
          ·
            refine ⟨56399549070376447603586657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37599699380250965069057771 56399549070376447603586657)
            ·
              refine ⟨42299661802782335702689993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56399549070376447603586657 42299661802782335702689993)
              ·
                refine ⟨31724746352086751777017495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42299661802782335702689993 31724746352086751777017495)
                ·
                  refine ⟨47587119528130127665526243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31724746352086751777017495 47587119528130127665526243)
                  ·
                    refine ⟨71380679292195191498289365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47587119528130127665526243 71380679292195191498289365)
                    ·
                      refine ⟨1672984670910824800741157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71380679292195191498289365 1672984670910824800741157)
                      ·
                        rfl

theorem cell23_3258126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3258126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258126 prefixEnd_3258126 := by exact prefixLift 3258126
  have htrace : WordTrace (prefixWord ++ tailWord_3258126) baseStart_3258126 baseEnd_3258126 := by
    simpa [prefixWord, tailWord_3258126, baseEnd_3258126] using wordTrace_append hprefix tailTrace_3258126
  have hstable : (prefixWord ++ tailWord_3258126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258126).length < 2 ^ (prefixWord ++ tailWord_3258126).sum := by decide
  have hdescent : baseEnd_3258126 < baseStart_3258126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258133 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3258133 : Nat := 118140960795 + 3258133 * 2 ^ 59
def prefixEnd_3258133 : Nat := 4983230072969 + 3 ^ 40 * 3258133 * 2
def baseEnd_3258133 : Nat := 557662755091802091117875

theorem tailTrace_3258133 : CollatzResearch.WordTrace tailWord_3258133 prefixEnd_3258133 557662755091802091117875 := by
  unfold tailWord_3258133
  simp only [CollatzResearch.WordTrace]
  refine ⟨118833873105348060660675053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79222582070232040440450035 118833873105348060660675053)
  ·
    refine ⟨44562702414505522747753145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118833873105348060660675053 44562702414505522747753145)
    ·
      refine ⟨33422026810879142060814859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44562702414505522747753145 33422026810879142060814859)
      ·
        refine ⟨50133040216318713091222289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33422026810879142060814859 50133040216318713091222289)
        ·
          refine ⟨37599780162239034818416717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50133040216318713091222289 37599780162239034818416717)
          ·
            refine ⟨14099917560839638056906269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37599780162239034818416717 14099917560839638056906269)
            ·
              refine ⟨5287469085314864271339851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14099917560839638056906269 5287469085314864271339851)
              ·
                refine ⟨7931203627972296407009777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287469085314864271339851 7931203627972296407009777)
                ·
                  refine ⟨5948402720979222305257333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7931203627972296407009777 5948402720979222305257333)
                  ·
                    refine ⟨557662755091802091117875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5948402720979222305257333 557662755091802091117875)
                    ·
                      rfl

theorem cell23_3258133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3258133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258133 prefixEnd_3258133 := by exact prefixLift 3258133
  have htrace : WordTrace (prefixWord ++ tailWord_3258133) baseStart_3258133 baseEnd_3258133 := by
    simpa [prefixWord, tailWord_3258133, baseEnd_3258133] using wordTrace_append hprefix tailTrace_3258133
  have hstable : (prefixWord ++ tailWord_3258133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258133).length < 2 ^ (prefixWord ++ tailWord_3258133).sum := by decide
  have hdescent : baseEnd_3258133 < baseStart_3258133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258170 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_3258170 : Nat := 118140960795 + 3258170 * 2 ^ 59
def prefixEnd_3258170 : Nat := 4983230072969 + 3 ^ 40 * 3258170 * 2
def baseEnd_3258170 : Nat := 1673007264059622628590955

theorem tailTrace_3258170 : CollatzResearch.WordTrace tailWord_3258170 prefixEnd_3258170 1673007264059622628590955 := by
  unfold tailWord_3258170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708805651553503994942991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79223481737476010653181309 29708805651553503994942991)
  ·
    refine ⟨44563208477330255992414487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29708805651553503994942991 44563208477330255992414487)
    ·
      refine ⟨66844812715995383988621731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44563208477330255992414487 66844812715995383988621731)
      ·
        refine ⟨100267219073993075982932597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66844812715995383988621731 100267219073993075982932597)
        ·
          refine ⟨9400051788186850873399931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100267219073993075982932597 9400051788186850873399931)
          ·
            refine ⟨14100077682280276310099897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400051788186850873399931 14100077682280276310099897)
            ·
              refine ⟨10575058261710207232574923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14100077682280276310099897 10575058261710207232574923)
              ·
                refine ⟨15862587392565310848862385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10575058261710207232574923 15862587392565310848862385)
                ·
                  refine ⟨11896940544423983136646789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15862587392565310848862385 11896940544423983136646789)
                  ·
                    refine ⟨2230676352079496838121273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11896940544423983136646789 2230676352079496838121273)
                    ·
                      refine ⟨1673007264059622628590955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230676352079496838121273 1673007264059622628590955)
                      ·
                        rfl

theorem cell23_3258170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_3258170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258170 prefixEnd_3258170 := by exact prefixLift 3258170
  have htrace : WordTrace (prefixWord ++ tailWord_3258170) baseStart_3258170 baseEnd_3258170 := by
    simpa [prefixWord, tailWord_3258170, baseEnd_3258170] using wordTrace_append hprefix tailTrace_3258170
  have hstable : (prefixWord ++ tailWord_3258170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258170).length < 2 ^ (prefixWord ++ tailWord_3258170).sum := by decide
  have hdescent : baseEnd_3258170 < baseStart_3258170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258197 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_3258197 : Nat := 118140960795 + 3258197 * 2 ^ 59
def prefixEnd_3258197 : Nat := 4983230072969 + 3 ^ 40 * 3258197 * 2
def baseEnd_3258197 : Nat := 557673709345764674317777

theorem tailTrace_3258197 : CollatzResearch.WordTrace tailWord_3258197 prefixEnd_3258197 557673709345764674317777 := by
  unfold tailWord_3258197
  simp only [CollatzResearch.WordTrace]
  refine ⟨118836207377116199591004845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79224138251410799727336563 118836207377116199591004845)
  ·
    refine ⟨44563577766418574846626817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118836207377116199591004845 44563577766418574846626817)
    ·
      refine ⟨33422683324813931134970113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44563577766418574846626817 33422683324813931134970113)
      ·
        refine ⟨25067012493610448351227585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33422683324813931134970113 25067012493610448351227585)
        ·
          refine ⟨18800259370207836263420689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25067012493610448351227585 18800259370207836263420689)
          ·
            refine ⟨14100194527655877197565517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18800259370207836263420689 14100194527655877197565517)
            ·
              refine ⟨5287572947870953949087069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14100194527655877197565517 5287572947870953949087069)
              ·
                refine ⟨1982839855451607730907651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287572947870953949087069 1982839855451607730907651)
                ·
                  refine ⟨2974259783177411596361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982839855451607730907651 2974259783177411596361477)
                  ·
                    refine ⟨557673709345764674317777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974259783177411596361477 557673709345764674317777)
                    ·
                      rfl

theorem cell23_3258197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_3258197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258197 prefixEnd_3258197 := by exact prefixLift 3258197
  have htrace : WordTrace (prefixWord ++ tailWord_3258197) baseStart_3258197 baseEnd_3258197 := by
    simpa [prefixWord, tailWord_3258197, baseEnd_3258197] using wordTrace_append hprefix tailTrace_3258197
  have hstable : (prefixWord ++ tailWord_3258197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258197).length < 2 ^ (prefixWord ++ tailWord_3258197).sum := by decide
  have hdescent : baseEnd_3258197 < baseStart_3258197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258363 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_3258363 : Nat := 118140960795 + 3258363 * 2 ^ 59
def prefixEnd_3258363 : Nat := 4983230072969 + 3 ^ 40 * 3258363 * 2
def baseEnd_3258363 : Nat := 1673106365825940373477567

theorem tailTrace_3258363 : CollatzResearch.WordTrace tailWord_3258363 prefixEnd_3258363 1673106365825940373477567 := by
  unfold tailWord_3258363
  simp only [CollatzResearch.WordTrace]
  refine ⟨118842261894514809941547743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79228174596343206627698495 118842261894514809941547743)
  ·
    refine ⟨178263392841772214912321615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118842261894514809941547743 178263392841772214912321615)
    ·
      refine ⟨267395089262658322368482423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178263392841772214912321615 267395089262658322368482423)
      ·
        refine ⟨401092633893987483552723635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267395089262658322368482423 401092633893987483552723635)
        ·
          refine ⟨601638950840981225329085453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401092633893987483552723635 601638950840981225329085453)
          ·
            refine ⟨225614606565367959498407045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601638950840981225329085453 225614606565367959498407045)
            ·
              refine ⟨42302738731006492405951321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225614606565367959498407045 42302738731006492405951321)
              ·
                refine ⟨31727054048254869304463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42302738731006492405951321 31727054048254869304463491)
                ·
                  refine ⟨47590581072382303956695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31727054048254869304463491 47590581072382303956695237)
                  ·
                    refine ⟨8923233951071681991880357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47590581072382303956695237 8923233951071681991880357)
                    ·
                      refine ⟨1673106365825940373477567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8923233951071681991880357 1673106365825940373477567)
                      ·
                        rfl

theorem cell23_3258363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_3258363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258363 prefixEnd_3258363 := by exact prefixLift 3258363
  have htrace : WordTrace (prefixWord ++ tailWord_3258363) baseStart_3258363 baseEnd_3258363 := by
    simpa [prefixWord, tailWord_3258363, baseEnd_3258363] using wordTrace_append hprefix tailTrace_3258363
  have hstable : (prefixWord ++ tailWord_3258363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258363).length < 2 ^ (prefixWord ++ tailWord_3258363).sum := by decide
  have hdescent : baseEnd_3258363 < baseStart_3258363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258401 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3258401 : Nat := 118140960795 + 3258401 * 2 ^ 59
def prefixEnd_3258401 : Nat := 4983230072969 + 3 ^ 40 * 3258401 * 2
def baseEnd_3258401 : Nat := 1673125878090811224802393

theorem tailTrace_3258401 : CollatzResearch.WordTrace tailWord_3258401 prefixEnd_3258401 1673125878090811224802393 := by
  unfold tailWord_3258401
  simp only [CollatzResearch.WordTrace]
  refine ⟨118843647868377142431431057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79229098578918094954287371 118843647868377142431431057)
  ·
    refine ⟨89132735901282856823573293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118843647868377142431431057 89132735901282856823573293)
    ·
      refine ⟨33424775962981071308839985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89132735901282856823573293 33424775962981071308839985)
      ·
        refine ⟨25068581972235803481629989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33424775962981071308839985 25068581972235803481629989)
        ·
          refine ⟨4700359119794213152805623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25068581972235803481629989 4700359119794213152805623)
          ·
            refine ⟨7050538679691319729208435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700359119794213152805623 7050538679691319729208435)
            ·
              refine ⟨10575808019536979593812653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050538679691319729208435 10575808019536979593812653)
              ·
                refine ⟨3965928007326367347679745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10575808019536979593812653 3965928007326367347679745)
                ·
                  refine ⟨2974446005494775510759809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3965928007326367347679745 2974446005494775510759809)
                  ·
                    refine ⟨2230834504121081633069857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974446005494775510759809 2230834504121081633069857)
                    ·
                      refine ⟨1673125878090811224802393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230834504121081633069857 1673125878090811224802393)
                      ·
                        rfl

theorem cell23_3258401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3258401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258401 prefixEnd_3258401 := by exact prefixLift 3258401
  have htrace : WordTrace (prefixWord ++ tailWord_3258401) baseStart_3258401 baseEnd_3258401 := by
    simpa [prefixWord, tailWord_3258401, baseEnd_3258401] using wordTrace_append hprefix tailTrace_3258401
  have hstable : (prefixWord ++ tailWord_3258401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258401).length < 2 ^ (prefixWord ++ tailWord_3258401).sum := by decide
  have hdescent : baseEnd_3258401 < baseStart_3258401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258440 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3258440 : Nat := 118140960795 + 3258440 * 2 ^ 59
def prefixEnd_3258440 : Nat := 4983230072969 + 3 ^ 40 * 3258440 * 2
def baseEnd_3258440 : Nat := 1673145903836336572214713

theorem tailTrace_3258440 : CollatzResearch.WordTrace tailWord_3258440 prefixEnd_3258440 1673145903836336572214713 := by
  unfold tailWord_3258440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59422535157617926046050387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79230046876823901394733849 59422535157617926046050387)
  ·
    refine ⟨89133802736426889069075581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59422535157617926046050387 89133802736426889069075581)
    ·
      refine ⟨33425176026160083400903343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89133802736426889069075581 33425176026160083400903343)
      ·
        refine ⟨50137764039240125101355015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33425176026160083400903343 50137764039240125101355015)
        ·
          refine ⟨75206646058860187652032523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50137764039240125101355015 75206646058860187652032523)
          ·
            refine ⟨112809969088290281478048785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75206646058860187652032523 112809969088290281478048785)
            ·
              refine ⟨84607476816217711108536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112809969088290281478048785 84607476816217711108536589)
              ·
                refine ⟨31727803806081641665701221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84607476816217711108536589 31727803806081641665701221)
                ·
                  refine ⟨5948963213640307812318979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31727803806081641665701221 5948963213640307812318979)
                  ·
                    refine ⟨8923444820460461718478469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948963213640307812318979 8923444820460461718478469)
                    ·
                      refine ⟨1673145903836336572214713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8923444820460461718478469 1673145903836336572214713)
                      ·
                        rfl

theorem cell23_3258440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3258440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258440 prefixEnd_3258440 := by exact prefixLift 3258440
  have htrace : WordTrace (prefixWord ++ tailWord_3258440) baseStart_3258440 baseEnd_3258440 := by
    simpa [prefixWord, tailWord_3258440, baseEnd_3258440] using wordTrace_append hprefix tailTrace_3258440
  have hstable : (prefixWord ++ tailWord_3258440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258440).length < 2 ^ (prefixWord ++ tailWord_3258440).sum := by decide
  have hdescent : baseEnd_3258440 < baseStart_3258440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258457 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 4, 2]
def baseStart_3258457 : Nat := 118140960795 + 3258457 * 2 ^ 59
def prefixEnd_3258457 : Nat := 4983230072969 + 3 ^ 40 * 3258457 * 2
def baseEnd_3258457 : Nat := 1673154633007463005702135

theorem tailTrace_3258457 : CollatzResearch.WordTrace tailWord_3258457 prefixEnd_3258457 1673154633007463005702135 := by
  unfold tailWord_3258457
  simp only [CollatzResearch.WordTrace]
  refine ⟨118845690356174263995469625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79230460237449509330313083 118845690356174263995469625)
  ·
    refine ⟨89134267767130697996602219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118845690356174263995469625 89134267767130697996602219)
    ·
      refine ⟨133701401650696046994903329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89134267767130697996602219 133701401650696046994903329)
      ·
        refine ⟨100276051238022035246177497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133701401650696046994903329 100276051238022035246177497)
        ·
          refine ⟨75207038428516526434633123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100276051238022035246177497 75207038428516526434633123)
          ·
            refine ⟨112810557642774789651949685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75207038428516526434633123 112810557642774789651949685)
            ·
              refine ⟨10575989779010136529870283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112810557642774789651949685 10575989779010136529870283)
              ·
                refine ⟨15863984668515204794805425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10575989779010136529870283 15863984668515204794805425)
                ·
                  refine ⟨11897988501386403596104069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15863984668515204794805425 11897988501386403596104069)
                  ·
                    refine ⟨2230872844009950674269513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11897988501386403596104069 2230872844009950674269513)
                    ·
                      refine ⟨1673154633007463005702135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230872844009950674269513 1673154633007463005702135)
                      ·
                        rfl

theorem cell23_3258457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_3258457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258457 prefixEnd_3258457 := by exact prefixLift 3258457
  have htrace : WordTrace (prefixWord ++ tailWord_3258457) baseStart_3258457 baseEnd_3258457 := by
    simpa [prefixWord, tailWord_3258457, baseEnd_3258457] using wordTrace_append hprefix tailTrace_3258457
  have hstable : (prefixWord ++ tailWord_3258457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258457).length < 2 ^ (prefixWord ++ tailWord_3258457).sum := by decide
  have hdescent : baseEnd_3258457 < baseStart_3258457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258477 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3258477 : Nat := 118140960795 + 3258477 * 2 ^ 59
def prefixEnd_3258477 : Nat := 4983230072969 + 3 ^ 40 * 3258477 * 2
def baseEnd_3258477 : Nat := 1673164902620552927452043

theorem tailTrace_3258477 : CollatzResearch.WordTrace tailWord_3258477 prefixEnd_3258477 1673164902620552927452043 := by
  unfold tailWord_3258477
  simp only [CollatzResearch.WordTrace]
  refine ⟨118846419816101807411197685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79230946544067871607465123 118846419816101807411197685)
  ·
    refine ⟨11141851857759544444799783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118846419816101807411197685 11141851857759544444799783)
    ·
      refine ⟨16712777786639316667199675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141851857759544444799783 16712777786639316667199675)
      ·
        refine ⟨25069166679958975000799513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16712777786639316667199675 25069166679958975000799513)
        ·
          refine ⟨18801875009969231250599635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25069166679958975000799513 18801875009969231250599635)
          ·
            refine ⟨28202812514953846875899453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18801875009969231250599635 28202812514953846875899453)
            ·
              refine ⟨10576054693107692578462295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28202812514953846875899453 10576054693107692578462295)
              ·
                refine ⟨15864082039661538867693443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576054693107692578462295 15864082039661538867693443)
                ·
                  refine ⟨23796123059492308301540165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15864082039661538867693443 23796123059492308301540165)
                  ·
                    refine ⟨4461773073654807806538781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23796123059492308301540165 4461773073654807806538781)
                    ·
                      refine ⟨1673164902620552927452043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4461773073654807806538781 1673164902620552927452043)
                      ·
                        rfl

theorem cell23_3258477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3258477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258477 prefixEnd_3258477 := by exact prefixLift 3258477
  have htrace : WordTrace (prefixWord ++ tailWord_3258477) baseStart_3258477 baseEnd_3258477 := by
    simpa [prefixWord, tailWord_3258477, baseEnd_3258477] using wordTrace_append hprefix tailTrace_3258477
  have hstable : (prefixWord ++ tailWord_3258477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258477).length < 2 ^ (prefixWord ++ tailWord_3258477).sum := by decide
  have hdescent : baseEnd_3258477 < baseStart_3258477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258490 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_3258490 : Nat := 118140960795 + 3258490 * 2 ^ 59
def prefixEnd_3258490 : Nat := 4983230072969 + 3 ^ 40 * 3258490 * 2
def baseEnd_3258490 : Nat := 1673171577869061376589483

theorem tailTrace_3258490 : CollatzResearch.WordTrace tailWord_3258490 prefixEnd_3258490 1673171577869061376589483 := by
  unfold tailWord_3258490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711723491263677657855231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79231262643369807087613949 29711723491263677657855231)
  ·
    refine ⟨44567585236895516486782847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29711723491263677657855231 44567585236895516486782847)
    ·
      refine ⟨66851377855343274730174271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44567585236895516486782847 66851377855343274730174271)
      ·
        refine ⟨100277066783014912095261407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66851377855343274730174271 100277066783014912095261407)
        ·
          refine ⟨150415600174522368142892111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100277066783014912095261407 150415600174522368142892111)
          ·
            refine ⟨225623400261783552214338167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150415600174522368142892111 225623400261783552214338167)
            ·
              refine ⟨338435100392675328321507251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225623400261783552214338167 338435100392675328321507251)
              ·
                refine ⟨507652650589012992482260877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338435100392675328321507251 507652650589012992482260877)
                ·
                  refine ⟨190369743970879872180847829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507652650589012992482260877 190369743970879872180847829)
                  ·
                    refine ⟨4461790874317497004238621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190369743970879872180847829 4461790874317497004238621)
                    ·
                      refine ⟨1673171577869061376589483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4461790874317497004238621 1673171577869061376589483)
                      ·
                        rfl

theorem cell23_3258490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_3258490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258490 prefixEnd_3258490 := by exact prefixLift 3258490
  have htrace : WordTrace (prefixWord ++ tailWord_3258490) baseStart_3258490 baseEnd_3258490 := by
    simpa [prefixWord, tailWord_3258490, baseEnd_3258490] using wordTrace_append hprefix tailTrace_3258490
  have hstable : (prefixWord ++ tailWord_3258490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258490).length < 2 ^ (prefixWord ++ tailWord_3258490).sum := by decide
  have hdescent : baseEnd_3258490 < baseStart_3258490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258497 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 8]
def baseStart_3258497 : Nat := 118140960795 + 3258497 * 2 ^ 59
def prefixEnd_3258497 : Nat := 4983230072969 + 3 ^ 40 * 3258497 * 2
def baseEnd_3258497 : Nat := 185908352470404761022439

theorem tailTrace_3258497 : CollatzResearch.WordTrace tailWord_3258497 prefixEnd_3258497 185908352470404761022439 := by
  unfold tailWord_3258497
  simp only [CollatzResearch.WordTrace]
  refine ⟨118847149276029350826925745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79231432850686233884617163 118847149276029350826925745)
  ·
    refine ⟨89135361957022013120194309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118847149276029350826925745 89135361957022013120194309)
    ·
      refine ⟨16712880366941627460036433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89135361957022013120194309 16712880366941627460036433)
      ·
        refine ⟨12534660275206220595027325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16712880366941627460036433 12534660275206220595027325)
        ·
          refine ⟨4700497603202332723135247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12534660275206220595027325 4700497603202332723135247)
          ·
            refine ⟨7050746404803499084702871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700497603202332723135247 7050746404803499084702871)
            ·
              refine ⟨10576119607205248627054307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050746404803499084702871 10576119607205248627054307)
              ·
                refine ⟨15864179410807872940581461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576119607205248627054307 15864179410807872940581461)
                ·
                  refine ⟨185908352470404761022439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15864179410807872940581461 185908352470404761022439)
                  ·
                    rfl

theorem cell23_3258497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_3258497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258497 prefixEnd_3258497 := by exact prefixLift 3258497
  have htrace : WordTrace (prefixWord ++ tailWord_3258497) baseStart_3258497 baseEnd_3258497 := by
    simpa [prefixWord, tailWord_3258497, baseEnd_3258497] using wordTrace_append hprefix tailTrace_3258497
  have hstable : (prefixWord ++ tailWord_3258497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258497).length < 2 ^ (prefixWord ++ tailWord_3258497).sum := by decide
  have hdescent : baseEnd_3258497 < baseStart_3258497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258500 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3258500 : Nat := 118140960795 + 3258500 * 2 ^ 59
def prefixEnd_3258500 : Nat := 4983230072969 + 3 ^ 40 * 3258500 * 2
def baseEnd_3258500 : Nat := 1673176712675606337464437

theorem tailTrace_3258500 : CollatzResearch.WordTrace tailWord_3258500 prefixEnd_3258500 1673176712675606337464437 := by
  unfold tailWord_3258500
  simp only [CollatzResearch.WordTrace]
  refine ⟨59423629347509241169642477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79231505796678988226189969 59423629347509241169642477)
  ·
    refine ⟨22283861005315965438615929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59423629347509241169642477 22283861005315965438615929)
    ·
      refine ⟨16712895753986974078961947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22283861005315965438615929 16712895753986974078961947)
      ·
        refine ⟨25069343630980461118442921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16712895753986974078961947 25069343630980461118442921)
        ·
          refine ⟨18802007723235345838832191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25069343630980461118442921 18802007723235345838832191)
          ·
            refine ⟨28203011584853018758248287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18802007723235345838832191 28203011584853018758248287)
            ·
              refine ⟨42304517377279528137372431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28203011584853018758248287 42304517377279528137372431)
              ·
                refine ⟨63456776065919292206058647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42304517377279528137372431 63456776065919292206058647)
                ·
                  refine ⟨95185164098878938309087971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63456776065919292206058647 95185164098878938309087971)
                  ·
                    refine ⟨142777746148318407463631957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95185164098878938309087971 142777746148318407463631957)
                    ·
                      refine ⟨1673176712675606337464437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142777746148318407463631957 1673176712675606337464437)
                      ·
                        rfl

theorem cell23_3258500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3258500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258500 prefixEnd_3258500 := by exact prefixLift 3258500
  have htrace : WordTrace (prefixWord ++ tailWord_3258500) baseStart_3258500 baseEnd_3258500 := by
    simpa [prefixWord, tailWord_3258500, baseEnd_3258500] using wordTrace_append hprefix tailTrace_3258500
  have hstable : (prefixWord ++ tailWord_3258500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258500).length < 2 ^ (prefixWord ++ tailWord_3258500).sum := by decide
  have hdescent : baseEnd_3258500 < baseStart_3258500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258514 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3258514 : Nat := 118140960795 + 3258514 * 2 ^ 59
def prefixEnd_3258514 : Nat := 4983230072969 + 3 ^ 40 * 3258514 * 2
def baseEnd_3258514 : Nat := 185909322378307698076597

theorem tailTrace_3258514 : CollatzResearch.WordTrace tailWord_3258514 prefixEnd_3258514 185909322378307698076597 := by
  unfold tailWord_3258514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711942329241940682573649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79231846211311841820196397 29711942329241940682573649)
  ·
    refine ⟨22283956746931455511930237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29711942329241940682573649 22283956746931455511930237)
    ·
      refine ⟨8356483780099295816973839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22283956746931455511930237 8356483780099295816973839)
      ·
        refine ⟨12534725670148943725460759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356483780099295816973839 12534725670148943725460759)
        ·
          refine ⟨18802088505223415588191139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534725670148943725460759 18802088505223415588191139)
          ·
            refine ⟨28203132757835123382286709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18802088505223415588191139 28203132757835123382286709)
            ·
              refine ⟨2644043696047042817089379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28203132757835123382286709 2644043696047042817089379)
              ·
                refine ⟨3966065544070564225634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644043696047042817089379 3966065544070564225634069)
                ·
                  refine ⟨185909322378307698076597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3966065544070564225634069 185909322378307698076597)
                  ·
                    rfl

theorem cell23_3258514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3258514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258514 prefixEnd_3258514 := by exact prefixLift 3258514
  have htrace : WordTrace (prefixWord ++ tailWord_3258514) baseStart_3258514 baseEnd_3258514 := by
    simpa [prefixWord, tailWord_3258514, baseEnd_3258514] using wordTrace_append hprefix tailTrace_3258514
  have hstable : (prefixWord ++ tailWord_3258514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258514).length < 2 ^ (prefixWord ++ tailWord_3258514).sum := by decide
  have hdescent : baseEnd_3258514 < baseStart_3258514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258517 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_3258517 : Nat := 118140960795 + 3258517 * 2 ^ 59
def prefixEnd_3258517 : Nat := 4983230072969 + 3 ^ 40 * 3258517 * 2
def baseEnd_3258517 : Nat := 1673185441846732770951859

theorem tailTrace_3258517 : CollatzResearch.WordTrace tailWord_3258517 prefixEnd_3258517 1673185441846732770951859 := by
  unfold tailWord_3258517
  simp only [CollatzResearch.WordTrace]
  refine ⟨118847878735956894242653805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79231919157304596161769203 118847878735956894242653805)
  ·
    refine ⟨44567954525983835340995177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118847878735956894242653805 44567954525983835340995177)
    ·
      refine ⟨33425965894487876505746383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44567954525983835340995177 33425965894487876505746383)
      ·
        refine ⟨50138948841731814758619575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33425965894487876505746383 50138948841731814758619575)
        ·
          refine ⟨75208423262597722137929363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50138948841731814758619575 75208423262597722137929363)
          ·
            refine ⟨112812634893896583206894045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75208423262597722137929363 112812634893896583206894045)
            ·
              refine ⟨42304738085211218702585267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112812634893896583206894045 42304738085211218702585267)
              ·
                refine ⟨63457107127816828053877901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42304738085211218702585267 63457107127816828053877901)
                ·
                  refine ⟨23796415172931310520204213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63457107127816828053877901 23796415172931310520204213)
                  ·
                    refine ⟨2230913922462310361269145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23796415172931310520204213 2230913922462310361269145)
                    ·
                      refine ⟨1673185441846732770951859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230913922462310361269145 1673185441846732770951859)
                      ·
                        rfl

theorem cell23_3258517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_3258517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258517 prefixEnd_3258517 := by exact prefixLift 3258517
  have htrace : WordTrace (prefixWord ++ tailWord_3258517) baseStart_3258517 baseEnd_3258517 := by
    simpa [prefixWord, tailWord_3258517, baseEnd_3258517] using wordTrace_append hprefix tailTrace_3258517
  have hstable : (prefixWord ++ tailWord_3258517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258517).length < 2 ^ (prefixWord ++ tailWord_3258517).sum := by decide
  have hdescent : baseEnd_3258517 < baseStart_3258517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258524 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3258524 : Nat := 118140960795 + 3258524 * 2 ^ 59
def prefixEnd_3258524 : Nat := 4983230072969 + 3 ^ 40 * 3258524 * 2
def baseEnd_3258524 : Nat := 1673189036211314243564327

theorem tailTrace_3258524 : CollatzResearch.WordTrace tailWord_3258524 prefixEnd_3258524 1673189036211314243564327 := by
  unfold tailWord_3258524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59424067023465767219079313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79232089364621022958772417 59424067023465767219079313)
  ·
    refine ⟨44568050267599325414309485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59424067023465767219079313 44568050267599325414309485)
    ·
      refine ⟨16713018850349747030366057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44568050267599325414309485 16713018850349747030366057)
      ·
        refine ⟨12534764137762310272774543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16713018850349747030366057 12534764137762310272774543)
        ·
          refine ⟨18802146206643465409161815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534764137762310272774543 18802146206643465409161815)
          ·
            refine ⟨28203219309965198113742723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18802146206643465409161815 28203219309965198113742723)
            ·
              refine ⟨42304828964947797170614085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28203219309965198113742723 42304828964947797170614085)
              ·
                refine ⟨7932155430927711969490141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42304828964947797170614085 7932155430927711969490141)
                ·
                  refine ⟨2974558286597891988558803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7932155430927711969490141 2974558286597891988558803)
                  ·
                    refine ⟨4461837429896837982838205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974558286597891988558803 4461837429896837982838205)
                    ·
                      refine ⟨1673189036211314243564327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4461837429896837982838205 1673189036211314243564327)
                      ·
                        rfl

theorem cell23_3258524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3258524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258524 prefixEnd_3258524 := by exact prefixLift 3258524
  have htrace : WordTrace (prefixWord ++ tailWord_3258524) baseStart_3258524 baseEnd_3258524 := by
    simpa [prefixWord, tailWord_3258524, baseEnd_3258524] using wordTrace_append hprefix tailTrace_3258524
  have hstable : (prefixWord ++ tailWord_3258524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258524).length < 2 ^ (prefixWord ++ tailWord_3258524).sum := by decide
  have hdescent : baseEnd_3258524 < baseStart_3258524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258535 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3258535 : Nat := 118140960795 + 3258535 * 2 ^ 59
def prefixEnd_3258535 : Nat := 4983230072969 + 3 ^ 40 * 3258535 * 2
def baseEnd_3258535 : Nat := 557731561499504566842259

theorem tailTrace_3258535 : CollatzResearch.WordTrace tailWord_3258535 prefixEnd_3258535 557731561499504566842259 := by
  unfold tailWord_3258535
  simp only [CollatzResearch.WordTrace]
  refine ⟨118848535249891683316809059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79232356833261122211206039 118848535249891683316809059)
  ·
    refine ⟨178272802874837524975213589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118848535249891683316809059 178272802874837524975213589)
    ·
      refine ⟨8356537634758008983213137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178272802874837524975213589 8356537634758008983213137)
      ·
        refine ⟨6267403226068506737409853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8356537634758008983213137 6267403226068506737409853)
        ·
          refine ⟨2350276209775690026528695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6267403226068506737409853 2350276209775690026528695)
          ·
            refine ⟨3525414314663535039793043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350276209775690026528695 3525414314663535039793043)
            ·
              refine ⟨5288121471995302559689565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525414314663535039793043 5288121471995302559689565)
              ·
                refine ⟨1983045551998238459883587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5288121471995302559689565 1983045551998238459883587)
                ·
                  refine ⟨2974568327997357689825381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983045551998238459883587 2974568327997357689825381)
                  ·
                    refine ⟨557731561499504566842259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974568327997357689825381 557731561499504566842259)
                    ·
                      rfl

theorem cell23_3258535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3258535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258535 prefixEnd_3258535 := by exact prefixLift 3258535
  have htrace : WordTrace (prefixWord ++ tailWord_3258535) baseStart_3258535 baseEnd_3258535 := by
    simpa [prefixWord, tailWord_3258535, baseEnd_3258535] using wordTrace_append hprefix tailTrace_3258535
  have hstable : (prefixWord ++ tailWord_3258535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258535).length < 2 ^ (prefixWord ++ tailWord_3258535).sum := by decide
  have hdescent : baseEnd_3258535 < baseStart_3258535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258558 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3258558 : Nat := 118140960795 + 3258558 * 2 ^ 59
def prefixEnd_3258558 : Nat := 4983230072969 + 3 ^ 40 * 3258558 * 2
def baseEnd_3258558 : Nat := 1673206494553567110539171

theorem tailTrace_3258558 : CollatzResearch.WordTrace tailWord_3258558 prefixEnd_3258558 1673206494553567110539171 := by
  unfold tailWord_3258558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856171766101044780612041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79232916085872238829930885 14856171766101044780612041)
  ·
    refine ⟨11142128824575783585459031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14856171766101044780612041 11142128824575783585459031)
    ·
      refine ⟨16713193236863675378188547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142128824575783585459031 16713193236863675378188547)
      ·
        refine ⟨25069789855295513067282821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713193236863675378188547 25069789855295513067282821)
        ·
          refine ⟨4700585597867908700115529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25069789855295513067282821 4700585597867908700115529)
          ·
            refine ⟨3525439198400931525086647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4700585597867908700115529 3525439198400931525086647)
            ·
              refine ⟨5288158797601397287629971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525439198400931525086647 5288158797601397287629971)
              ·
                refine ⟨7932238196402095931444957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288158797601397287629971 7932238196402095931444957)
                ·
                  refine ⟨2974589323650785974291859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7932238196402095931444957 2974589323650785974291859)
                  ·
                    refine ⟨4461883985476178961437789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974589323650785974291859 4461883985476178961437789)
                    ·
                      refine ⟨1673206494553567110539171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4461883985476178961437789 1673206494553567110539171)
                      ·
                        rfl

theorem cell23_3258558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3258558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258558 prefixEnd_3258558 := by exact prefixLift 3258558
  have htrace : WordTrace (prefixWord ++ tailWord_3258558) baseStart_3258558 baseEnd_3258558 := by
    simpa [prefixWord, tailWord_3258558, baseEnd_3258558] using wordTrace_append hprefix tailTrace_3258558
  have hstable : (prefixWord ++ tailWord_3258558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258558).length < 2 ^ (prefixWord ++ tailWord_3258558).sum := by decide
  have hdescent : baseEnd_3258558 < baseStart_3258558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258584 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3258584 : Nat := 118140960795 + 3258584 * 2 ^ 59
def prefixEnd_3258584 : Nat := 4983230072969 + 3 ^ 40 * 3258584 * 2
def baseEnd_3258584 : Nat := 1673219845050584008814051

theorem tailTrace_3258584 : CollatzResearch.WordTrace tailWord_3258584 prefixEnd_3258584 1673219845050584008814051 := by
  unfold tailWord_3258584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59425161213357082342671403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79233548284476109790228537 59425161213357082342671403)
  ·
    refine ⟨89137741820035623514007105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59425161213357082342671403 89137741820035623514007105)
    ·
      refine ⟨66853306365026717635505329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89137741820035623514007105 66853306365026717635505329)
      ·
        refine ⟨50139979773770038226628997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66853306365026717635505329 50139979773770038226628997)
        ·
          refine ⟨9401246207581882167492937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50139979773770038226628997 9401246207581882167492937)
          ·
            refine ⟨7050934655686411625619703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401246207581882167492937 7050934655686411625619703)
            ·
              refine ⟨10576401983529617438429555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050934655686411625619703 10576401983529617438429555)
              ·
                refine ⟨15864602975294426157644333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576401983529617438429555 15864602975294426157644333)
                ·
                  refine ⟨5949226115735409809116625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15864602975294426157644333 5949226115735409809116625)
                  ·
                    refine ⟨4461919586801557356837469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5949226115735409809116625 4461919586801557356837469)
                    ·
                      refine ⟨1673219845050584008814051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4461919586801557356837469 1673219845050584008814051)
                      ·
                        rfl

theorem cell23_3258584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3258584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258584 prefixEnd_3258584 := by exact prefixLift 3258584
  have htrace : WordTrace (prefixWord ++ tailWord_3258584) baseStart_3258584 baseEnd_3258584 := by
    simpa [prefixWord, tailWord_3258584, baseEnd_3258584] using wordTrace_append hprefix tailTrace_3258584
  have hstable : (prefixWord ++ tailWord_3258584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258584).length < 2 ^ (prefixWord ++ tailWord_3258584).sum := by decide
  have hdescent : baseEnd_3258584 < baseStart_3258584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258624 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2]
def baseStart_3258624 : Nat := 118140960795 + 3258624 * 2 ^ 59
def prefixEnd_3258624 : Nat := 4983230072969 + 3 ^ 40 * 3258624 * 2
def baseEnd_3258624 : Nat := 1673240384276763852313867

theorem tailTrace_3258624 : CollatzResearch.WordTrace tailWord_3258624 prefixEnd_3258624 1673240384276763852313867 := by
  unfold tailWord_3258624
  simp only [CollatzResearch.WordTrace]
  refine ⟨59425890673284625758399463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79234520897712834344532617 59425890673284625758399463)
  ·
    refine ⟨89138836009926938637599195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59425890673284625758399463 89138836009926938637599195)
    ·
      refine ⟨133708254014890407956398793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89138836009926938637599195 133708254014890407956398793)
      ·
        refine ⟨100281190511167805967299095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133708254014890407956398793 100281190511167805967299095)
        ·
          refine ⟨150421785766751708950948643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100281190511167805967299095 150421785766751708950948643)
          ·
            refine ⟨225632678650127563426422965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150421785766751708950948643 225632678650127563426422965)
            ·
              refine ⟨21153063623449459071227153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225632678650127563426422965 21153063623449459071227153)
              ·
                refine ⟨15864797717587094303420365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21153063623449459071227153 15864797717587094303420365)
                ·
                  refine ⟨5949299144095160363782637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15864797717587094303420365 5949299144095160363782637)
                  ·
                    refine ⟨2230987179035685136418489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5949299144095160363782637 2230987179035685136418489)
                    ·
                      refine ⟨1673240384276763852313867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2230987179035685136418489 1673240384276763852313867)
                      ·
                        rfl

theorem cell23_3258624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_3258624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258624 prefixEnd_3258624 := by exact prefixLift 3258624
  have htrace : WordTrace (prefixWord ++ tailWord_3258624) baseStart_3258624 baseEnd_3258624 := by
    simpa [prefixWord, tailWord_3258624, baseEnd_3258624] using wordTrace_append hprefix tailTrace_3258624
  have hstable : (prefixWord ++ tailWord_3258624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258624).length < 2 ^ (prefixWord ++ tailWord_3258624).sum := by decide
  have hdescent : baseEnd_3258624 < baseStart_3258624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258657 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3258657 : Nat := 118140960795 + 3258657 * 2 ^ 59
def prefixEnd_3258657 : Nat := 4983230072969 + 3 ^ 40 * 3258657 * 2
def baseEnd_3258657 : Nat := 1673257329138362223201215

theorem tailTrace_3258657 : CollatzResearch.WordTrace tailWord_3258657 prefixEnd_3258657 1673257329138362223201215 := by
  unfold tailWord_3258657
  simp only [CollatzResearch.WordTrace]
  refine ⟨118852984955449698152750225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79235323303633132101833483 118852984955449698152750225)
  ·
    refine ⟨89139738716587273614562669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118852984955449698152750225 89139738716587273614562669)
    ·
      refine ⟨33427402018720227605461001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89139738716587273614562669 33427402018720227605461001)
      ·
        refine ⟨25070551514040170704095751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33427402018720227605461001 25070551514040170704095751)
        ·
          refine ⟨37605827271060256056143627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25070551514040170704095751 37605827271060256056143627)
          ·
            refine ⟨56408740906590384084215441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37605827271060256056143627 56408740906590384084215441)
            ·
              refine ⟨42306555679942788063161581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56408740906590384084215441 42306555679942788063161581)
              ·
                refine ⟨15864958379978545523685593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42306555679942788063161581 15864958379978545523685593)
                ·
                  refine ⟨11898718784983909142764195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15864958379978545523685593 11898718784983909142764195)
                  ·
                    refine ⟨17848078177475863714146293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11898718784983909142764195 17848078177475863714146293)
                    ·
                      refine ⟨1673257329138362223201215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17848078177475863714146293 1673257329138362223201215)
                      ·
                        rfl

theorem cell23_3258657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3258657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258657 prefixEnd_3258657 := by exact prefixLift 3258657
  have htrace : WordTrace (prefixWord ++ tailWord_3258657) baseStart_3258657 baseEnd_3258657 := by
    simpa [prefixWord, tailWord_3258657, baseEnd_3258657] using wordTrace_append hprefix tailTrace_3258657
  have hstable : (prefixWord ++ tailWord_3258657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258657).length < 2 ^ (prefixWord ++ tailWord_3258657).sum := by decide
  have hdescent : baseEnd_3258657 < baseStart_3258657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258658 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3258658 : Nat := 118140960795 + 3258658 * 2 ^ 59
def prefixEnd_3258658 : Nat := 4983230072969 + 3 ^ 40 * 3258658 * 2
def baseEnd_3258658 : Nat := 1673257842619016719288711

theorem tailTrace_3258658 : CollatzResearch.WordTrace tailWord_3258658 prefixEnd_3258658 1673257842619016719288711 := by
  unfold tailWord_3258658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713255357111518830884157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79235347618964050215691085 29713255357111518830884157)
  ·
    refine ⟨11142470758916819561581559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29713255357111518830884157 11142470758916819561581559)
    ·
      refine ⟨16713706138375229342372339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142470758916819561581559 16713706138375229342372339)
      ·
        refine ⟨25070559207562844013558509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713706138375229342372339 25070559207562844013558509)
        ·
          refine ⟨9401459702836066505084441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25070559207562844013558509 9401459702836066505084441)
          ·
            refine ⟨7051094777127049878813331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401459702836066505084441 7051094777127049878813331)
            ·
              refine ⟨10576642165690574818219997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051094777127049878813331 10576642165690574818219997)
              ·
                refine ⟨3966240812133965556832499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576642165690574818219997 3966240812133965556832499)
                ·
                  refine ⟨5949361218200948335248749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966240812133965556832499 5949361218200948335248749)
                  ·
                    refine ⟨2231010456825355625718281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5949361218200948335248749 2231010456825355625718281)
                    ·
                      refine ⟨1673257842619016719288711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231010456825355625718281 1673257842619016719288711)
                      ·
                        rfl

theorem cell23_3258658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3258658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258658 prefixEnd_3258658 := by exact prefixLift 3258658
  have htrace : WordTrace (prefixWord ++ tailWord_3258658) baseStart_3258658 baseEnd_3258658 := by
    simpa [prefixWord, tailWord_3258658, baseEnd_3258658] using wordTrace_append hprefix tailTrace_3258658
  have hstable : (prefixWord ++ tailWord_3258658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258658).length < 2 ^ (prefixWord ++ tailWord_3258658).sum := by decide
  have hdescent : baseEnd_3258658 < baseStart_3258658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258714 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_3258714 : Nat := 118140960795 + 3258714 * 2 ^ 59
def prefixEnd_3258714 : Nat := 4983230072969 + 3 ^ 40 * 3258714 * 2
def baseEnd_3258714 : Nat := 1673286597535668500188453

theorem tailTrace_3258714 : CollatzResearch.WordTrace tailWord_3258714 prefixEnd_3258714 1673286597535668500188453 := by
  unfold tailWord_3258714
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713765979060799221893799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79236709277495464591716797 29713765979060799221893799)
  ·
    refine ⟨44570648968591198832840699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29713765979060799221893799 44570648968591198832840699)
    ·
      refine ⟨66855973452886798249261049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44570648968591198832840699 66855973452886798249261049)
      ·
        refine ⟨50141980089665098686945787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66855973452886798249261049 50141980089665098686945787)
        ·
          refine ⟨75212970134497648030418681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50141980089665098686945787 75212970134497648030418681)
          ·
            refine ⟨56409727600873236022814011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75212970134497648030418681 56409727600873236022814011)
            ·
              refine ⟨84614591401309854034221017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56409727600873236022814011 84614591401309854034221017)
              ·
                refine ⟨63460943550982390525665763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84614591401309854034221017 63460943550982390525665763)
                ·
                  refine ⟨95191415326473585788498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63460943550982390525665763 95191415326473585788498645)
                  ·
                    refine ⟨2231048796714224666917937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95191415326473585788498645 2231048796714224666917937)
                    ·
                      refine ⟨1673286597535668500188453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231048796714224666917937 1673286597535668500188453)
                      ·
                        rfl

theorem cell23_3258714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_3258714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258714 prefixEnd_3258714 := by exact prefixLift 3258714
  have htrace : WordTrace (prefixWord ++ tailWord_3258714) baseStart_3258714 baseEnd_3258714 := by
    simpa [prefixWord, tailWord_3258714, baseEnd_3258714] using wordTrace_append hprefix tailTrace_3258714
  have hstable : (prefixWord ++ tailWord_3258714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258714).length < 2 ^ (prefixWord ++ tailWord_3258714).sum := by decide
  have hdescent : baseEnd_3258714 < baseStart_3258714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258724 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3258724 : Nat := 118140960795 + 3258724 * 2 ^ 59
def prefixEnd_3258724 : Nat := 4983230072969 + 3 ^ 40 * 3258724 * 2
def baseEnd_3258724 : Nat := 557763910780737820354469

theorem tailTrace_3258724 : CollatzResearch.WordTrace tailWord_3258724 prefixEnd_3258724 557763910780737820354469 := by
  unfold tailWord_3258724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59427714323103484297719613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79236952430804645730292817 59427714323103484297719613)
  ·
    refine ⟨22285392871163806611644855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59427714323103484297719613 22285392871163806611644855)
    ·
      refine ⟨33428089306745709917467283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22285392871163806611644855 33428089306745709917467283)
      ·
        refine ⟨50142133960118564876200925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33428089306745709917467283 50142133960118564876200925)
        ·
          refine ⟨18803300235044461828575347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50142133960118564876200925 18803300235044461828575347)
          ·
            refine ⟨28204950352566692742863021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18803300235044461828575347 28204950352566692742863021)
            ·
              refine ⟨10576856382212509778573633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28204950352566692742863021 10576856382212509778573633)
              ·
                refine ⟨7932642286659382333930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10576856382212509778573633 7932642286659382333930225)
                ·
                  refine ⟨5949481714994536750447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932642286659382333930225 5949481714994536750447669)
                  ·
                    refine ⟨557763910780737820354469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5949481714994536750447669 557763910780737820354469)
                    ·
                      rfl

theorem cell23_3258724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3258724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258724 prefixEnd_3258724 := by exact prefixLift 3258724
  have htrace : WordTrace (prefixWord ++ tailWord_3258724) baseStart_3258724 baseEnd_3258724 := by
    simpa [prefixWord, tailWord_3258724, baseEnd_3258724] using wordTrace_append hprefix tailTrace_3258724
  have hstable : (prefixWord ++ tailWord_3258724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258724).length < 2 ^ (prefixWord ++ tailWord_3258724).sum := by decide
  have hdescent : baseEnd_3258724 < baseStart_3258724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258728 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 5]
def baseStart_3258728 : Nat := 118140960795 + 3258728 * 2 ^ 59
def prefixEnd_3258728 : Nat := 4983230072969 + 3 ^ 40 * 3258728 * 2
def baseEnd_3258728 : Nat := 185921531807203493934821

theorem tailTrace_3258728 : CollatzResearch.WordTrace tailWord_3258728 prefixEnd_3258728 185921531807203493934821 := by
  unfold tailWord_3258728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59427787269096238639292419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79237049692128318185723225 59427787269096238639292419)
  ·
    refine ⟨89141680903644357958938629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59427787269096238639292419 89141680903644357958938629)
    ·
      refine ⟨16714065169433317117300993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89141680903644357958938629 16714065169433317117300993)
      ·
        refine ⟨12535548877074987837975745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16714065169433317117300993 12535548877074987837975745)
        ·
          refine ⟨9401661657806240878481809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12535548877074987837975745 9401661657806240878481809)
          ·
            refine ⟨7051246243354680658861357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401661657806240878481809 7051246243354680658861357)
            ·
              refine ⟨2644217341258005247073009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051246243354680658861357 2644217341258005247073009)
              ·
                refine ⟨1983163005943503935304757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644217341258005247073009 1983163005943503935304757)
                ·
                  refine ⟨185921531807203493934821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983163005943503935304757 185921531807203493934821)
                  ·
                    rfl

theorem cell23_3258728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 5].length) (baseStart_3258728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258728 prefixEnd_3258728 := by exact prefixLift 3258728
  have htrace : WordTrace (prefixWord ++ tailWord_3258728) baseStart_3258728 baseEnd_3258728 := by
    simpa [prefixWord, tailWord_3258728, baseEnd_3258728] using wordTrace_append hprefix tailTrace_3258728
  have hstable : (prefixWord ++ tailWord_3258728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258728).length < 2 ^ (prefixWord ++ tailWord_3258728).sum := by decide
  have hdescent : baseEnd_3258728 < baseStart_3258728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258757 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_3258757 : Nat := 118140960795 + 3258757 * 2 ^ 59
def prefixEnd_3258757 : Nat := 4983230072969 + 3 ^ 40 * 3258757 * 2
def baseEnd_3258757 : Nat := 1673308677203811831950755

theorem tailTrace_3258757 : CollatzResearch.WordTrace tailWord_3258757 prefixEnd_3258757 1673308677203811831950755 := by
  unfold tailWord_3258757
  simp only [CollatzResearch.WordTrace]
  refine ⟨118856632255087415231390525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79237754836724943487593683 118856632255087415231390525)
  ·
    refine ⟨44571237095657780711771447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118856632255087415231390525 44571237095657780711771447)
    ·
      refine ⟨66856855643486671067657171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44571237095657780711771447 66856855643486671067657171)
      ·
        refine ⟨100285283465230006601485757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66856855643486671067657171 100285283465230006601485757)
        ·
          refine ⟨37606981299461252475557159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100285283465230006601485757 37606981299461252475557159)
          ·
            refine ⟨56410471949191878713335739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37606981299461252475557159 56410471949191878713335739)
            ·
              refine ⟨84615707923787818070003609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56410471949191878713335739 84615707923787818070003609)
              ·
                refine ⟨63461780942840863552502707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84615707923787818070003609 63461780942840863552502707)
                ·
                  refine ⟨95192671414261295328754061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63461780942840863552502707 95192671414261295328754061)
                  ·
                    refine ⟨35697251780347985748282773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95192671414261295328754061 35697251780347985748282773)
                    ·
                      refine ⟨1673308677203811831950755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35697251780347985748282773 1673308677203811831950755)
                      ·
                        rfl

theorem cell23_3258757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_3258757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258757 prefixEnd_3258757 := by exact prefixLift 3258757
  have htrace : WordTrace (prefixWord ++ tailWord_3258757) baseStart_3258757 baseEnd_3258757 := by
    simpa [prefixWord, tailWord_3258757, baseEnd_3258757] using wordTrace_append hprefix tailTrace_3258757
  have hstable : (prefixWord ++ tailWord_3258757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258757).length < 2 ^ (prefixWord ++ tailWord_3258757).sum := by decide
  have hdescent : baseEnd_3258757 < baseStart_3258757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258761 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_3258761 : Nat := 118140960795 + 3258761 * 2 ^ 59
def prefixEnd_3258761 : Nat := 4983230072969 + 3 ^ 40 * 3258761 * 2
def baseEnd_3258761 : Nat := 1673310731126429816300737

theorem tailTrace_3258761 : CollatzResearch.WordTrace tailWord_3258761 prefixEnd_3258761 1673310731126429816300737 := by
  unfold tailWord_3258761
  simp only [CollatzResearch.WordTrace]
  refine ⟨118856778147072923914536137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79237852098048615943024091 118856778147072923914536137)
  ·
    refine ⟨89142583610304692935902103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118856778147072923914536137 89142583610304692935902103)
    ·
      refine ⟨133713875415457039403853155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89142583610304692935902103 133713875415457039403853155)
      ·
        refine ⟨200570813123185559105779733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133713875415457039403853155 200570813123185559105779733)
        ·
          refine ⟨9401756865149323083083425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200570813123185559105779733 9401756865149323083083425)
          ·
            refine ⟨7051317648861992312312569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401756865149323083083425 7051317648861992312312569)
            ·
              refine ⟨5288488236646494234234427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051317648861992312312569 5288488236646494234234427)
              ·
                refine ⟨7932732354969741351351641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288488236646494234234427 7932732354969741351351641)
                ·
                  refine ⟨5949549266227306013513731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932732354969741351351641 5949549266227306013513731)
                  ·
                    refine ⟨8924323899340959020270597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5949549266227306013513731 8924323899340959020270597)
                    ·
                      refine ⟨1673310731126429816300737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8924323899340959020270597 1673310731126429816300737)
                      ·
                        rfl

theorem cell23_3258761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_3258761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258761 prefixEnd_3258761 := by exact prefixLift 3258761
  have htrace : WordTrace (prefixWord ++ tailWord_3258761) baseStart_3258761 baseEnd_3258761 := by
    simpa [prefixWord, tailWord_3258761, baseEnd_3258761] using wordTrace_append hprefix tailTrace_3258761
  have hstable : (prefixWord ++ tailWord_3258761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258761).length < 2 ^ (prefixWord ++ tailWord_3258761).sum := by decide
  have hdescent : baseEnd_3258761 < baseStart_3258761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258784 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 6]
def baseStart_3258784 : Nat := 118140960795 + 3258784 * 2 ^ 59
def prefixEnd_3258784 : Nat := 4983230072969 + 3 ^ 40 * 3258784 * 2
def baseEnd_3258784 : Nat := 185924726797942580701459

theorem tailTrace_3258784 : CollatzResearch.WordTrace tailWord_3258784 prefixEnd_3258784 185924726797942580701459 := by
  unfold tailWord_3258784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59428808512994799421311703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79238411350659732561748937 59428808512994799421311703)
  ·
    refine ⟨89143212769492199131967555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59428808512994799421311703 89143212769492199131967555)
    ·
      refine ⟨133714819154238298697951333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89143212769492199131967555 133714819154238298697951333)
      ·
        refine ⟨25071528591419681005865875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133714819154238298697951333 25071528591419681005865875)
        ·
          refine ⟨37607292887129521508798813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25071528591419681005865875 37607292887129521508798813)
          ·
            refine ⟨14102734832673570565799555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37607292887129521508798813 14102734832673570565799555)
            ·
              refine ⟨21154102249010355848699333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14102734832673570565799555 21154102249010355848699333)
              ·
                refine ⟨3966394171689441721631125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21154102249010355848699333 3966394171689441721631125)
                ·
                  refine ⟨185924726797942580701459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3966394171689441721631125 185924726797942580701459)
                  ·
                    rfl

theorem cell23_3258784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_3258784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258784 prefixEnd_3258784 := by exact prefixLift 3258784
  have htrace : WordTrace (prefixWord ++ tailWord_3258784) baseStart_3258784 baseEnd_3258784 := by
    simpa [prefixWord, tailWord_3258784, baseEnd_3258784] using wordTrace_append hprefix tailTrace_3258784
  have hstable : (prefixWord ++ tailWord_3258784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258784).length < 2 ^ (prefixWord ++ tailWord_3258784).sum := by decide
  have hdescent : baseEnd_3258784 < baseStart_3258784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258845 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_3258845 : Nat := 118140960795 + 3258845 * 2 ^ 59
def prefixEnd_3258845 : Nat := 4983230072969 + 3 ^ 40 * 3258845 * 2
def baseEnd_3258845 : Nat := 1673353863501407487650351

theorem tailTrace_3258845 : CollatzResearch.WordTrace tailWord_3258845 prefixEnd_3258845 1673353863501407487650351 := by
  unfold tailWord_3258845
  simp only [CollatzResearch.WordTrace]
  refine ⟨118859841878768606260593989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79239894585845737507062659 118859841878768606260593989)
  ·
    refine ⟨22286220352269113673861373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118859841878768606260593989 22286220352269113673861373)
    ·
      refine ⟨8357332632100917627698015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22286220352269113673861373 8357332632100917627698015)
      ·
        refine ⟨12535998948151376441547023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357332632100917627698015 12535998948151376441547023)
        ·
          refine ⟨18803998422227064662320535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12535998948151376441547023 18803998422227064662320535)
          ·
            refine ⟨28205997633340596993480803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18803998422227064662320535 28205997633340596993480803)
            ·
              refine ⟨42308996450010895490221205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28205997633340596993480803 42308996450010895490221205)
              ·
                refine ⟨1983234208594260726104119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42308996450010895490221205 1983234208594260726104119)
                ·
                  refine ⟨2974851312891391089156179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983234208594260726104119 2974851312891391089156179)
                  ·
                    refine ⟨4462276969337086633734269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974851312891391089156179 4462276969337086633734269)
                    ·
                      refine ⟨1673353863501407487650351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4462276969337086633734269 1673353863501407487650351)
                      ·
                        rfl

theorem cell23_3258845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_3258845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258845 prefixEnd_3258845 := by exact prefixLift 3258845
  have htrace : WordTrace (prefixWord ++ tailWord_3258845) baseStart_3258845 baseEnd_3258845 := by
    simpa [prefixWord, tailWord_3258845, baseEnd_3258845] using wordTrace_append hprefix tailTrace_3258845
  have hstable : (prefixWord ++ tailWord_3258845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258845).length < 2 ^ (prefixWord ++ tailWord_3258845).sum := by decide
  have hdescent : baseEnd_3258845 < baseStart_3258845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258864 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_3258864 : Nat := 118140960795 + 3258864 * 2 ^ 59
def prefixEnd_3258864 : Nat := 4983230072969 + 3 ^ 40 * 3258864 * 2
def baseEnd_3258864 : Nat := 1673363619633842913312763

theorem tailTrace_3258864 : CollatzResearch.WordTrace tailWord_3258864 prefixEnd_3258864 1673363619633842913312763 := by
  unfold tailWord_3258864
  simp only [CollatzResearch.WordTrace]
  refine ⟨59430267432849886252767823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79240356577133181670357097 59430267432849886252767823)
  ·
    refine ⟨89145401149274829379151735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59430267432849886252767823 89145401149274829379151735)
    ·
      refine ⟨133718101723912244068727603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89145401149274829379151735 133718101723912244068727603)
      ·
        refine ⟨200577152585868366103091405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133718101723912244068727603 200577152585868366103091405)
        ·
          refine ⟨75216432219700637288659277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200577152585868366103091405 75216432219700637288659277)
          ·
            refine ⟨28206162082387738983247229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75216432219700637288659277 28206162082387738983247229)
            ·
              refine ⟨10577310780895402118717711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28206162082387738983247229 10577310780895402118717711)
              ·
                refine ⟨15865966171343103178076567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10577310780895402118717711 15865966171343103178076567)
                ·
                  refine ⟨23798949257014654767114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15865966171343103178076567 23798949257014654767114851)
                  ·
                    refine ⟨35698423885521982150672277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23798949257014654767114851 35698423885521982150672277)
                    ·
                      refine ⟨1673363619633842913312763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35698423885521982150672277 1673363619633842913312763)
                      ·
                        rfl

theorem cell23_3258864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_3258864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258864 prefixEnd_3258864 := by exact prefixLift 3258864
  have htrace : WordTrace (prefixWord ++ tailWord_3258864) baseStart_3258864 baseEnd_3258864 := by
    simpa [prefixWord, tailWord_3258864, baseEnd_3258864] using wordTrace_append hprefix tailTrace_3258864
  have hstable : (prefixWord ++ tailWord_3258864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258864).length < 2 ^ (prefixWord ++ tailWord_3258864).sum := by decide
  have hdescent : baseEnd_3258864 < baseStart_3258864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258911 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 7, 2]
def baseStart_3258911 : Nat := 118140960795 + 3258911 * 2 ^ 59
def prefixEnd_3258911 : Nat := 4983230072969 + 3 ^ 40 * 3258911 * 2
def baseEnd_3258911 : Nat := 1673387753224604229425047

theorem tailTrace_3258911 : CollatzResearch.WordTrace tailWord_3258911 prefixEnd_3258911 1673387753224604229425047 := by
  unfold tailWord_3258911
  simp only [CollatzResearch.WordTrace]
  refine ⟨118862249096529499532496587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79241499397686333021664391 118862249096529499532496587)
  ·
    refine ⟨178293373644794249298744881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118862249096529499532496587 178293373644794249298744881)
    ·
      refine ⟨133720030233595686974058661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178293373644794249298744881 133720030233595686974058661)
      ·
        refine ⟨25072505668799191307635999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133720030233595686974058661 25072505668799191307635999)
        ·
          refine ⟨37608758503198786961453999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25072505668799191307635999 37608758503198786961453999)
          ·
            refine ⟨56413137754798180442180999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37608758503198786961453999 56413137754798180442180999)
            ·
              refine ⟨84619706632197270663271499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56413137754798180442180999 84619706632197270663271499)
              ·
                refine ⟨126929559948295905994907249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84619706632197270663271499 126929559948295905994907249)
                ·
                  refine ⟨95197169961221929496180437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126929559948295905994907249 95197169961221929496180437)
                  ·
                    refine ⟨2231183670966138972566729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95197169961221929496180437 2231183670966138972566729)
                    ·
                      refine ⟨1673387753224604229425047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231183670966138972566729 1673387753224604229425047)
                      ·
                        rfl

theorem cell23_3258911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_3258911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258911 prefixEnd_3258911 := by exact prefixLift 3258911
  have htrace : WordTrace (prefixWord ++ tailWord_3258911) baseStart_3258911 baseEnd_3258911 := by
    simpa [prefixWord, tailWord_3258911, baseEnd_3258911] using wordTrace_append hprefix tailTrace_3258911
  have hstable : (prefixWord ++ tailWord_3258911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258911).length < 2 ^ (prefixWord ++ tailWord_3258911).sum := by decide
  have hdescent : baseEnd_3258911 < baseStart_3258911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258912 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_3258912 : Nat := 118140960795 + 3258912 * 2 ^ 59
def prefixEnd_3258912 : Nat := 4983230072969 + 3 ^ 40 * 3258912 * 2
def baseEnd_3258912 : Nat := 557796088901752908504181

theorem tailTrace_3258912 : CollatzResearch.WordTrace tailWord_3258912 prefixEnd_3258912 557796088901752908504181 := by
  unfold tailWord_3258912
  simp only [CollatzResearch.WordTrace]
  refine ⟨59431142784762938351641495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79241523713017251135521993 59431142784762938351641495)
  ·
    refine ⟨89146714177144407527462243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59431142784762938351641495 89146714177144407527462243)
    ·
      refine ⟨133720071265716611291193365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89146714177144407527462243 133720071265716611291193365)
      ·
        refine ⟨6268128340580466154274689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133720071265716611291193365 6268128340580466154274689)
        ·
          refine ⟨4701096255435349615706017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268128340580466154274689 4701096255435349615706017)
          ·
            refine ⟨3525822191576512211779513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701096255435349615706017 3525822191576512211779513)
            ·
              refine ⟨2644366643682384158834635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525822191576512211779513 2644366643682384158834635)
              ·
                refine ⟨3966549965523576238251953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644366643682384158834635 3966549965523576238251953)
                ·
                  refine ⟨2974912474142682178688965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966549965523576238251953 2974912474142682178688965)
                  ·
                    refine ⟨557796088901752908504181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974912474142682178688965 557796088901752908504181)
                    ·
                      rfl

theorem cell23_3258912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_3258912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258912 prefixEnd_3258912 := by exact prefixLift 3258912
  have htrace : WordTrace (prefixWord ++ tailWord_3258912) baseStart_3258912 baseEnd_3258912 := by
    simpa [prefixWord, tailWord_3258912, baseEnd_3258912] using wordTrace_append hprefix tailTrace_3258912
  have hstable : (prefixWord ++ tailWord_3258912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258912).length < 2 ^ (prefixWord ++ tailWord_3258912).sum := by decide
  have hdescent : baseEnd_3258912 < baseStart_3258912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258919 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3258919 : Nat := 118140960795 + 3258919 * 2 ^ 59
def prefixEnd_3258919 : Nat := 4983230072969 + 3 ^ 40 * 3258919 * 2
def baseEnd_3258919 : Nat := 1673391861069840198125011

theorem tailTrace_3258919 : CollatzResearch.WordTrace tailWord_3258919 prefixEnd_3258919 1673391861069840198125011 := by
  unfold tailWord_3258919
  simp only [CollatzResearch.WordTrace]
  refine ⟨118862540880500516898787811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79241693920333677932525207 118862540880500516898787811)
  ·
    refine ⟨178293811320750775348181717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118862540880500516898787811 178293811320750775348181717)
    ·
      refine ⟨4178761202830096297223009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 178293811320750775348181717 4178761202830096297223009)
      ·
        refine ⟨3134070902122572222917257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178761202830096297223009 3134070902122572222917257)
        ·
          refine ⟨2350553176591929167187943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134070902122572222917257 2350553176591929167187943)
          ·
            refine ⟨3525829764887893750781915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350553176591929167187943 3525829764887893750781915)
            ·
              refine ⟨5288744647331840626172873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525829764887893750781915 5288744647331840626172873)
              ·
                refine ⟨3966558485498880469629655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5288744647331840626172873 3966558485498880469629655)
                ·
                  refine ⟨5949837728248320704444483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966558485498880469629655 5949837728248320704444483)
                  ·
                    refine ⟨8924756592372481056666725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5949837728248320704444483 8924756592372481056666725)
                    ·
                      refine ⟨1673391861069840198125011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8924756592372481056666725 1673391861069840198125011)
                      ·
                        rfl

theorem cell23_3258919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3258919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258919 prefixEnd_3258919 := by exact prefixLift 3258919
  have htrace : WordTrace (prefixWord ++ tailWord_3258919) baseStart_3258919 baseEnd_3258919 := by
    simpa [prefixWord, tailWord_3258919, baseEnd_3258919] using wordTrace_append hprefix tailTrace_3258919
  have hstable : (prefixWord ++ tailWord_3258919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258919).length < 2 ^ (prefixWord ++ tailWord_3258919).sum := by decide
  have hdescent : baseEnd_3258919 < baseStart_3258919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3258961 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_3258961 : Nat := 118140960795 + 3258961 * 2 ^ 59
def prefixEnd_3258961 : Nat := 4983230072969 + 3 ^ 40 * 3258961 * 2
def baseEnd_3258961 : Nat := 1673413427257329033799817

theorem tailTrace_3258961 : CollatzResearch.WordTrace tailWord_3258961 prefixEnd_3258961 1673413427257329033799817 := by
  unfold tailWord_3258961
  simp only [CollatzResearch.WordTrace]
  refine ⟨118864072746348358071816737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79242715164232238714544491 118864072746348358071816737)
  ·
    refine ⟨89148054559761268553862553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118864072746348358071816737 89148054559761268553862553)
    ·
      refine ⟨66861040919820951415396915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89148054559761268553862553 66861040919820951415396915)
      ·
        refine ⟨100291561379731427123095373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66861040919820951415396915 100291561379731427123095373)
        ·
          refine ⟨37609335517399285171160765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100291561379731427123095373 37609335517399285171160765)
          ·
            refine ⟨14103500819024731939185287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37609335517399285171160765 14103500819024731939185287)
            ·
              refine ⟨21155251228537097908777931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14103500819024731939185287 21155251228537097908777931)
              ·
                refine ⟨31732876842805646863166897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21155251228537097908777931 31732876842805646863166897)
                ·
                  refine ⟨23799657632104235147375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31732876842805646863166897 23799657632104235147375173)
                  ·
                    refine ⟨4462435806019544090132845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23799657632104235147375173 4462435806019544090132845)
                    ·
                      refine ⟨1673413427257329033799817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4462435806019544090132845 1673413427257329033799817)
                      ·
                        rfl

theorem cell23_3258961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_3258961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3258961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3258961 prefixEnd_3258961 := by exact prefixLift 3258961
  have htrace : WordTrace (prefixWord ++ tailWord_3258961) baseStart_3258961 baseEnd_3258961 := by
    simpa [prefixWord, tailWord_3258961, baseEnd_3258961] using wordTrace_append hprefix tailTrace_3258961
  have hstable : (prefixWord ++ tailWord_3258961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3258961).length < 2 ^ (prefixWord ++ tailWord_3258961).sum := by decide
  have hdescent : baseEnd_3258961 < baseStart_3258961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3258961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259011 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 2, 5]
def baseStart_3259011 : Nat := 118140960795 + 3259011 * 2 ^ 59
def prefixEnd_3259011 : Nat := 4983230072969 + 3 ^ 40 * 3259011 * 2
def baseEnd_3259011 : Nat := 557813033763351279391529

theorem tailTrace_3259011 : CollatzResearch.WordTrace tailWord_3259011 prefixEnd_3259011 557813033763351279391529 := by
  unfold tailWord_3259011
  simp only [CollatzResearch.WordTrace]
  refine ⟨118865896396167216611136887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79243930930778144407424591 118865896396167216611136887)
  ·
    refine ⟨178298844594250824916705331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118865896396167216611136887 178298844594250824916705331)
    ·
      refine ⟨267448266891376237375057997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178298844594250824916705331 267448266891376237375057997)
      ·
        refine ⟨100293100084266089015646749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267448266891376237375057997 100293100084266089015646749)
        ·
          refine ⟨37609912531599783380867531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100293100084266089015646749 37609912531599783380867531)
          ·
            refine ⟨56414868797399675071301297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37609912531599783380867531 56414868797399675071301297)
            ·
              refine ⟨42311151598049756303475973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56414868797399675071301297 42311151598049756303475973)
              ·
                refine ⟨7933340924634329306901745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42311151598049756303475973 7933340924634329306901745)
                ·
                  refine ⟨5950005693475746980176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933340924634329306901745 5950005693475746980176309)
                  ·
                    refine ⟨557813033763351279391529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5950005693475746980176309 557813033763351279391529)
                    ·
                      rfl

theorem cell23_3259011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].length) (baseStart_3259011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259011 prefixEnd_3259011 := by exact prefixLift 3259011
  have htrace : WordTrace (prefixWord ++ tailWord_3259011) baseStart_3259011 baseEnd_3259011 := by
    simpa [prefixWord, tailWord_3259011, baseEnd_3259011] using wordTrace_append hprefix tailTrace_3259011
  have hstable : (prefixWord ++ tailWord_3259011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259011).length < 2 ^ (prefixWord ++ tailWord_3259011).sum := by decide
  have hdescent : baseEnd_3259011 < baseStart_3259011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259028 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3259028 : Nat := 118140960795 + 3259028 * 2 ^ 59
def prefixEnd_3259028 : Nat := 4983230072969 + 3 ^ 40 * 3259028 * 2
def baseEnd_3259028 : Nat := 557815943487060090554003

theorem tailTrace_3259028 : CollatzResearch.WordTrace tailWord_3259028 prefixEnd_3259028 557815943487060090554003 := by
  unfold tailWord_3259028
  simp only [CollatzResearch.WordTrace]
  refine ⟨59433258218552814257252869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79244344291403752343003825 59433258218552814257252869)
  ·
    refine ⟨11143735915978652673234913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59433258218552814257252869 11143735915978652673234913)
    ·
      refine ⟨8357801936983989504926185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11143735915978652673234913 8357801936983989504926185)
      ·
        refine ⟨6268351452737992128694639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8357801936983989504926185 6268351452737992128694639)
        ·
          refine ⟨9402527179106988193041959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268351452737992128694639 9402527179106988193041959)
          ·
            refine ⟨14103790768660482289562939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9402527179106988193041959 14103790768660482289562939)
            ·
              refine ⟨21155686152990723434344409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14103790768660482289562939 21155686152990723434344409)
              ·
                refine ⟨15866764614743042575758307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21155686152990723434344409 15866764614743042575758307)
                ·
                  refine ⟨23800146922114563863637461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15866764614743042575758307 23800146922114563863637461)
                  ·
                    refine ⟨557815943487060090554003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23800146922114563863637461 557815943487060090554003)
                    ·
                      rfl

theorem cell23_3259028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3259028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259028 prefixEnd_3259028 := by exact prefixLift 3259028
  have htrace : WordTrace (prefixWord ++ tailWord_3259028) baseStart_3259028 baseEnd_3259028 := by
    simpa [prefixWord, tailWord_3259028, baseEnd_3259028] using wordTrace_append hprefix tailTrace_3259028
  have hstable : (prefixWord ++ tailWord_3259028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259028).length < 2 ^ (prefixWord ++ tailWord_3259028).sum := by decide
  have hdescent : baseEnd_3259028 < baseStart_3259028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259031 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3259031 : Nat := 118140960795 + 3259031 * 2 ^ 59
def prefixEnd_3259031 : Nat := 4983230072969 + 3 ^ 40 * 3259031 * 2
def baseEnd_3259031 : Nat := 1673449370903143759924495

theorem tailTrace_3259031 : CollatzResearch.WordTrace tailWord_3259031 prefixEnd_3259031 1673449370903143759924495 := by
  unfold tailWord_3259031
  simp only [CollatzResearch.WordTrace]
  refine ⟨118866625856094760026864947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79244417237396506684576631 118866625856094760026864947)
  ·
    refine ⟨178299938784142140040297421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118866625856094760026864947 178299938784142140040297421)
    ·
      refine ⟨66862477044053302515111533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178299938784142140040297421 66862477044053302515111533)
      ·
        refine ⟨25073428891519988443166825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66862477044053302515111533 25073428891519988443166825)
        ·
          refine ⟨18805071668639991332375119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25073428891519988443166825 18805071668639991332375119)
          ·
            refine ⟨28207607502959986998562679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18805071668639991332375119 28207607502959986998562679)
            ·
              refine ⟨42311411254439980497844019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28207607502959986998562679 42311411254439980497844019)
              ·
                refine ⟨63467116881659970746766029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42311411254439980497844019 63467116881659970746766029)
                ·
                  refine ⟨23800168830622489030037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63467116881659970746766029 23800168830622489030037261)
                  ·
                    refine ⟨8925063311483433386263973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23800168830622489030037261 8925063311483433386263973)
                    ·
                      refine ⟨1673449370903143759924495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8925063311483433386263973 1673449370903143759924495)
                      ·
                        rfl

theorem cell23_3259031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3259031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259031 prefixEnd_3259031 := by exact prefixLift 3259031
  have htrace : WordTrace (prefixWord ++ tailWord_3259031) baseStart_3259031 baseEnd_3259031 := by
    simpa [prefixWord, tailWord_3259031, baseEnd_3259031] using wordTrace_append hprefix tailTrace_3259031
  have hstable : (prefixWord ++ tailWord_3259031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259031).length < 2 ^ (prefixWord ++ tailWord_3259031).sum := by decide
  have hdescent : baseEnd_3259031 < baseStart_3259031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259062 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3259062 : Nat := 118140960795 + 3259062 * 2 ^ 59
def prefixEnd_3259062 : Nat := 4983230072969 + 3 ^ 40 * 3259062 * 2
def baseEnd_3259062 : Nat := 557821762934477712878951

theorem tailTrace_3259062 : CollatzResearch.WordTrace tailWord_3259062 prefixEnd_3259062 557821762934477712878951 := by
  unfold tailWord_3259062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429234782436403270077715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79245171012654968214162293 7429234782436403270077715)
  ·
    refine ⟨11143852173654604905116573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429234782436403270077715 11143852173654604905116573)
    ·
      refine ⟨4178944565120476839418715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11143852173654604905116573 4178944565120476839418715)
      ·
        refine ⟨6268416847680715259128073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178944565120476839418715 6268416847680715259128073)
        ·
          refine ⟨4701312635760536444346055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268416847680715259128073 4701312635760536444346055)
          ·
            refine ⟨7051968953640804666519083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701312635760536444346055 7051968953640804666519083)
            ·
              refine ⟨10577953430461206999778625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051968953640804666519083 10577953430461206999778625)
              ·
                refine ⟨7933465072845905249833969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10577953430461206999778625 7933465072845905249833969)
                ·
                  refine ⟨5950098804634428937375477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933465072845905249833969 5950098804634428937375477)
                  ·
                    refine ⟨557821762934477712878951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5950098804634428937375477 557821762934477712878951)
                    ·
                      rfl

theorem cell23_3259062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3259062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259062 prefixEnd_3259062 := by exact prefixLift 3259062
  have htrace : WordTrace (prefixWord ++ tailWord_3259062) baseStart_3259062 baseEnd_3259062 := by
    simpa [prefixWord, tailWord_3259062, baseEnd_3259062] using wordTrace_append hprefix tailTrace_3259062
  have hstable : (prefixWord ++ tailWord_3259062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259062).length < 2 ^ (prefixWord ++ tailWord_3259062).sum := by decide
  have hdescent : baseEnd_3259062 < baseStart_3259062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259071 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 8]
def baseStart_3259071 : Nat := 118140960795 + 3259071 * 2 ^ 59
def prefixEnd_3259071 : Nat := 4983230072969 + 3 ^ 40 * 3259071 * 2
def baseEnd_3259071 : Nat := 185941101125480400380479

theorem tailTrace_3259071 : CollatzResearch.WordTrace tailWord_3259071 prefixEnd_3259071 185941101125480400380479 := by
  unfold tailWord_3259071
  simp only [CollatzResearch.WordTrace]
  refine ⟨118868084775949846858321067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79245389850633231238880711 118868084775949846858321067)
  ·
    refine ⟨178302127163924770287481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118868084775949846858321067 178302127163924770287481601)
    ·
      refine ⟨133726595372943577715611201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178302127163924770287481601 133726595372943577715611201)
      ·
        refine ⟨100294946529707683286708401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133726595372943577715611201 100294946529707683286708401)
        ·
          refine ⟨75221209897280762465031301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100294946529707683286708401 75221209897280762465031301)
          ·
            refine ⟨14103976855740142962193369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75221209897280762465031301 14103976855740142962193369)
            ·
              refine ⟨10577982641805107221645027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14103976855740142962193369 10577982641805107221645027)
              ·
                refine ⟨15866973962707660832467541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10577982641805107221645027 15866973962707660832467541)
                ·
                  refine ⟨185941101125480400380479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15866973962707660832467541 185941101125480400380479)
                  ·
                    rfl

theorem cell23_3259071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 8].length) (baseStart_3259071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259071 prefixEnd_3259071 := by exact prefixLift 3259071
  have htrace : WordTrace (prefixWord ++ tailWord_3259071) baseStart_3259071 baseEnd_3259071 := by
    simpa [prefixWord, tailWord_3259071, baseEnd_3259071] using wordTrace_append hprefix tailTrace_3259071
  have hstable : (prefixWord ++ tailWord_3259071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259071).length < 2 ^ (prefixWord ++ tailWord_3259071).sum := by decide
  have hdescent : baseEnd_3259071 < baseStart_3259071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259148 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_3259148 : Nat := 118140960795 + 3259148 * 2 ^ 59
def prefixEnd_3259148 : Nat := 4983230072969 + 3 ^ 40 * 3259148 * 2
def baseEnd_3259148 : Nat := 557836482713239934053819

theorem tailTrace_3259148 : CollatzResearch.WordTrace tailWord_3259148 prefixEnd_3259148 557836482713239934053819 := by
  unfold tailWord_3259148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435446598335444504437049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79247262131113926005916065 59435446598335444504437049)
  ·
    refine ⟨44576584948751583378327787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59435446598335444504437049 44576584948751583378327787)
    ·
      refine ⟨66864877423127375067491681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44576584948751583378327787 66864877423127375067491681)
      ·
        refine ⟨50148658067345531300618761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66864877423127375067491681 50148658067345531300618761)
        ·
          refine ⟨37611493550509148475464071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50148658067345531300618761 37611493550509148475464071)
          ·
            refine ⟨56417240325763722713196107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37611493550509148475464071 56417240325763722713196107)
            ·
              refine ⟨84625860488645584069794161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56417240325763722713196107 84625860488645584069794161)
              ·
                refine ⟨63469395366484188052345621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84625860488645584069794161 63469395366484188052345621)
                ·
                  refine ⟨2975127907803946314953701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63469395366484188052345621 2975127907803946314953701)
                  ·
                    refine ⟨557836482713239934053819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975127907803946314953701 557836482713239934053819)
                    ·
                      rfl

theorem cell23_3259148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_3259148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259148 prefixEnd_3259148 := by exact prefixLift 3259148
  have htrace : WordTrace (prefixWord ++ tailWord_3259148) baseStart_3259148 baseEnd_3259148 := by
    simpa [prefixWord, tailWord_3259148, baseEnd_3259148] using wordTrace_append hprefix tailTrace_3259148
  have hstable : (prefixWord ++ tailWord_3259148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259148).length < 2 ^ (prefixWord ++ tailWord_3259148).sum := by decide
  have hdescent : baseEnd_3259148 < baseStart_3259148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259159 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3259159 : Nat := 118140960795 + 3259159 * 2 ^ 59
def prefixEnd_3259159 : Nat := 4983230072969 + 3 ^ 40 * 3259159 * 2
def baseEnd_3259159 : Nat := 1673515096426919259123907

theorem tailTrace_3259159 : CollatzResearch.WordTrace tailWord_3259159 prefixEnd_3259159 1673515096426919259123907 := by
  unfold tailWord_3259159
  simp only [CollatzResearch.WordTrace]
  refine ⟨118871294399631037887524531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79247529599754025258349687 118871294399631037887524531)
  ·
    refine ⟨178306941599446556831286797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118871294399631037887524531 178306941599446556831286797)
    ·
      refine ⟨66865103099792458811732549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178306941599446556831286797 66865103099792458811732549)
      ·
        refine ⟨12537206831211086027199853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66865103099792458811732549 12537206831211086027199853)
        ·
          refine ⟨4701452561704157260199945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12537206831211086027199853 4701452561704157260199945)
          ·
            refine ⟨3526089421278117945149959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701452561704157260199945 3526089421278117945149959)
            ·
              refine ⟨5289134131917176917724939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526089421278117945149959 5289134131917176917724939)
              ·
                refine ⟨7933701197875765376587409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289134131917176917724939 7933701197875765376587409)
                ·
                  refine ⟨5950275898406824032440557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933701197875765376587409 5950275898406824032440557)
                  ·
                    refine ⟨2231353461902559012165209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5950275898406824032440557 2231353461902559012165209)
                    ·
                      refine ⟨1673515096426919259123907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231353461902559012165209 1673515096426919259123907)
                      ·
                        rfl

theorem cell23_3259159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3259159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259159 prefixEnd_3259159 := by exact prefixLift 3259159
  have htrace : WordTrace (prefixWord ++ tailWord_3259159) baseStart_3259159 baseEnd_3259159 := by
    simpa [prefixWord, tailWord_3259159, baseEnd_3259159] using wordTrace_append hprefix tailTrace_3259159
  have hstable : (prefixWord ++ tailWord_3259159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259159).length < 2 ^ (prefixWord ++ tailWord_3259159).sum := by decide
  have hdescent : baseEnd_3259159 < baseStart_3259159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259172 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3259172 : Nat := 118140960795 + 3259172 * 2 ^ 59
def prefixEnd_3259172 : Nat := 4983230072969 + 3 ^ 40 * 3259172 * 2
def baseEnd_3259172 : Nat := 1673521771675427708261347

theorem tailTrace_3259172 : CollatzResearch.WordTrace tailWord_3259172 prefixEnd_3259172 1673521771675427708261347 := by
  unfold tailWord_3259172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435884274291970553873885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79247845699055960738498513 59435884274291970553873885)
  ·
    refine ⟨22288456602859488957702707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59435884274291970553873885 22288456602859488957702707)
    ·
      refine ⟨33432684904289233436554061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22288456602859488957702707 33432684904289233436554061)
      ·
        refine ⟨12537256839108462538707773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33432684904289233436554061 12537256839108462538707773)
        ·
          refine ⟨4701471314665673452015415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12537256839108462538707773 4701471314665673452015415)
          ·
            refine ⟨7052206971998510178023123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701471314665673452015415 7052206971998510178023123)
            ·
              refine ⟨10578310457997765267034685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052206971998510178023123 10578310457997765267034685)
              ·
                refine ⟨3966866421749161975138007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10578310457997765267034685 3966866421749161975138007)
                ·
                  refine ⟨5950299632623742962707011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966866421749161975138007 5950299632623742962707011)
                  ·
                    refine ⟨8925449448935614444060517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950299632623742962707011 8925449448935614444060517)
                    ·
                      refine ⟨1673521771675427708261347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8925449448935614444060517 1673521771675427708261347)
                      ·
                        rfl

theorem cell23_3259172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3259172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259172 prefixEnd_3259172 := by exact prefixLift 3259172
  have htrace : WordTrace (prefixWord ++ tailWord_3259172) baseStart_3259172 baseEnd_3259172 := by
    simpa [prefixWord, tailWord_3259172, baseEnd_3259172] using wordTrace_append hprefix tailTrace_3259172
  have hstable : (prefixWord ++ tailWord_3259172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259172).length < 2 ^ (prefixWord ++ tailWord_3259172).sum := by decide
  have hdescent : baseEnd_3259172 < baseStart_3259172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259182 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3259182 : Nat := 118140960795 + 3259182 * 2 ^ 59
def prefixEnd_3259182 : Nat := 4983230072969 + 3 ^ 40 * 3259182 * 2
def baseEnd_3259182 : Nat := 557842302160657556378767

theorem tailTrace_3259182 : CollatzResearch.WordTrace tailWord_3259182 prefixEnd_3259182 557842302160657556378767 := by
  unfold tailWord_3259182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859016659818464101951475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79248088852365141877074533 14859016659818464101951475)
  ·
    refine ⟨22288524989727696152927213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14859016659818464101951475 22288524989727696152927213)
    ·
      refine ⟨8358196871147886057347705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22288524989727696152927213 8358196871147886057347705)
      ·
        refine ⟨6268647653360914543010779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358196871147886057347705 6268647653360914543010779)
        ·
          refine ⟨9402971480041371814516169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268647653360914543010779 9402971480041371814516169)
          ·
            refine ⟨7052228610031028860887127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402971480041371814516169 7052228610031028860887127)
            ·
              refine ⟨10578342915046543291330691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052228610031028860887127 10578342915046543291330691)
              ·
                refine ⟨15867514372569814936996037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10578342915046543291330691 15867514372569814936996037)
                ·
                  refine ⟨2975158944856840300686757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15867514372569814936996037 2975158944856840300686757)
                  ·
                    refine ⟨557842302160657556378767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975158944856840300686757 557842302160657556378767)
                    ·
                      rfl

theorem cell23_3259182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3259182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259182 prefixEnd_3259182 := by exact prefixLift 3259182
  have htrace : WordTrace (prefixWord ++ tailWord_3259182) baseStart_3259182 baseEnd_3259182 := by
    simpa [prefixWord, tailWord_3259182, baseEnd_3259182] using wordTrace_append hprefix tailTrace_3259182
  have hstable : (prefixWord ++ tailWord_3259182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259182).length < 2 ^ (prefixWord ++ tailWord_3259182).sum := by decide
  have hdescent : baseEnd_3259182 < baseStart_3259182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259189 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_3259189 : Nat := 118140960795 + 3259189 * 2 ^ 59
def prefixEnd_3259189 : Nat := 4983230072969 + 3 ^ 40 * 3259189 * 2
def baseEnd_3259189 : Nat := 1673530500846554141748769

theorem tailTrace_3259189 : CollatzResearch.WordTrace tailWord_3259189 prefixEnd_3259189 1673530500846554141748769 := by
  unfold tailWord_3259189
  simp only [CollatzResearch.WordTrace]
  refine ⟨118872388589522353011116621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79248259059681568674077747 118872388589522353011116621)
  ·
    refine ⟨44577145721070882379168733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118872388589522353011116621 44577145721070882379168733)
    ·
      refine ⟨16716429645401580892188275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44577145721070882379168733 16716429645401580892188275)
      ·
        refine ⟨25074644468102371338282413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16716429645401580892188275 25074644468102371338282413)
        ·
          refine ⟨9402991675538389251855905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25074644468102371338282413 9402991675538389251855905)
          ·
            refine ⟨7052243756653791938891929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402991675538389251855905 7052243756653791938891929)
            ·
              refine ⟨5289182817490343954168947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052243756653791938891929 5289182817490343954168947)
              ·
                refine ⟨7933774226235515931253421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289182817490343954168947 7933774226235515931253421)
                ·
                  refine ⟨2975165334838318474220033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7933774226235515931253421 2975165334838318474220033)
                  ·
                    refine ⟨2231374001128738855665025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2975165334838318474220033 2231374001128738855665025)
                    ·
                      refine ⟨1673530500846554141748769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231374001128738855665025 1673530500846554141748769)
                      ·
                        rfl

theorem cell23_3259189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_3259189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259189 prefixEnd_3259189 := by exact prefixLift 3259189
  have htrace : WordTrace (prefixWord ++ tailWord_3259189) baseStart_3259189 baseEnd_3259189 := by
    simpa [prefixWord, tailWord_3259189, baseEnd_3259189] using wordTrace_append hprefix tailTrace_3259189
  have hstable : (prefixWord ++ tailWord_3259189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259189).length < 2 ^ (prefixWord ++ tailWord_3259189).sum := by decide
  have hdescent : baseEnd_3259189 < baseStart_3259189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259206 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3259206 : Nat := 118140960795 + 3259206 * 2 ^ 59
def prefixEnd_3259206 : Nat := 4983230072969 + 3 ^ 40 * 3259206 * 2
def baseEnd_3259206 : Nat := 1673539230017680575236191

theorem tailTrace_3259206 : CollatzResearch.WordTrace tailWord_3259206 prefixEnd_3259206 1673539230017680575236191 := by
  unfold tailWord_3259206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714781519701898903577671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79248672420307176609656981 3714781519701898903577671)
  ·
    refine ⟨5572172279552848355366507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714781519701898903577671 5572172279552848355366507)
    ·
      refine ⟨8358258419329272533049761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572172279552848355366507 8358258419329272533049761)
      ·
        refine ⟨6268693814496954399787321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358258419329272533049761 6268693814496954399787321)
        ·
          refine ⟨4701520360872715799840491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268693814496954399787321 4701520360872715799840491)
          ·
            refine ⟨7052280541309073699760737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701520360872715799840491 7052280541309073699760737)
            ·
              refine ⟨5289210405981805274820553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052280541309073699760737 5289210405981805274820553)
              ·
                refine ⟨3966907804486353956115415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5289210405981805274820553 3966907804486353956115415)
                ·
                  refine ⟨5950361706729530934173123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966907804486353956115415 5950361706729530934173123)
                  ·
                    refine ⟨8925542560094296401259685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950361706729530934173123 8925542560094296401259685)
                    ·
                      refine ⟨1673539230017680575236191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8925542560094296401259685 1673539230017680575236191)
                      ·
                        rfl

theorem cell23_3259206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3259206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259206 prefixEnd_3259206 := by exact prefixLift 3259206
  have htrace : WordTrace (prefixWord ++ tailWord_3259206) baseStart_3259206 baseEnd_3259206 := by
    simpa [prefixWord, tailWord_3259206, baseEnd_3259206] using wordTrace_append hprefix tailTrace_3259206
  have hstable : (prefixWord ++ tailWord_3259206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259206).length < 2 ^ (prefixWord ++ tailWord_3259206).sum := by decide
  have hdescent : baseEnd_3259206 < baseStart_3259206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259218 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3259218 : Nat := 118140960795 + 3259218 * 2 ^ 59
def prefixEnd_3259218 : Nat := 4983230072969 + 3 ^ 40 * 3259218 * 2
def baseEnd_3259218 : Nat := 1673545391785534528286135

theorem tailTrace_3259218 : CollatzResearch.WordTrace tailWord_3259218 prefixEnd_3259218 1673545391785534528286135 := by
  unfold tailWord_3259218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718361576604322740980577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79248964204278193975948205 29718361576604322740980577)
  ·
    refine ⟨22288771182453242055735433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29718361576604322740980577 22288771182453242055735433)
    ·
      refine ⟨16716578386839931541801575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22288771182453242055735433 16716578386839931541801575)
      ·
        refine ⟨25074867580259897312702363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16716578386839931541801575 25074867580259897312702363)
        ·
          refine ⟨37612301370389845969053545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25074867580259897312702363 37612301370389845969053545)
          ·
            refine ⟨28209226027792384476790159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37612301370389845969053545 28209226027792384476790159)
            ·
              refine ⟨42313839041688576715185239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28209226027792384476790159 42313839041688576715185239)
              ·
                refine ⟨63470758562532865072777859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42313839041688576715185239 63470758562532865072777859)
                ·
                  refine ⟨95206137843799297609166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63470758562532865072777859 95206137843799297609166789)
                  ·
                    refine ⟨17851150845712368301718773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95206137843799297609166789 17851150845712368301718773)
                    ·
                      refine ⟨1673545391785534528286135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17851150845712368301718773 1673545391785534528286135)
                      ·
                        rfl

theorem cell23_3259218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3259218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259218 prefixEnd_3259218 := by exact prefixLift 3259218
  have htrace : WordTrace (prefixWord ++ tailWord_3259218) baseStart_3259218 baseEnd_3259218 := by
    simpa [prefixWord, tailWord_3259218, baseEnd_3259218] using wordTrace_append hprefix tailTrace_3259218
  have hstable : (prefixWord ++ tailWord_3259218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259218).length < 2 ^ (prefixWord ++ tailWord_3259218).sum := by decide
  have hdescent : baseEnd_3259218 < baseStart_3259218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259232 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2]
def baseStart_3259232 : Nat := 118140960795 + 3259232 * 2 ^ 59
def prefixEnd_3259232 : Nat := 4983230072969 + 3 ^ 40 * 3259232 * 2
def baseEnd_3259232 : Nat := 1673552580514697473511071

theorem tailTrace_3259232 : CollatzResearch.WordTrace tailWord_3259232 prefixEnd_3259232 1673552580514697473511071 := by
  unfold tailWord_3259232
  simp only [CollatzResearch.WordTrace]
  refine ⟨59436978464183285677465975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79249304618911047569954633 59436978464183285677465975)
  ·
    refine ⟨89155467696274928516198963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59436978464183285677465975 89155467696274928516198963)
    ·
      refine ⟨133733201544412392774298445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89155467696274928516198963 133733201544412392774298445)
      ·
        refine ⟨50149950579154647290361917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133733201544412392774298445 50149950579154647290361917)
        ·
          refine ⟨18806231467182992733885719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50149950579154647290361917 18806231467182992733885719)
          ·
            refine ⟨28209347200774489100828579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18806231467182992733885719 28209347200774489100828579)
            ·
              refine ⟨42314020801161733651242869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28209347200774489100828579 42314020801161733651242869)
              ·
                refine ⟨3966939450108912529804019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42314020801161733651242869 3966939450108912529804019)
                ·
                  refine ⟨5950409175163368794706029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966939450108912529804019 5950409175163368794706029)
                  ·
                    refine ⟨2231403440686263298014761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5950409175163368794706029 2231403440686263298014761)
                    ·
                      refine ⟨1673552580514697473511071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231403440686263298014761 1673552580514697473511071)
                      ·
                        rfl

theorem cell23_3259232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_3259232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259232 prefixEnd_3259232 := by exact prefixLift 3259232
  have htrace : WordTrace (prefixWord ++ tailWord_3259232) baseStart_3259232 baseEnd_3259232 := by
    simpa [prefixWord, tailWord_3259232, baseEnd_3259232] using wordTrace_append hprefix tailTrace_3259232
  have hstable : (prefixWord ++ tailWord_3259232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259232).length < 2 ^ (prefixWord ++ tailWord_3259232).sum := by decide
  have hdescent : baseEnd_3259232 < baseStart_3259232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259258 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3259258 : Nat := 118140960795 + 3259258 * 2 ^ 59
def prefixEnd_3259258 : Nat := 4983230072969 + 3 ^ 40 * 3259258 * 2
def baseEnd_3259258 : Nat := 1673565931011714371785951

theorem tailTrace_3259258 : CollatzResearch.WordTrace tailWord_3259258 prefixEnd_3259258 1673565931011714371785951 := by
  unfold tailWord_3259258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718726306568094448844607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79249936817514918530252285 29718726306568094448844607)
  ·
    refine ⟨44578089459852141673266911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29718726306568094448844607 44578089459852141673266911)
    ·
      refine ⟨66867134189778212509900367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44578089459852141673266911 66867134189778212509900367)
      ·
        refine ⟨100300701284667318764850551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66867134189778212509900367 100300701284667318764850551)
        ·
          refine ⟨150451051927000978147275827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100300701284667318764850551 150451051927000978147275827)
          ·
            refine ⟨225676577890501467220913741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150451051927000978147275827 225676577890501467220913741)
            ·
              refine ⟨84628716708938050207842653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225676577890501467220913741 84628716708938050207842653)
              ·
                refine ⟨31735768765851768827940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84628716708938050207842653 31735768765851768827940995)
                ·
                  refine ⟨47603653148777653241911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31735768765851768827940995 47603653148777653241911493)
                  ·
                    refine ⟨8925684965395809982858405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47603653148777653241911493 8925684965395809982858405)
                    ·
                      refine ⟨1673565931011714371785951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8925684965395809982858405 1673565931011714371785951)
                      ·
                        rfl

theorem cell23_3259258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3259258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259258 prefixEnd_3259258 := by exact prefixLift 3259258
  have htrace : WordTrace (prefixWord ++ tailWord_3259258) baseStart_3259258 baseEnd_3259258 := by
    simpa [prefixWord, tailWord_3259258, baseEnd_3259258] using wordTrace_append hprefix tailTrace_3259258
  have hstable : (prefixWord ++ tailWord_3259258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259258).length < 2 ^ (prefixWord ++ tailWord_3259258).sum := by decide
  have hdescent : baseEnd_3259258 < baseStart_3259258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259268 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 9]
def baseStart_3259268 : Nat := 118140960795 + 3259268 * 2 ^ 59
def prefixEnd_3259268 : Nat := 4983230072969 + 3 ^ 40 * 3259268 * 2
def baseEnd_3259268 : Nat := 185952340646473259184545

theorem tailTrace_3259268 : CollatzResearch.WordTrace tailWord_3259268 prefixEnd_3259268 185952340646473259184545 := by
  unfold tailWord_3259268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59437634978118074751621229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79250179970824099668828305 59437634978118074751621229)
  ·
    refine ⟨22289113116794278031857961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59437634978118074751621229 22289113116794278031857961)
    ·
      refine ⟨16716834837595708523893471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22289113116794278031857961 16716834837595708523893471)
      ·
        refine ⟨25075252256393562785840207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16716834837595708523893471 25075252256393562785840207)
        ·
          refine ⟨37612878384590344178760311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25075252256393562785840207 37612878384590344178760311)
          ·
            refine ⟨56419317576885516268140467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37612878384590344178760311 56419317576885516268140467)
            ·
              refine ⟨84628976365328274402210701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56419317576885516268140467 84628976365328274402210701)
              ·
                refine ⟨31735866136998102900829013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84628976365328274402210701 31735866136998102900829013)
                ·
                  refine ⟨185952340646473259184545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31735866136998102900829013 185952340646473259184545)
                  ·
                    rfl

theorem cell23_3259268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_3259268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259268 prefixEnd_3259268 := by exact prefixLift 3259268
  have htrace : WordTrace (prefixWord ++ tailWord_3259268) baseStart_3259268 baseEnd_3259268 := by
    simpa [prefixWord, tailWord_3259268, baseEnd_3259268] using wordTrace_append hprefix tailTrace_3259268
  have hstable : (prefixWord ++ tailWord_3259268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259268).length < 2 ^ (prefixWord ++ tailWord_3259268).sum := by decide
  have hdescent : baseEnd_3259268 < baseStart_3259268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259305 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 7, 2]
def baseStart_3259305 : Nat := 118140960795 + 3259305 * 2 ^ 59
def prefixEnd_3259305 : Nat := 4983230072969 + 3 ^ 40 * 3259305 * 2
def baseEnd_3259305 : Nat := 1673590064602475687898235

theorem tailTrace_3259305 : CollatzResearch.WordTrace tailWord_3259305 prefixEnd_3259305 1673590064602475687898235 := by
  unfold tailWord_3259305
  simp only [CollatzResearch.WordTrace]
  refine ⟨118876619457102104822339369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79251079638068069881559579 118876619457102104822339369)
  ·
    refine ⟨89157464592826578616754527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118876619457102104822339369 89157464592826578616754527)
    ·
      refine ⟨133736196889239867925131791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89157464592826578616754527 133736196889239867925131791)
      ·
        refine ⟨200604295333859801887697687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133736196889239867925131791 200604295333859801887697687)
        ·
          refine ⟨300906443000789702831546531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200604295333859801887697687 300906443000789702831546531)
          ·
            refine ⟨451359664501184554247319797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300906443000789702831546531 451359664501184554247319797)
            ·
              refine ⟨42314968546986051960686231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451359664501184554247319797 42314968546986051960686231)
              ·
                refine ⟨63472452820479077941029347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42314968546986051960686231 63472452820479077941029347)
                ·
                  refine ⟨95208679230718616911544021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63472452820479077941029347 95208679230718616911544021)
                  ·
                    refine ⟨2231453419469967583864313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95208679230718616911544021 2231453419469967583864313)
                    ·
                      refine ⟨1673590064602475687898235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231453419469967583864313 1673590064602475687898235)
                      ·
                        rfl

theorem cell23_3259305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7, 2].length) (baseStart_3259305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259305 prefixEnd_3259305 := by exact prefixLift 3259305
  have htrace : WordTrace (prefixWord ++ tailWord_3259305) baseStart_3259305 baseEnd_3259305 := by
    simpa [prefixWord, tailWord_3259305, baseEnd_3259305] using wordTrace_append hprefix tailTrace_3259305
  have hstable : (prefixWord ++ tailWord_3259305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259305).length < 2 ^ (prefixWord ++ tailWord_3259305).sum := by decide
  have hdescent : baseEnd_3259305 < baseStart_3259305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259309 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3259309 : Nat := 118140960795 + 3259309 * 2 ^ 59
def prefixEnd_3259309 : Nat := 4983230072969 + 3 ^ 40 * 3259309 * 2
def baseEnd_3259309 : Nat := 1673592118525093672248217

theorem tailTrace_3259309 : CollatzResearch.WordTrace tailWord_3259309 prefixEnd_3259309 1673592118525093672248217 := by
  unfold tailWord_3259309
  simp only [CollatzResearch.WordTrace]
  refine ⟨118876765349087613505484981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79251176899391742336989987 118876765349087613505484981)
  ·
    refine ⟨11144696751476963766139217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118876765349087613505484981 11144696751476963766139217)
    ·
      refine ⟨8358522563607722824604413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11144696751476963766139217 8358522563607722824604413)
      ·
        refine ⟨3134445961352896059226655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8358522563607722824604413 3134445961352896059226655)
        ·
          refine ⟨4701668942029344088839983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134445961352896059226655 4701668942029344088839983)
          ·
            refine ⟨7052503413044016133259975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701668942029344088839983 7052503413044016133259975)
            ·
              refine ⟨10578755119566024199889963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052503413044016133259975 10578755119566024199889963)
              ·
                refine ⟨15868132679349036299834945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10578755119566024199889963 15868132679349036299834945)
                ·
                  refine ⟨11901099509511777224876209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15868132679349036299834945 11901099509511777224876209)
                  ·
                    refine ⟨8925824632133832918657157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11901099509511777224876209 8925824632133832918657157)
                    ·
                      refine ⟨1673592118525093672248217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8925824632133832918657157 1673592118525093672248217)
                      ·
                        rfl

theorem cell23_3259309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3259309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259309 prefixEnd_3259309 := by exact prefixLift 3259309
  have htrace : WordTrace (prefixWord ++ tailWord_3259309) baseStart_3259309 baseEnd_3259309 := by
    simpa [prefixWord, tailWord_3259309, baseEnd_3259309] using wordTrace_append hprefix tailTrace_3259309
  have hstable : (prefixWord ++ tailWord_3259309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259309).length < 2 ^ (prefixWord ++ tailWord_3259309).sum := by decide
  have hdescent : baseEnd_3259309 < baseStart_3259309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259334 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3259334 : Nat := 118140960795 + 3259334 * 2 ^ 59
def prefixEnd_3259334 : Nat := 4983230072969 + 3 ^ 40 * 3259334 * 2
def baseEnd_3259334 : Nat := 1673604955541456074435603

theorem tailTrace_3259334 : CollatzResearch.WordTrace tailWord_3259334 prefixEnd_3259334 1673604955541456074435603 := by
  unfold tailWord_3259334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714927411687407586723283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79251784782664695183430037 3714927411687407586723283)
  ·
    refine ⟨5572391117531111380084925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714927411687407586723283 5572391117531111380084925)
    ·
      refine ⟨2089646669074166767531847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5572391117531111380084925 2089646669074166767531847)
      ·
        refine ⟨3134470003611250151297771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089646669074166767531847 3134470003611250151297771)
        ·
          refine ⟨4701705005416875226946657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134470003611250151297771 4701705005416875226946657)
          ·
            refine ⟨3526278754062656420209993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701705005416875226946657 3526278754062656420209993)
            ·
              refine ⟨2644709065546992315157495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526278754062656420209993 2644709065546992315157495)
              ·
                refine ⟨3967063598320488472736243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644709065546992315157495 3967063598320488472736243)
                ·
                  refine ⟨5950595397480732709104365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967063598320488472736243 5950595397480732709104365)
                  ·
                    refine ⟨2231473274055274765914137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5950595397480732709104365 2231473274055274765914137)
                    ·
                      refine ⟨1673604955541456074435603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231473274055274765914137 1673604955541456074435603)
                      ·
                        rfl

theorem cell23_3259334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3259334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259334 prefixEnd_3259334 := by exact prefixLift 3259334
  have htrace : WordTrace (prefixWord ++ tailWord_3259334) baseStart_3259334 baseEnd_3259334 := by
    simpa [prefixWord, tailWord_3259334, baseEnd_3259334] using wordTrace_append hprefix tailTrace_3259334
  have hstable : (prefixWord ++ tailWord_3259334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259334).length < 2 ^ (prefixWord ++ tailWord_3259334).sum := by decide
  have hdescent : baseEnd_3259334 < baseStart_3259334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259345 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_3259345 : Nat := 118140960795 + 3259345 * 2 ^ 59
def prefixEnd_3259345 : Nat := 4983230072969 + 3 ^ 40 * 3259345 * 2
def baseEnd_3259345 : Nat := 557870201276218510466017

theorem tailTrace_3259345 : CollatzResearch.WordTrace tailWord_3259345 prefixEnd_3259345 557870201276218510466017 := by
  unfold tailWord_3259345
  simp only [CollatzResearch.WordTrace]
  refine ⟨118878078376957191653795489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79252052251304794435863659 118878078376957191653795489)
  ·
    refine ⟨89158558782717893740346617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118878078376957191653795489 89158558782717893740346617)
    ·
      refine ⟨66868919087038420305259963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89158558782717893740346617 66868919087038420305259963)
      ·
        refine ⟨100303378630557630457889945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66868919087038420305259963 100303378630557630457889945)
        ·
          refine ⟨75227533972918222843417459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100303378630557630457889945 75227533972918222843417459)
          ·
            refine ⟨112841300959377334265126189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75227533972918222843417459 112841300959377334265126189)
            ·
              refine ⟨42315487859766500349422321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112841300959377334265126189 42315487859766500349422321)
              ·
                refine ⟨31736615894824875262066741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42315487859766500349422321 31736615894824875262066741)
                ·
                  refine ⟨2975307740139832055818757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31736615894824875262066741 2975307740139832055818757)
                  ·
                    refine ⟨557870201276218510466017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975307740139832055818757 557870201276218510466017)
                    ·
                      rfl

theorem cell23_3259345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_3259345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259345 prefixEnd_3259345 := by exact prefixLift 3259345
  have htrace : WordTrace (prefixWord ++ tailWord_3259345) baseStart_3259345 baseEnd_3259345 := by
    simpa [prefixWord, tailWord_3259345, baseEnd_3259345] using wordTrace_append hprefix tailTrace_3259345
  have hstable : (prefixWord ++ tailWord_3259345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259345).length < 2 ^ (prefixWord ++ tailWord_3259345).sum := by decide
  have hdescent : baseEnd_3259345 < baseStart_3259345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259352 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_3259352 : Nat := 118140960795 + 3259352 * 2 ^ 59
def prefixEnd_3259352 : Nat := 4983230072969 + 3 ^ 40 * 3259352 * 2
def baseEnd_3259352 : Nat := 1673614198193237004010519

theorem tailTrace_3259352 : CollatzResearch.WordTrace tailWord_3259352 prefixEnd_3259352 1673614198193237004010519 := by
  unfold tailWord_3259352
  simp only [CollatzResearch.WordTrace]
  refine ⟨59439166843965915924650155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79252222458621221232866873 59439166843965915924650155)
  ·
    refine ⟨89158750265948873886975233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59439166843965915924650155 89158750265948873886975233)
    ·
      refine ⟨66869062699461655415231425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89158750265948873886975233 66869062699461655415231425)
      ·
        refine ⟨50151797024596241561423569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66869062699461655415231425 50151797024596241561423569)
        ·
          refine ⟨37613847768447181171067677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50151797024596241561423569 37613847768447181171067677)
          ·
            refine ⟨14105192913167692939150379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37613847768447181171067677 14105192913167692939150379)
            ·
              refine ⟨21157789369751539408725569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14105192913167692939150379 21157789369751539408725569)
              ·
                refine ⟨15868342027313654556544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21157789369751539408725569 15868342027313654556544177)
                ·
                  refine ⟨11901256520485240917408133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15868342027313654556544177 11901256520485240917408133)
                  ·
                    refine ⟨2231485597590982672014025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11901256520485240917408133 2231485597590982672014025)
                    ·
                      refine ⟨1673614198193237004010519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231485597590982672014025 1673614198193237004010519)
                      ·
                        rfl

theorem cell23_3259352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_3259352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259352 prefixEnd_3259352 := by exact prefixLift 3259352
  have htrace : WordTrace (prefixWord ++ tailWord_3259352) baseStart_3259352 baseEnd_3259352 := by
    simpa [prefixWord, tailWord_3259352, baseEnd_3259352] using wordTrace_append hprefix tailTrace_3259352
  have hstable : (prefixWord ++ tailWord_3259352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259352).length < 2 ^ (prefixWord ++ tailWord_3259352).sum := by decide
  have hdescent : baseEnd_3259352 < baseStart_3259352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259385 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3259385 : Nat := 118140960795 + 3259385 * 2 ^ 59
def prefixEnd_3259385 : Nat := 4983230072969 + 3 ^ 40 * 3259385 * 2
def baseEnd_3259385 : Nat := 1673631143054835374897867

theorem tailTrace_3259385 : CollatzResearch.WordTrace tailWord_3259385 prefixEnd_3259385 1673631143054835374897867 := by
  unfold tailWord_3259385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118879537296812278485251609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79253024864541518990167739 118879537296812278485251609)
  ·
    refine ⟨89159652972609208863938707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118879537296812278485251609 89159652972609208863938707)
    ·
      refine ⟨133739479458913813295908061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89159652972609208863938707 133739479458913813295908061)
      ·
        refine ⟨50152304797092679985965523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133739479458913813295908061 50152304797092679985965523)
        ·
          refine ⟨75228457195639019978948285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50152304797092679985965523 75228457195639019978948285)
          ·
            refine ⟨28210671448364632492105607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75228457195639019978948285 28210671448364632492105607)
            ·
              refine ⟨42316007172546948738158411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28210671448364632492105607 42316007172546948738158411)
              ·
                refine ⟨63474010758820423107237617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42316007172546948738158411 63474010758820423107237617)
                ·
                  refine ⟨47605508069115317330428213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63474010758820423107237617 47605508069115317330428213)
                  ·
                    refine ⟨4463016381479560999727645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47605508069115317330428213 4463016381479560999727645)
                    ·
                      refine ⟨1673631143054835374897867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463016381479560999727645 1673631143054835374897867)
                      ·
                        rfl

theorem cell23_3259385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3259385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259385 prefixEnd_3259385 := by exact prefixLift 3259385
  have htrace : WordTrace (prefixWord ++ tailWord_3259385) baseStart_3259385 baseEnd_3259385 := by
    simpa [prefixWord, tailWord_3259385, baseEnd_3259385] using wordTrace_append hprefix tailTrace_3259385
  have hstable : (prefixWord ++ tailWord_3259385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259385).length < 2 ^ (prefixWord ++ tailWord_3259385).sum := by decide
  have hdescent : baseEnd_3259385 < baseStart_3259385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259435 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 6]
def baseStart_3259435 : Nat := 118140960795 + 3259435 * 2 ^ 59
def prefixEnd_3259435 : Nat := 4983230072969 + 3 ^ 40 * 3259435 * 2
def baseEnd_3259435 : Nat := 557885605695853393090879

theorem tailTrace_3259435 : CollatzResearch.WordTrace tailWord_3259435 prefixEnd_3259435 557885605695853393090879 := by
  unfold tailWord_3259435
  simp only [CollatzResearch.WordTrace]
  refine ⟨118881360946631137024571759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79254240631087424683047839 118881360946631137024571759)
  ·
    refine ⟨178322041419946705536857639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118881360946631137024571759 178322041419946705536857639)
    ·
      refine ⟨267483062129920058305286459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178322041419946705536857639 267483062129920058305286459)
      ·
        refine ⟨401224593194880087457929689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267483062129920058305286459 401224593194880087457929689)
        ·
          refine ⟨300918444896160065593447267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401224593194880087457929689 300918444896160065593447267)
          ·
            refine ⟨451377667344240098390170901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300918444896160065593447267 451377667344240098390170901)
            ·
              refine ⟨21158328156761254612039261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451377667344240098390170901 21158328156761254612039261)
              ·
                refine ⟨7934373058785470479514723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21158328156761254612039261 7934373058785470479514723)
                ·
                  refine ⟨11901559588178205719272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934373058785470479514723 11901559588178205719272085)
                  ·
                    refine ⟨557885605695853393090879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11901559588178205719272085 557885605695853393090879)
                    ·
                      rfl

theorem cell23_3259435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_3259435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259435 prefixEnd_3259435 := by exact prefixLift 3259435
  have htrace : WordTrace (prefixWord ++ tailWord_3259435) baseStart_3259435 baseEnd_3259435 := by
    simpa [prefixWord, tailWord_3259435, baseEnd_3259435] using wordTrace_append hprefix tailTrace_3259435
  have hstable : (prefixWord ++ tailWord_3259435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259435).length < 2 ^ (prefixWord ++ tailWord_3259435).sum := by decide
  have hdescent : baseEnd_3259435 < baseStart_3259435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259442 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3259442 : Nat := 118140960795 + 3259442 * 2 ^ 59
def prefixEnd_3259442 : Nat := 4983230072969 + 3 ^ 40 * 3259442 * 2
def baseEnd_3259442 : Nat := 1673660411452141651885105

theorem tailTrace_3259442 : CollatzResearch.WordTrace tailWord_3259442 prefixEnd_3259442 1673660411452141651885105 := by
  unfold tailWord_3259442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29720404064401444305019145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79254410838403851480051053 29720404064401444305019145)
  ·
    refine ⟨22290303048301083228764359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29720404064401444305019145 22290303048301083228764359)
    ·
      refine ⟨33435454572451624843146539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22290303048301083228764359 33435454572451624843146539)
      ·
        refine ⟨50153181858677437264719809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33435454572451624843146539 50153181858677437264719809)
        ·
          refine ⟨37614886394008077948539857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50153181858677437264719809 37614886394008077948539857)
          ·
            refine ⟨28211164795506058461404893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37614886394008077948539857 28211164795506058461404893)
            ·
              refine ⟨10579186798314771923026835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28211164795506058461404893 10579186798314771923026835)
              ·
                refine ⟨15868780197472157884540253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579186798314771923026835 15868780197472157884540253)
                ·
                  refine ⟨5950792574052059206702595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15868780197472157884540253 5950792574052059206702595)
                  ·
                    refine ⟨8926188861078088810053893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950792574052059206702595 8926188861078088810053893)
                    ·
                      refine ⟨1673660411452141651885105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8926188861078088810053893 1673660411452141651885105)
                      ·
                        rfl

theorem cell23_3259442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3259442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259442 prefixEnd_3259442 := by exact prefixLift 3259442
  have htrace : WordTrace (prefixWord ++ tailWord_3259442) baseStart_3259442 baseEnd_3259442 := by
    simpa [prefixWord, tailWord_3259442, baseEnd_3259442] using wordTrace_append hprefix tailTrace_3259442
  have hstable : (prefixWord ++ tailWord_3259442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259442).length < 2 ^ (prefixWord ++ tailWord_3259442).sum := by decide
  have hdescent : baseEnd_3259442 < baseStart_3259442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259446 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3259446 : Nat := 118140960795 + 3259446 * 2 ^ 59
def prefixEnd_3259446 : Nat := 4983230072969 + 3 ^ 40 * 3259446 * 2
def baseEnd_3259446 : Nat := 1673662465374759636235087

theorem tailTrace_3259446 : CollatzResearch.WordTrace tailWord_3259446 prefixEnd_3259446 1673662465374759636235087 := by
  unfold tailWord_3259446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430110134349455368951387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79254508099727523935481461 7430110134349455368951387)
  ·
    refine ⟨11145165201524183053427081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430110134349455368951387 11145165201524183053427081)
    ·
      refine ⟨8358873901143137290070311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11145165201524183053427081 8358873901143137290070311)
      ·
        refine ⟨12538310851714705935105467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358873901143137290070311 12538310851714705935105467)
        ·
          refine ⟨18807466277572058902658201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538310851714705935105467 18807466277572058902658201)
          ·
            refine ⟨14105599708179044176993651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18807466277572058902658201 14105599708179044176993651)
            ·
              refine ⟨21158399562268566265490477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14105599708179044176993651 21158399562268566265490477)
              ·
                refine ⟨7934399835850712349558929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21158399562268566265490477 7934399835850712349558929)
                ·
                  refine ⟨5950799876888034262169197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7934399835850712349558929 5950799876888034262169197)
                  ·
                    refine ⟨2231549953833012848313449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5950799876888034262169197 2231549953833012848313449)
                    ·
                      refine ⟨1673662465374759636235087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231549953833012848313449 1673662465374759636235087)
                      ·
                        rfl

theorem cell23_3259446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3259446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259446 prefixEnd_3259446 := by exact prefixLift 3259446
  have htrace : WordTrace (prefixWord ++ tailWord_3259446) baseStart_3259446 baseEnd_3259446 := by
    simpa [prefixWord, tailWord_3259446, baseEnd_3259446] using wordTrace_append hprefix tailTrace_3259446
  have hstable : (prefixWord ++ tailWord_3259446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259446).length < 2 ^ (prefixWord ++ tailWord_3259446).sum := by decide
  have hdescent : baseEnd_3259446 < baseStart_3259446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259452 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3259452 : Nat := 118140960795 + 3259452 * 2 ^ 59
def prefixEnd_3259452 : Nat := 4983230072969 + 3 ^ 40 * 3259452 * 2
def baseEnd_3259452 : Nat := 557888515419562204253353

theorem tailTrace_3259452 : CollatzResearch.WordTrace tailWord_3259452 prefixEnd_3259452 557888515419562204253353 := by
  unfold tailWord_3259452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59440990493784774463970305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79254653991713032618627073 59440990493784774463970305)
  ·
    refine ⟨44580742870338580847977729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59440990493784774463970305 44580742870338580847977729)
    ·
      refine ⟨33435557152753935635983297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44580742870338580847977729 33435557152753935635983297)
      ·
        refine ⟨25076667864565451726987473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33435557152753935635983297 25076667864565451726987473)
        ·
          refine ⟨18807500898424088795240605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25076667864565451726987473 18807500898424088795240605)
          ·
            refine ⟨7052812836909033298215227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18807500898424088795240605 7052812836909033298215227)
            ·
              refine ⟨10579219255363549947322841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052812836909033298215227 10579219255363549947322841)
              ·
                refine ⟨7934414441522662460492131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10579219255363549947322841 7934414441522662460492131)
                ·
                  refine ⟨11901621662283993690738197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934414441522662460492131 11901621662283993690738197)
                  ·
                    refine ⟨557888515419562204253353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11901621662283993690738197 557888515419562204253353)
                    ·
                      rfl

theorem cell23_3259452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3259452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259452 prefixEnd_3259452 := by exact prefixLift 3259452
  have htrace : WordTrace (prefixWord ++ tailWord_3259452) baseStart_3259452 baseEnd_3259452 := by
    simpa [prefixWord, tailWord_3259452, baseEnd_3259452] using wordTrace_append hprefix tailTrace_3259452
  have hstable : (prefixWord ++ tailWord_3259452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259452).length < 2 ^ (prefixWord ++ tailWord_3259452).sum := by decide
  have hdescent : baseEnd_3259452 < baseStart_3259452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259459 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 1, 1, 4]
def baseStart_3259459 : Nat := 118140960795 + 3259459 * 2 ^ 59
def prefixEnd_3259459 : Nat := 4983230072969 + 3 ^ 40 * 3259459 * 2
def baseEnd_3259459 : Nat := 1673669140623268085372527

theorem tailTrace_3259459 : CollatzResearch.WordTrace tailWord_3259459 prefixEnd_3259459 1673669140623268085372527 := by
  unfold tailWord_3259459
  simp only [CollatzResearch.WordTrace]
  refine ⟨118882236298544189123445431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79254824199029459415630287 118882236298544189123445431)
  ·
    refine ⟨178323354447816283685168147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118882236298544189123445431 178323354447816283685168147)
    ·
      refine ⟨267485031671724425527752221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178323354447816283685168147 267485031671724425527752221)
      ·
        refine ⟨100306886876896659572907083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267485031671724425527752221 100306886876896659572907083)
        ·
          refine ⟨150460330315344989359360625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100306886876896659572907083 150460330315344989359360625)
          ·
            refine ⟨112845247736508742019520469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150460330315344989359360625 112845247736508742019520469)
            ·
              refine ⟨2644810493824423641082511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112845247736508742019520469 2644810493824423641082511)
              ·
                refine ⟨3967215740736635461623767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644810493824423641082511 3967215740736635461623767)
                ·
                  refine ⟨5950823611104953192435651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967215740736635461623767 5950823611104953192435651)
                  ·
                    refine ⟨8926235416657429788653477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950823611104953192435651 8926235416657429788653477)
                    ·
                      refine ⟨1673669140623268085372527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8926235416657429788653477 1673669140623268085372527)
                      ·
                        rfl

theorem cell23_3259459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_3259459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259459 prefixEnd_3259459 := by exact prefixLift 3259459
  have htrace : WordTrace (prefixWord ++ tailWord_3259459) baseStart_3259459 baseEnd_3259459 := by
    simpa [prefixWord, tailWord_3259459, baseEnd_3259459] using wordTrace_append hprefix tailTrace_3259459
  have hstable : (prefixWord ++ tailWord_3259459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259459).length < 2 ^ (prefixWord ++ tailWord_3259459).sum := by decide
  have hdescent : baseEnd_3259459 < baseStart_3259459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259486 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3259486 : Nat := 118140960795 + 3259486 * 2 ^ 59
def prefixEnd_3259486 : Nat := 4983230072969 + 3 ^ 40 * 3259486 * 2
def baseEnd_3259486 : Nat := 557894334866979826578301

theorem tailTrace_3259486 : CollatzResearch.WordTrace tailWord_3259486 prefixEnd_3259486 557894334866979826578301 := by
  unfold tailWord_3259486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860402633680796591834789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79255480712964248489785541 14860402633680796591834789)
  ·
    refine ⟨2786325493815149360969023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14860402633680796591834789 2786325493815149360969023)
    ·
      refine ⟨4179488240722724041453535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786325493815149360969023 4179488240722724041453535)
      ·
        refine ⟨6269232361084086062180303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179488240722724041453535 6269232361084086062180303)
        ·
          refine ⟨9403848541626129093270455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269232361084086062180303 9403848541626129093270455)
          ·
            refine ⟨14105772812439193639905683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403848541626129093270455 14105772812439193639905683)
            ·
              refine ⟨21158659218658790459858525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14105772812439193639905683 21158659218658790459858525)
              ·
                refine ⟨7934497206997046422446947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21158659218658790459858525 7934497206997046422446947)
                ·
                  refine ⟨11901745810495569633670421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934497206997046422446947 11901745810495569633670421)
                  ·
                    refine ⟨557894334866979826578301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11901745810495569633670421 557894334866979826578301)
                    ·
                      rfl

theorem cell23_3259486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3259486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259486 prefixEnd_3259486 := by exact prefixLift 3259486
  have htrace : WordTrace (prefixWord ++ tailWord_3259486) baseStart_3259486 baseEnd_3259486 := by
    simpa [prefixWord, tailWord_3259486, baseEnd_3259486] using wordTrace_append hprefix tailTrace_3259486
  have hstable : (prefixWord ++ tailWord_3259486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259486).length < 2 ^ (prefixWord ++ tailWord_3259486).sum := by decide
  have hdescent : baseEnd_3259486 < baseStart_3259486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259510 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3259510 : Nat := 118140960795 + 3259510 * 2 ^ 59
def prefixEnd_3259510 : Nat := 4983230072969 + 3 ^ 40 * 3259510 * 2
def baseEnd_3259510 : Nat := 1673695328136647385834793

theorem tailTrace_3259510 : CollatzResearch.WordTrace tailWord_3259510 prefixEnd_3259510 1673695328136647385834793 := by
  unfold tailWord_3259510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430256026334964052096999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79256064280906283222367989 7430256026334964052096999)
  ·
    refine ⟨11145384039502446078145499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430256026334964052096999 11145384039502446078145499)
    ·
      refine ⟨16718076059253669117218249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11145384039502446078145499 16718076059253669117218249)
      ·
        refine ⟨12538557044440251837913687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16718076059253669117218249 12538557044440251837913687)
        ·
          refine ⟨18807835566660377756870531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538557044440251837913687 18807835566660377756870531)
          ·
            refine ⟨28211753349990566635305797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18807835566660377756870531 28211753349990566635305797)
            ·
              refine ⟨5289703753123231244119837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28211753349990566635305797 5289703753123231244119837)
              ·
                refine ⟨1983638907421211716544939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289703753123231244119837 1983638907421211716544939)
                ·
                  refine ⟨2975458361131817574817409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983638907421211716544939 2975458361131817574817409)
                  ·
                    refine ⟨2231593770848863181113057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2975458361131817574817409 2231593770848863181113057)
                    ·
                      refine ⟨1673695328136647385834793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231593770848863181113057 1673695328136647385834793)
                      ·
                        rfl

theorem cell23_3259510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3259510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259510 prefixEnd_3259510 := by exact prefixLift 3259510
  have htrace : WordTrace (prefixWord ++ tailWord_3259510) baseStart_3259510 baseEnd_3259510 := by
    simpa [prefixWord, tailWord_3259510, baseEnd_3259510] using wordTrace_append hprefix tailTrace_3259510
  have hstable : (prefixWord ++ tailWord_3259510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259510).length < 2 ^ (prefixWord ++ tailWord_3259510).sum := by decide
  have hdescent : baseEnd_3259510 < baseStart_3259510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259513 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 1, 2, 3]
def baseStart_3259513 : Nat := 118140960795 + 3259513 * 2 ^ 59
def prefixEnd_3259513 : Nat := 4983230072969 + 3 ^ 40 * 3259513 * 2
def baseEnd_3259513 : Nat := 1673696868578610874097279

theorem tailTrace_3259513 : CollatzResearch.WordTrace tailWord_3259513 prefixEnd_3259513 1673696868578610874097279 := by
  unfold tailWord_3259513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118884205840348556345911193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79256137226899037563940795 118884205840348556345911193)
  ·
    refine ⟨89163154380261417259433395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118884205840348556345911193 89163154380261417259433395)
    ·
      refine ⟨133744731570392125889150093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89163154380261417259433395 133744731570392125889150093)
      ·
        refine ⟨50154274338897047208431285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133744731570392125889150093 50154274338897047208431285)
        ·
          refine ⟨4701963219271598175790433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50154274338897047208431285 4701963219271598175790433)
          ·
            refine ⟨3526472414453698631842825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701963219271598175790433 3526472414453698631842825)
            ·
              refine ⟨2644854310840273973882119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526472414453698631842825 2644854310840273973882119)
              ·
                refine ⟨3967281466260410960823179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644854310840273973882119 3967281466260410960823179)
                ·
                  refine ⟨5950922199390616441234769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967281466260410960823179 5950922199390616441234769)
                  ·
                    refine ⟨4463191649542962330926077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950922199390616441234769 4463191649542962330926077)
                    ·
                      refine ⟨1673696868578610874097279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463191649542962330926077 1673696868578610874097279)
                      ·
                        rfl

theorem cell23_3259513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_3259513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259513 prefixEnd_3259513 := by exact prefixLift 3259513
  have htrace : WordTrace (prefixWord ++ tailWord_3259513) baseStart_3259513 baseEnd_3259513 := by
    simpa [prefixWord, tailWord_3259513, baseEnd_3259513] using wordTrace_append hprefix tailTrace_3259513
  have hstable : (prefixWord ++ tailWord_3259513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259513).length < 2 ^ (prefixWord ++ tailWord_3259513).sum := by decide
  have hdescent : baseEnd_3259513 < baseStart_3259513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259543 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_3259543 : Nat := 118140960795 + 3259543 * 2 ^ 59
def prefixEnd_3259543 : Nat := 4983230072969 + 3 ^ 40 * 3259543 * 2
def baseEnd_3259543 : Nat := 1673712272998245756722141

theorem tailTrace_3259543 : CollatzResearch.WordTrace tailWord_3259543 prefixEnd_3259543 1673712272998245756722141 := by
  unfold tailWord_3259543
  simp only [CollatzResearch.WordTrace]
  refine ⟨118885300030239871469503283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79256866686826580979668855 118885300030239871469503283)
  ·
    refine ⟨178327950045359807204254925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118885300030239871469503283 178327950045359807204254925)
    ·
      refine ⟨66872981267009927701595597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178327950045359807204254925 66872981267009927701595597)
      ·
        refine ⟨25077367975128722888098349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66872981267009927701595597 25077367975128722888098349)
        ·
          refine ⟨9404012990673271083036881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25077367975128722888098349 9404012990673271083036881)
          ·
            refine ⟨7053009743004953312277661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9404012990673271083036881 7053009743004953312277661)
            ·
              refine ⟨2644878653626857492104123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053009743004953312277661 2644878653626857492104123)
              ·
                refine ⟨3967317980440286238156185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644878653626857492104123 3967317980440286238156185)
                ·
                  refine ⟨2975488485330214678617139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3967317980440286238156185 2975488485330214678617139)
                  ·
                    refine ⟨4463232727995322017925709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975488485330214678617139 4463232727995322017925709)
                    ·
                      refine ⟨1673712272998245756722141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463232727995322017925709 1673712272998245756722141)
                      ·
                        rfl

theorem cell23_3259543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_3259543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259543 prefixEnd_3259543 := by exact prefixLift 3259543
  have htrace : WordTrace (prefixWord ++ tailWord_3259543) baseStart_3259543 baseEnd_3259543 := by
    simpa [prefixWord, tailWord_3259543, baseEnd_3259543] using wordTrace_append hprefix tailTrace_3259543
  have hstable : (prefixWord ++ tailWord_3259543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259543).length < 2 ^ (prefixWord ++ tailWord_3259543).sum := by decide
  have hdescent : baseEnd_3259543 < baseStart_3259543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259552 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3259552 : Nat := 118140960795 + 3259552 * 2 ^ 59
def prefixEnd_3259552 : Nat := 4983230072969 + 3 ^ 40 * 3259552 * 2
def baseEnd_3259552 : Nat := 1673716894324136221509599

theorem tailTrace_3259552 : CollatzResearch.WordTrace tailWord_3259552 prefixEnd_3259552 1673716894324136221509599 := by
  unfold tailWord_3259552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59442814143603633003290455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79257085524804844004387273 59442814143603633003290455)
  ·
    refine ⟨89164221215405449504935683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59442814143603633003290455 89164221215405449504935683)
    ·
      refine ⟨133746331823108174257403525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89164221215405449504935683 133746331823108174257403525)
      ·
        refine ⟨25077437216832782673263161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133746331823108174257403525 25077437216832782673263161)
        ·
          refine ⟨18808077912624587004947371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25077437216832782673263161 18808077912624587004947371)
          ·
            refine ⟨28212116868936880507421057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18808077912624587004947371 28212116868936880507421057)
            ·
              refine ⟨21159087651702660380565793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28212116868936880507421057 21159087651702660380565793)
              ·
                refine ⟨15869315738776995285424345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21159087651702660380565793 15869315738776995285424345)
                ·
                  refine ⟨11901986804082746464068259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15869315738776995285424345 11901986804082746464068259)
                  ·
                    refine ⟨17852980206124119696102389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11901986804082746464068259 17852980206124119696102389)
                    ·
                      refine ⟨1673716894324136221509599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17852980206124119696102389 1673716894324136221509599)
                      ·
                        rfl

theorem cell23_3259552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3259552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259552 prefixEnd_3259552 := by exact prefixLift 3259552
  have htrace : WordTrace (prefixWord ++ tailWord_3259552) baseStart_3259552 baseEnd_3259552 := by
    simpa [prefixWord, tailWord_3259552, baseEnd_3259552] using wordTrace_append hprefix tailTrace_3259552
  have hstable : (prefixWord ++ tailWord_3259552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259552).length < 2 ^ (prefixWord ++ tailWord_3259552).sum := by decide
  have hdescent : baseEnd_3259552 < baseStart_3259552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259569 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3259569 : Nat := 118140960795 + 3259569 * 2 ^ 59
def prefixEnd_3259569 : Nat := 4983230072969 + 3 ^ 40 * 3259569 * 2
def baseEnd_3259569 : Nat := 1673725623495262654997021

theorem tailTrace_3259569 : CollatzResearch.WordTrace tailWord_3259569 prefixEnd_3259569 1673725623495262654997021 := by
  unfold tailWord_3259569
  simp only [CollatzResearch.WordTrace]
  refine ⟨118886248328145677909949761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79257498885430451939966507 118886248328145677909949761)
  ·
    refine ⟨89164686246109258432462321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118886248328145677909949761 89164686246109258432462321)
    ·
      refine ⟨66873514684581943824346741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89164686246109258432462321 66873514684581943824346741)
      ·
        refine ⟨6269392001679557233532507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66873514684581943824346741 6269392001679557233532507)
        ·
          refine ⟨9404088002519335850298761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269392001679557233532507 9404088002519335850298761)
          ·
            refine ⟨7053066001889501887724071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9404088002519335850298761 7053066001889501887724071)
            ·
              refine ⟨10579599002834252831586107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053066001889501887724071 10579599002834252831586107)
              ·
                refine ⟨15869398504251379247379161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579599002834252831586107 15869398504251379247379161)
                ·
                  refine ⟨11902048878188534435534371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15869398504251379247379161 11902048878188534435534371)
                  ·
                    refine ⟨17853073317282801653301557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11902048878188534435534371 17853073317282801653301557)
                    ·
                      refine ⟨1673725623495262654997021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17853073317282801653301557 1673725623495262654997021)
                      ·
                        rfl

theorem cell23_3259569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3259569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259569 prefixEnd_3259569 := by exact prefixLift 3259569
  have htrace : WordTrace (prefixWord ++ tailWord_3259569) baseStart_3259569 baseEnd_3259569 := by
    simpa [prefixWord, tailWord_3259569, baseEnd_3259569] using wordTrace_append hprefix tailTrace_3259569
  have hstable : (prefixWord ++ tailWord_3259569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259569).length < 2 ^ (prefixWord ++ tailWord_3259569).sum := by decide
  have hdescent : baseEnd_3259569 < baseStart_3259569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259629 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3259629 : Nat := 118140960795 + 3259629 * 2 ^ 59
def prefixEnd_3259629 : Nat := 4983230072969 + 3 ^ 40 * 3259629 * 2
def baseEnd_3259629 : Nat := 1673756432334532420246745

theorem tailTrace_3259629 : CollatzResearch.WordTrace tailWord_3259629 prefixEnd_3259629 1673756432334532420246745 := by
  unfold tailWord_3259629
  simp only [CollatzResearch.WordTrace]
  refine ⟨118888436707928308157133941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79258957805285538771422627 118888436707928308157133941)
  ·
    refine ⟨11145790941368278889731307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118888436707928308157133941 11145790941368278889731307)
    ·
      refine ⟨16718686412052418334596961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11145790941368278889731307 16718686412052418334596961)
      ·
        refine ⟨12539014809039313750947721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16718686412052418334596961 12539014809039313750947721)
        ·
          refine ⟨9404261106779485313210791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12539014809039313750947721 9404261106779485313210791)
          ·
            refine ⟨14106391660169227969816187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404261106779485313210791 14106391660169227969816187)
            ·
              refine ⟨21159587490253841954724281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14106391660169227969816187 21159587490253841954724281)
              ·
                refine ⟨15869690617690381466043211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21159587490253841954724281 15869690617690381466043211)
                ·
                  refine ⟨23804535926535572199064817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15869690617690381466043211 23804535926535572199064817)
                  ·
                    refine ⟨17853401944901679149298613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23804535926535572199064817 17853401944901679149298613)
                    ·
                      refine ⟨1673756432334532420246745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17853401944901679149298613 1673756432334532420246745)
                      ·
                        rfl

theorem cell23_3259629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3259629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259629 prefixEnd_3259629 := by exact prefixLift 3259629
  have htrace : WordTrace (prefixWord ++ tailWord_3259629) baseStart_3259629 baseEnd_3259629 := by
    simpa [prefixWord, tailWord_3259629, baseEnd_3259629] using wordTrace_append hprefix tailTrace_3259629
  have hstable : (prefixWord ++ tailWord_3259629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259629).length < 2 ^ (prefixWord ++ tailWord_3259629).sum := by decide
  have hdescent : baseEnd_3259629 < baseStart_3259629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_3259639 : Nat := 118140960795 + 3259639 * 2 ^ 59
def prefixEnd_3259639 : Nat := 4983230072969 + 3 ^ 40 * 3259639 * 2
def baseEnd_3259639 : Nat := 1673761567141077381121699

theorem tailTrace_3259639 : CollatzResearch.WordTrace tailWord_3259639 prefixEnd_3259639 1673761567141077381121699 := by
  unfold tailWord_3259639
  simp only [CollatzResearch.WordTrace]
  refine ⟨118888801437892079864997971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79259200958594719909998647 118888801437892079864997971)
  ·
    refine ⟨178333202156838119797496957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118888801437892079864997971 178333202156838119797496957)
    ·
      refine ⟨66874950808814294924061359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178333202156838119797496957 66874950808814294924061359)
      ·
        refine ⟨100312426213221442386092039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66874950808814294924061359 100312426213221442386092039)
        ·
          refine ⟨150468639319832163579138059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100312426213221442386092039 150468639319832163579138059)
          ·
            refine ⟨225702958979748245368707089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150468639319832163579138059 225702958979748245368707089)
            ·
              refine ⟨169277219234811184026530317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225702958979748245368707089 169277219234811184026530317)
              ·
                refine ⟨63478957213054194009948869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169277219234811184026530317 63478957213054194009948869)
                ·
                  refine ⟨11902304477447661376865413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63478957213054194009948869 11902304477447661376865413)
                  ·
                    refine ⟨2231682089521436508162265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11902304477447661376865413 2231682089521436508162265)
                    ·
                      refine ⟨1673761567141077381121699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2231682089521436508162265 1673761567141077381121699)
                      ·
                        rfl

theorem cell23_3259639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_3259639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259639 prefixEnd_3259639 := by exact prefixLift 3259639
  have htrace : WordTrace (prefixWord ++ tailWord_3259639) baseStart_3259639 baseEnd_3259639 := by
    simpa [prefixWord, tailWord_3259639, baseEnd_3259639] using wordTrace_append hprefix tailTrace_3259639
  have hstable : (prefixWord ++ tailWord_3259639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259639).length < 2 ^ (prefixWord ++ tailWord_3259639).sum := by decide
  have hdescent : baseEnd_3259639 < baseStart_3259639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259642 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3259642 : Nat := 118140960795 + 3259642 * 2 ^ 59
def prefixEnd_3259642 : Nat := 4983230072969 + 3 ^ 40 * 3259642 * 2
def baseEnd_3259642 : Nat := 1673763107583040869384185

theorem tailTrace_3259642 : CollatzResearch.WordTrace tailWord_3259642 prefixEnd_3259642 1673763107583040869384185 := by
  unfold tailWord_3259642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722227714220302844339295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79259273904587474251571453 29722227714220302844339295)
  ·
    refine ⟨44583341571330454266508943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29722227714220302844339295 44583341571330454266508943)
    ·
      refine ⟨66875012356995681399763415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44583341571330454266508943 66875012356995681399763415)
      ·
        refine ⟨100312518535493522099645123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66875012356995681399763415 100312518535493522099645123)
        ·
          refine ⟨150468777803240283149467685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100312518535493522099645123 150468777803240283149467685)
          ·
            refine ⟨28212895838107553090525191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150468777803240283149467685 28212895838107553090525191)
            ·
              refine ⟨42319343757161329635787787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28212895838107553090525191 42319343757161329635787787)
              ·
                refine ⟨63479015635741994453681681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42319343757161329635787787 63479015635741994453681681)
                ·
                  refine ⟨47609261726806495840261261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63479015635741994453681681 47609261726806495840261261)
                  ·
                    refine ⟨17853473147552435940097973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47609261726806495840261261 17853473147552435940097973)
                    ·
                      refine ⟨1673763107583040869384185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17853473147552435940097973 1673763107583040869384185)
                      ·
                        rfl

theorem cell23_3259642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3259642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259642 prefixEnd_3259642 := by exact prefixLift 3259642
  have htrace : WordTrace (prefixWord ++ tailWord_3259642) baseStart_3259642 baseEnd_3259642 := by
    simpa [prefixWord, tailWord_3259642, baseEnd_3259642] using wordTrace_append hprefix tailTrace_3259642
  have hstable : (prefixWord ++ tailWord_3259642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259642).length < 2 ^ (prefixWord ++ tailWord_3259642).sum := by decide
  have hdescent : baseEnd_3259642 < baseStart_3259642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259676 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3259676 : Nat := 118140960795 + 3259676 * 2 ^ 59
def prefixEnd_3259676 : Nat := 4983230072969 + 3 ^ 40 * 3259676 * 2
def baseEnd_3259676 : Nat := 1673780565925293736359029

theorem tailTrace_3259676 : CollatzResearch.WordTrace tailWord_3259676 prefixEnd_3259676 1673780565925293736359029 := by
  unfold tailWord_3259676
  simp only [CollatzResearch.WordTrace]
  refine ⟨59445075469379017592047441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79260100625838690122729921 59445075469379017592047441)
  ·
    refine ⟨44583806602034263194035581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59445075469379017592047441 44583806602034263194035581)
    ·
      refine ⟨16718927475762848697763343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44583806602034263194035581 16718927475762848697763343)
      ·
        refine ⟨25078391213644273046645015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16718927475762848697763343 25078391213644273046645015)
        ·
          refine ⟨37617586820466409569967523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25078391213644273046645015 37617586820466409569967523)
          ·
            refine ⟨56426380230699614354951285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37617586820466409569967523 56426380230699614354951285)
            ·
              refine ⟨5289973146628088845776683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56426380230699614354951285 5289973146628088845776683)
              ·
                refine ⟨7934959719942133268665025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289973146628088845776683 7934959719942133268665025)
                ·
                  refine ⟨5951219789956599951498769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7934959719942133268665025 5951219789956599951498769)
                  ·
                    refine ⟨4463414842467449963624077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951219789956599951498769 4463414842467449963624077)
                    ·
                      refine ⟨1673780565925293736359029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463414842467449963624077 1673780565925293736359029)
                      ·
                        rfl

theorem cell23_3259676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3259676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259676 prefixEnd_3259676 := by exact prefixLift 3259676
  have htrace : WordTrace (prefixWord ++ tailWord_3259676) baseStart_3259676 baseEnd_3259676 := by
    simpa [prefixWord, tailWord_3259676, baseEnd_3259676] using wordTrace_append hprefix tailTrace_3259676
  have hstable : (prefixWord ++ tailWord_3259676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259676).length < 2 ^ (prefixWord ++ tailWord_3259676).sum := by decide
  have hdescent : baseEnd_3259676 < baseStart_3259676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259683 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 1, 4]
def baseStart_3259683 : Nat := 118140960795 + 3259683 * 2 ^ 59
def prefixEnd_3259683 : Nat := 4983230072969 + 3 ^ 40 * 3259683 * 2
def baseEnd_3259683 : Nat := 557928053429958402990499

theorem tailTrace_3259683 : CollatzResearch.WordTrace tailWord_3259683 prefixEnd_3259683 557928053429958402990499 := by
  unfold tailWord_3259683
  simp only [CollatzResearch.WordTrace]
  refine ⟨118890406249732675379599703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79260270833155116919733135 118890406249732675379599703)
  ·
    refine ⟨178335609374599013069399555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118890406249732675379599703 178335609374599013069399555)
    ·
      refine ⟨267503414061898519604099333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178335609374599013069399555 267503414061898519604099333)
      ·
        refine ⟨50156890136605972425768625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267503414061898519604099333 50156890136605972425768625)
        ·
          refine ⟨37617667602454479319326469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50156890136605972425768625 37617667602454479319326469)
          ·
            refine ⟨7053312675460214872373713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37617667602454479319326469 7053312675460214872373713)
            ·
              refine ⟨5289984506595161154280285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7053312675460214872373713 5289984506595161154280285)
              ·
                refine ⟨1983744189973185432855107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289984506595161154280285 1983744189973185432855107)
                ·
                  refine ⟨2975616284959778149282661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983744189973185432855107 2975616284959778149282661)
                  ·
                    refine ⟨557928053429958402990499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975616284959778149282661 557928053429958402990499)
                    ·
                      rfl

theorem cell23_3259683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 4].length) (baseStart_3259683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259683 prefixEnd_3259683 := by exact prefixLift 3259683
  have htrace : WordTrace (prefixWord ++ tailWord_3259683) baseStart_3259683 baseEnd_3259683 := by
    simpa [prefixWord, tailWord_3259683, baseEnd_3259683] using wordTrace_append hprefix tailTrace_3259683
  have hstable : (prefixWord ++ tailWord_3259683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259683).length < 2 ^ (prefixWord ++ tailWord_3259683).sum := by decide
  have hdescent : baseEnd_3259683 < baseStart_3259683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259713 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 6]
def baseStart_3259713 : Nat := 118140960795 + 3259713 * 2 ^ 59
def prefixEnd_3259713 : Nat := 4983230072969 + 3 ^ 40 * 3259713 * 2
def baseEnd_3259713 : Nat := 185977729412167787955151

theorem tailTrace_3259713 : CollatzResearch.WordTrace tailWord_3259713 prefixEnd_3259713 185977729412167787955151 := by
  unfold tailWord_3259713
  simp only [CollatzResearch.WordTrace]
  refine ⟨118891500439623990503191793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79261000293082660335461195 118891500439623990503191793)
  ·
    refine ⟨89168625329717992877393845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118891500439623990503191793 89168625329717992877393845)
    ·
      refine ⟨8359558624661061832255673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89168625329717992877393845 8359558624661061832255673)
      ·
        refine ⟨6269668968495796374191755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8359558624661061832255673 6269668968495796374191755)
        ·
          refine ⟨9404503452743694561287633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269668968495796374191755 9404503452743694561287633)
          ·
            refine ⟨7053377589557770920965725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9404503452743694561287633 7053377589557770920965725)
            ·
              refine ⟨2645016596084164095362147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053377589557770920965725 2645016596084164095362147)
              ·
                refine ⟨3967524894126246143043221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645016596084164095362147 3967524894126246143043221)
                ·
                  refine ⟨185977729412167787955151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3967524894126246143043221 185977729412167787955151)
                  ·
                    rfl

theorem cell23_3259713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_3259713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259713 prefixEnd_3259713 := by exact prefixLift 3259713
  have htrace : WordTrace (prefixWord ++ tailWord_3259713) baseStart_3259713 baseEnd_3259713 := by
    simpa [prefixWord, tailWord_3259713, baseEnd_3259713] using wordTrace_append hprefix tailTrace_3259713
  have hstable : (prefixWord ++ tailWord_3259713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259713).length < 2 ^ (prefixWord ++ tailWord_3259713).sum := by decide
  have hdescent : baseEnd_3259713 < baseStart_3259713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259726 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3259726 : Nat := 118140960795 + 3259726 * 2 ^ 59
def prefixEnd_3259726 : Nat := 4983230072969 + 3 ^ 40 * 3259726 * 2
def baseEnd_3259726 : Nat := 557935413319339513577933

theorem tailTrace_3259726 : CollatzResearch.WordTrace tailWord_3259726 prefixEnd_3259726 557935413319339513577933 := by
  unfold tailWord_3259726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14861496823572111715426879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79261316392384595815610021 14861496823572111715426879)
  ·
    refine ⟨22292245235358167573140319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14861496823572111715426879 22292245235358167573140319)
    ·
      refine ⟨33438367853037251359710479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22292245235358167573140319 33438367853037251359710479)
      ·
        refine ⟨50157551779555877039565719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33438367853037251359710479 50157551779555877039565719)
        ·
          refine ⟨75236327669333815559348579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50157551779555877039565719 75236327669333815559348579)
          ·
            refine ⟨112854491504000723339022869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75236327669333815559348579 112854491504000723339022869)
            ·
              refine ⟨5290054289250033906516697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112854491504000723339022869 5290054289250033906516697)
              ·
                refine ⟨3967540716937525429887523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290054289250033906516697 3967540716937525429887523)
                ·
                  refine ⟨5951311075406288144831285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967540716937525429887523 5951311075406288144831285)
                  ·
                    refine ⟨557935413319339513577933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5951311075406288144831285 557935413319339513577933)
                    ·
                      rfl

theorem cell23_3259726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3259726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259726 prefixEnd_3259726 := by exact prefixLift 3259726
  have htrace : WordTrace (prefixWord ++ tailWord_3259726) baseStart_3259726 baseEnd_3259726 := by
    simpa [prefixWord, tailWord_3259726, baseEnd_3259726] using wordTrace_append hprefix tailTrace_3259726
  have hstable : (prefixWord ++ tailWord_3259726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259726).length < 2 ^ (prefixWord ++ tailWord_3259726).sum := by decide
  have hdescent : baseEnd_3259726 < baseStart_3259726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259756 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_3259756 : Nat := 118140960795 + 3259756 * 2 ^ 59
def prefixEnd_3259756 : Nat := 4983230072969 + 3 ^ 40 * 3259756 * 2
def baseEnd_3259756 : Nat := 557940548125884474452887

theorem tailTrace_3259756 : CollatzResearch.WordTrace tailWord_3259756 prefixEnd_3259756 557940548125884474452887 := by
  unfold tailWord_3259756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59446534389234104423503561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79262045852312139231338081 59446534389234104423503561)
  ·
    refine ⟨44584900791925578317627671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59446534389234104423503561 44584900791925578317627671)
    ·
      refine ⟨66877351187888367476441507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44584900791925578317627671 66877351187888367476441507)
      ·
        refine ⟨100316026781832551214662261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66877351187888367476441507 100316026781832551214662261)
        ·
          refine ⟨9404627510796801676374587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100316026781832551214662261 9404627510796801676374587)
          ·
            refine ⟨14106941266195202514561881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404627510796801676374587 14106941266195202514561881)
            ·
              refine ⟨10580205949646401885921411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14106941266195202514561881 10580205949646401885921411)
              ·
                refine ⟨15870308924469602828882117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10580205949646401885921411 15870308924469602828882117)
                ·
                  refine ⟨2975682923338050530415397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15870308924469602828882117 2975682923338050530415397)
                  ·
                    refine ⟨557940548125884474452887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975682923338050530415397 557940548125884474452887)
                    ·
                      rfl

theorem cell23_3259756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_3259756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259756 prefixEnd_3259756 := by exact prefixLift 3259756
  have htrace : WordTrace (prefixWord ++ tailWord_3259756) baseStart_3259756 baseEnd_3259756 := by
    simpa [prefixWord, tailWord_3259756, baseEnd_3259756] using wordTrace_append hprefix tailTrace_3259756
  have hstable : (prefixWord ++ tailWord_3259756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259756).length < 2 ^ (prefixWord ++ tailWord_3259756).sum := by decide
  have hdescent : baseEnd_3259756 < baseStart_3259756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259757 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3259757 : Nat := 118140960795 + 3259757 * 2 ^ 59
def prefixEnd_3259757 : Nat := 4983230072969 + 3 ^ 40 * 3259757 * 2
def baseEnd_3259757 : Nat := 1673822157858307919446157

theorem tailTrace_3259757 : CollatzResearch.WordTrace tailWord_3259757 prefixEnd_3259757 1673822157858307919446157 := by
  unfold tailWord_3259757
  simp only [CollatzResearch.WordTrace]
  refine ⟨118893105251464586017793525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79262070167643057345195683 118893105251464586017793525)
  ·
    refine ⟨11146228617324804939168143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118893105251464586017793525 11146228617324804939168143)
    ·
      refine ⟨16719342925987207408752215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146228617324804939168143 16719342925987207408752215)
      ·
        refine ⟨25079014388980811113128323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16719342925987207408752215 25079014388980811113128323)
        ·
          refine ⟨37618521583471216669692485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25079014388980811113128323 37618521583471216669692485)
          ·
            refine ⟨7053472796900853125567341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37618521583471216669692485 7053472796900853125567341)
            ·
              refine ⟨2645052298837819922087753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053472796900853125567341 2645052298837819922087753)
              ·
                refine ⟨1983789224128364941565815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645052298837819922087753 1983789224128364941565815)
                ·
                  refine ⟨2975683836192547412348723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983789224128364941565815 2975683836192547412348723)
                  ·
                    refine ⟨4463525754288821118523085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975683836192547412348723 4463525754288821118523085)
                    ·
                      refine ⟨1673822157858307919446157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463525754288821118523085 1673822157858307919446157)
                      ·
                        rfl

theorem cell23_3259757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3259757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259757 prefixEnd_3259757 := by exact prefixLift 3259757
  have htrace : WordTrace (prefixWord ++ tailWord_3259757) baseStart_3259757 baseEnd_3259757 := by
    simpa [prefixWord, tailWord_3259757, baseEnd_3259757] using wordTrace_append hprefix tailTrace_3259757
  have hstable : (prefixWord ++ tailWord_3259757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259757).length < 2 ^ (prefixWord ++ tailWord_3259757).sum := by decide
  have hdescent : baseEnd_3259757 < baseStart_3259757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259783 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3259783 : Nat := 118140960795 + 3259783 * 2 ^ 59
def prefixEnd_3259783 : Nat := 4983230072969 + 3 ^ 40 * 3259783 * 2
def baseEnd_3259783 : Nat := 1673835508355324817721037

theorem tailTrace_3259783 : CollatzResearch.WordTrace tailWord_3259783 prefixEnd_3259783 1673835508355324817721037 := by
  unfold tailWord_3259783
  simp only [CollatzResearch.WordTrace]
  refine ⟨118894053549370392458240003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79262702366246928305493335 118894053549370392458240003)
  ·
    refine ⟨178341080324055588687360005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118894053549370392458240003 178341080324055588687360005)
    ·
      refine ⟨33438952560760422878880001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178341080324055588687360005 33438952560760422878880001)
      ·
        refine ⟨25079214420570317159160001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33438952560760422878880001 25079214420570317159160001)
        ·
          refine ⟨18809410815427737869370001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25079214420570317159160001 18809410815427737869370001)
          ·
            refine ⟨14107058111570803402027501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18809410815427737869370001 14107058111570803402027501)
            ·
              refine ⟨5290146791839051275760313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14107058111570803402027501 5290146791839051275760313)
              ·
                refine ⟨3967610093879288456820235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290146791839051275760313 3967610093879288456820235)
                ·
                  refine ⟨5951415140818932685230353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967610093879288456820235 5951415140818932685230353)
                  ·
                    refine ⟨4463561355614199513922765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951415140818932685230353 4463561355614199513922765)
                    ·
                      refine ⟨1673835508355324817721037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463561355614199513922765 1673835508355324817721037)
                      ·
                        rfl

theorem cell23_3259783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3259783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259783 prefixEnd_3259783 := by exact prefixLift 3259783
  have htrace : WordTrace (prefixWord ++ tailWord_3259783) baseStart_3259783 baseEnd_3259783 := by
    simpa [prefixWord, tailWord_3259783, baseEnd_3259783] using wordTrace_append hprefix tailTrace_3259783
  have hstable : (prefixWord ++ tailWord_3259783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259783).length < 2 ^ (prefixWord ++ tailWord_3259783).sum := by decide
  have hdescent : baseEnd_3259783 < baseStart_3259783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259800 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3259800 : Nat := 118140960795 + 3259800 * 2 ^ 59
def prefixEnd_3259800 : Nat := 4983230072969 + 3 ^ 40 * 3259800 * 2
def baseEnd_3259800 : Nat := 1673844237526451251208459

theorem tailTrace_3259800 : CollatzResearch.WordTrace tailWord_3259800 prefixEnd_3259800 1673844237526451251208459 := by
  unfold tailWord_3259800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59447336795154402180804427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79263115726872536241072569 59447336795154402180804427)
  ·
    refine ⟨89171005192731603271206641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59447336795154402180804427 89171005192731603271206641)
    ·
      refine ⟨66878253894548702453404981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89171005192731603271206641 66878253894548702453404981)
      ·
        refine ⟨6269836302613940855006717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66878253894548702453404981 6269836302613940855006717)
        ·
          refine ⟨2351188613480227820627519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6269836302613940855006717 2351188613480227820627519)
          ·
            refine ⟨3526782920220341730941279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351188613480227820627519 3526782920220341730941279)
            ·
              refine ⟨5290174380330512596411919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526782920220341730941279 5290174380330512596411919)
              ·
                refine ⟨7935261570495768894617879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290174380330512596411919 7935261570495768894617879)
                ·
                  refine ⟨11902892355743653341926819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935261570495768894617879 11902892355743653341926819)
                  ·
                    refine ⟨17854338533615480012890229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11902892355743653341926819 17854338533615480012890229)
                    ·
                      refine ⟨1673844237526451251208459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17854338533615480012890229 1673844237526451251208459)
                      ·
                        rfl

theorem cell23_3259800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3259800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259800 prefixEnd_3259800 := by exact prefixLift 3259800
  have htrace : WordTrace (prefixWord ++ tailWord_3259800) baseStart_3259800 baseEnd_3259800 := by
    simpa [prefixWord, tailWord_3259800, baseEnd_3259800] using wordTrace_append hprefix tailTrace_3259800
  have hstable : (prefixWord ++ tailWord_3259800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259800).length < 2 ^ (prefixWord ++ tailWord_3259800).sum := by decide
  have hdescent : baseEnd_3259800 < baseStart_3259800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_3259839 : Nat := 118140960795 + 3259839 * 2 ^ 59
def prefixEnd_3259839 : Nat := 4983230072969 + 3 ^ 40 * 3259839 * 2
def baseEnd_3259839 : Nat := 1673864263271976598620779

theorem tailTrace_3259839 : CollatzResearch.WordTrace tailWord_3259839 prefixEnd_3259839 1673864263271976598620779 := by
  unfold tailWord_3259839
  simp only [CollatzResearch.WordTrace]
  refine ⟨118896096037167514022278571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79264064024778342681519047 118896096037167514022278571)
  ·
    refine ⟨178344144055751271033417857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118896096037167514022278571 178344144055751271033417857)
    ·
      refine ⟨133758108041813453275063393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178344144055751271033417857 133758108041813453275063393)
      ·
        refine ⟨100318581031360089956297545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133758108041813453275063393 100318581031360089956297545)
        ·
          refine ⟨75238935773520067467223159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100318581031360089956297545 75238935773520067467223159)
          ·
            refine ⟨112858403660280101200834739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75238935773520067467223159 112858403660280101200834739)
            ·
              refine ⟨169287605490420151801252109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112858403660280101200834739 169287605490420151801252109)
              ·
                refine ⟨63482852058907556925469541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169287605490420151801252109 63482852058907556925469541)
                ·
                  refine ⟨11903034761045166923525539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63482852058907556925469541 11903034761045166923525539)
                  ·
                    refine ⟨17854552141567750385288309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11903034761045166923525539 17854552141567750385288309)
                    ·
                      refine ⟨1673864263271976598620779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17854552141567750385288309 1673864263271976598620779)
                      ·
                        rfl

theorem cell23_3259839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_3259839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259839 prefixEnd_3259839 := by exact prefixLift 3259839
  have htrace : WordTrace (prefixWord ++ tailWord_3259839) baseStart_3259839 baseEnd_3259839 := by
    simpa [prefixWord, tailWord_3259839, baseEnd_3259839] using wordTrace_append hprefix tailTrace_3259839
  have hstable : (prefixWord ++ tailWord_3259839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259839).length < 2 ^ (prefixWord ++ tailWord_3259839).sum := by decide
  have hdescent : baseEnd_3259839 < baseStart_3259839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259849 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3259849 : Nat := 118140960795 + 3259849 * 2 ^ 59
def prefixEnd_3259849 : Nat := 4983230072969 + 3 ^ 40 * 3259849 * 2
def baseEnd_3259849 : Nat := 1673869398078521559495733

theorem tailTrace_3259849 : CollatzResearch.WordTrace tailWord_3259849 prefixEnd_3259849 1673869398078521559495733 := by
  unfold tailWord_3259849
  simp only [CollatzResearch.WordTrace]
  refine ⟨118896460767131285730142601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79264307178087523820095067 118896460767131285730142601)
  ·
    refine ⟨89172345575348464297606951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118896460767131285730142601 89172345575348464297606951)
    ·
      refine ⟨133758518363022696446410427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89172345575348464297606951 133758518363022696446410427)
      ·
        refine ⟨200637777544534044669615641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133758518363022696446410427 200637777544534044669615641)
        ·
          refine ⟨150478333158400533502211731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200637777544534044669615641 150478333158400533502211731)
          ·
            refine ⟨225717499737600800253317597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150478333158400533502211731 225717499737600800253317597)
            ·
              refine ⟨84644062401600300094994099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225717499737600800253317597 84644062401600300094994099)
              ·
                refine ⟨126966093602400450142491149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84644062401600300094994099 126966093602400450142491149)
                ·
                  refine ⟨47612285100900168803434181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126966093602400450142491149 47612285100900168803434181)
                  ·
                    refine ⟨8927303456418781650643909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47612285100900168803434181 8927303456418781650643909)
                    ·
                      refine ⟨1673869398078521559495733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8927303456418781650643909 1673869398078521559495733)
                      ·
                        rfl

theorem cell23_3259849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3259849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259849 prefixEnd_3259849 := by exact prefixLift 3259849
  have htrace : WordTrace (prefixWord ++ tailWord_3259849) baseStart_3259849 baseEnd_3259849 := by
    simpa [prefixWord, tailWord_3259849, baseEnd_3259849] using wordTrace_append hprefix tailTrace_3259849
  have hstable : (prefixWord ++ tailWord_3259849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259849).length < 2 ^ (prefixWord ++ tailWord_3259849).sum := by decide
  have hdescent : baseEnd_3259849 < baseStart_3259849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259866 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3259866 : Nat := 118140960795 + 3259866 * 2 ^ 59
def prefixEnd_3259866 : Nat := 4983230072969 + 3 ^ 40 * 3259866 * 2
def baseEnd_3259866 : Nat := 1673878127249647992983155

theorem tailTrace_3259866 : CollatzResearch.WordTrace tailWord_3259866 prefixEnd_3259866 1673878127249647992983155 := by
  unfold tailWord_3259866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29724270202017424408377863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79264720538713131755674301 29724270202017424408377863)
  ·
    refine ⟨44586405303026136612566795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29724270202017424408377863 44586405303026136612566795)
    ·
      refine ⟨66879607954539204918850193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44586405303026136612566795 66879607954539204918850193)
      ·
        refine ⟨50159705965904403689137645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66879607954539204918850193 50159705965904403689137645)
        ·
          refine ⟨18809889737214151383426617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50159705965904403689137645 18809889737214151383426617)
          ·
            refine ⟨14107417302910613537569963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18809889737214151383426617 14107417302910613537569963)
            ·
              refine ⟨21161125954365920306354945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14107417302910613537569963 21161125954365920306354945)
              ·
                refine ⟨15870844465774440229766209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21161125954365920306354945 15870844465774440229766209)
                ·
                  refine ⟨11903133349330830172324657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15870844465774440229766209 11903133349330830172324657)
                  ·
                    refine ⟨8927350011998122629243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11903133349330830172324657 8927350011998122629243493)
                    ·
                      refine ⟨1673878127249647992983155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8927350011998122629243493 1673878127249647992983155)
                      ·
                        rfl

theorem cell23_3259866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3259866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259866 prefixEnd_3259866 := by exact prefixLift 3259866
  have htrace : WordTrace (prefixWord ++ tailWord_3259866) baseStart_3259866 baseEnd_3259866 := by
    simpa [prefixWord, tailWord_3259866, baseEnd_3259866] using wordTrace_append hprefix tailTrace_3259866
  have hstable : (prefixWord ++ tailWord_3259866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259866).length < 2 ^ (prefixWord ++ tailWord_3259866).sum := by decide
  have hdescent : baseEnd_3259866 < baseStart_3259866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259893 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 7]
def baseStart_3259893 : Nat := 118140960795 + 3259893 * 2 ^ 59
def prefixEnd_3259893 : Nat := 4983230072969 + 3 ^ 40 * 3259893 * 2
def baseEnd_3259893 : Nat := 185987999025257709705059

theorem tailTrace_3259893 : CollatzResearch.WordTrace tailWord_3259893 prefixEnd_3259893 185987999025257709705059 := by
  unfold tailWord_3259893
  simp only [CollatzResearch.WordTrace]
  refine ⟨118898065578971881244744333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79265377052647920829829555 118898065578971881244744333)
  ·
    refine ⟨44586774592114455466779125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118898065578971881244744333 44586774592114455466779125)
    ·
      refine ⟨4180010118010730200010543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44586774592114455466779125 4180010118010730200010543)
      ·
        refine ⟨6270015177016095300015815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180010118010730200010543 6270015177016095300015815)
        ·
          refine ⟨9405022765524142950023723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270015177016095300015815 9405022765524142950023723)
          ·
            refine ⟨14107534148286214425035585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405022765524142950023723 14107534148286214425035585)
            ·
              refine ⟨10580650611214660818776689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14107534148286214425035585 10580650611214660818776689)
              ·
                refine ⟨7935487958410995614082517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580650611214660818776689 7935487958410995614082517)
                ·
                  refine ⟨185987999025257709705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7935487958410995614082517 185987999025257709705059)
                  ·
                    rfl

theorem cell23_3259893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_3259893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259893 prefixEnd_3259893 := by exact prefixLift 3259893
  have htrace : WordTrace (prefixWord ++ tailWord_3259893) baseStart_3259893 baseEnd_3259893 := by
    simpa [prefixWord, tailWord_3259893, baseEnd_3259893] using wordTrace_append hprefix tailTrace_3259893
  have hstable : (prefixWord ++ tailWord_3259893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259893).length < 2 ^ (prefixWord ++ tailWord_3259893).sum := by decide
  have hdescent : baseEnd_3259893 < baseStart_3259893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259899 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_3259899 : Nat := 118140960795 + 3259899 * 2 ^ 59
def prefixEnd_3259899 : Nat := 4983230072969 + 3 ^ 40 * 3259899 * 2
def baseEnd_3259899 : Nat := 1673895072111246363870503

theorem tailTrace_3259899 : CollatzResearch.WordTrace tailWord_3259899 prefixEnd_3259899 1673895072111246363870503 := by
  unfold tailWord_3259899
  simp only [CollatzResearch.WordTrace]
  refine ⟨118898284416950144269462751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79265522944633429512975167 118898284416950144269462751)
  ·
    refine ⟨178347426625425216404194127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118898284416950144269462751 178347426625425216404194127)
    ·
      refine ⟨267521139938137824606291191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178347426625425216404194127 267521139938137824606291191)
      ·
        refine ⟨401281709907206736909436787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267521139938137824606291191 401281709907206736909436787)
        ·
          refine ⟨601922564860810105364155181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401281709907206736909436787 601922564860810105364155181)
          ·
            refine ⟨225720961822803789511558193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601922564860810105364155181 225720961822803789511558193)
            ·
              refine ⟨169290721367102842133668645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225720961822803789511558193 169290721367102842133668645)
              ·
                refine ⟨31742010256331782900062871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169290721367102842133668645 31742010256331782900062871)
                ·
                  refine ⟨47613015384497674350094307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31742010256331782900062871 47613015384497674350094307)
                  ·
                    refine ⟨71419523076746511525141461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47613015384497674350094307 71419523076746511525141461)
                    ·
                      refine ⟨1673895072111246363870503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71419523076746511525141461 1673895072111246363870503)
                      ·
                        rfl

theorem cell23_3259899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_3259899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259899 prefixEnd_3259899 := by exact prefixLift 3259899
  have htrace : WordTrace (prefixWord ++ tailWord_3259899) baseStart_3259899 baseEnd_3259899 := by
    simpa [prefixWord, tailWord_3259899, baseEnd_3259899] using wordTrace_append hprefix tailTrace_3259899
  have hstable : (prefixWord ++ tailWord_3259899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259899).length < 2 ^ (prefixWord ++ tailWord_3259899).sum := by decide
  have hdescent : baseEnd_3259899 < baseStart_3259899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259919 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 8]
def baseStart_3259919 : Nat := 118140960795 + 3259919 * 2 ^ 59
def prefixEnd_3259919 : Nat := 4983230072969 + 3 ^ 40 * 3259919 * 2
def baseEnd_3259919 : Nat := 557968447241445428540137

theorem tailTrace_3259919 : CollatzResearch.WordTrace tailWord_3259919 prefixEnd_3259919 557968447241445428540137 := by
  unfold tailWord_3259919
  simp only [CollatzResearch.WordTrace]
  refine ⟨118899013876877687685190811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79266009251251791790127207 118899013876877687685190811)
  ·
    refine ⟨178348520815316531527786217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118899013876877687685190811 178348520815316531527786217)
    ·
      refine ⟨133761390611487398645839663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178348520815316531527786217 133761390611487398645839663)
      ·
        refine ⟨200642085917231097968759495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133761390611487398645839663 200642085917231097968759495)
        ·
          refine ⟨300963128875846646953139243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200642085917231097968759495 300963128875846646953139243)
          ·
            refine ⟨451444693313769970429708865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300963128875846646953139243 451444693313769970429708865)
            ·
              refine ⟨338583519985327477822281649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451444693313769970429708865 338583519985327477822281649)
              ·
                refine ⟨253937639988995608366711237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338583519985327477822281649 253937639988995608366711237)
                ·
                  refine ⟨47613307497936676568758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253937639988995608366711237 47613307497936676568758357)
                  ·
                    refine ⟨557968447241445428540137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47613307497936676568758357 557968447241445428540137)
                    ·
                      rfl

theorem cell23_3259919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_3259919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259919 prefixEnd_3259919 := by exact prefixLift 3259919
  have htrace : WordTrace (prefixWord ++ tailWord_3259919) baseStart_3259919 baseEnd_3259919 := by
    simpa [prefixWord, tailWord_3259919, baseEnd_3259919] using wordTrace_append hprefix tailTrace_3259919
  have hstable : (prefixWord ++ tailWord_3259919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259919).length < 2 ^ (prefixWord ++ tailWord_3259919).sum := by decide
  have hdescent : baseEnd_3259919 < baseStart_3259919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3259993 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_3259993 : Nat := 118140960795 + 3259993 * 2 ^ 59
def prefixEnd_3259993 : Nat := 4983230072969 + 3 ^ 40 * 3259993 * 2
def baseEnd_3259993 : Nat := 1673943339292768996095071

theorem tailTrace_3259993 : CollatzResearch.WordTrace tailWord_3259993 prefixEnd_3259993 1673943339292768996095071 := by
  unfold tailWord_3259993
  simp only [CollatzResearch.WordTrace]
  refine ⟨118901712878609598323384633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79267808585739732215589755 118901712878609598323384633)
  ·
    refine ⟨89176284658957198742538475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118901712878609598323384633 89176284658957198742538475)
    ·
      refine ⟨133764426988435798113807713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89176284658957198742538475 133764426988435798113807713)
      ·
        refine ⟨100323320241326848585355785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133764426988435798113807713 100323320241326848585355785)
        ·
          refine ⟨75242490180995136439016839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100323320241326848585355785 75242490180995136439016839)
          ·
            refine ⟨112863735271492704658525259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75242490180995136439016839 112863735271492704658525259)
            ·
              refine ⟨169295602907239056987787889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112863735271492704658525259 169295602907239056987787889)
              ·
                refine ⟨126971702180429292740840917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169295602907239056987787889 126971702180429292740840917)
                ·
                  refine ⟨2975899269853811548613459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126971702180429292740840917 2975899269853811548613459)
                  ·
                    refine ⟨4463848904780717322920189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975899269853811548613459 4463848904780717322920189)
                    ·
                      refine ⟨1673943339292768996095071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463848904780717322920189 1673943339292768996095071)
                      ·
                        rfl

theorem cell23_3259993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_3259993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3259993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3259993 prefixEnd_3259993 := by exact prefixLift 3259993
  have htrace : WordTrace (prefixWord ++ tailWord_3259993) baseStart_3259993 baseEnd_3259993 := by
    simpa [prefixWord, tailWord_3259993, baseEnd_3259993] using wordTrace_append hprefix tailTrace_3259993
  have hstable : (prefixWord ++ tailWord_3259993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3259993).length < 2 ^ (prefixWord ++ tailWord_3259993).sum := by decide
  have hdescent : baseEnd_3259993 < baseStart_3259993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3259993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260010 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3260010 : Nat := 118140960795 + 3260010 * 2 ^ 59
def prefixEnd_3260010 : Nat := 4983230072969 + 3 ^ 40 * 3260010 * 2
def baseEnd_3260010 : Nat := 1673952068463895429582493

theorem tailTrace_3260010 : CollatzResearch.WordTrace tailWord_3260010 prefixEnd_3260010 1673952068463895429582493 := by
  unfold tailWord_3260010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725583229887002556688371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79268221946365340151168989 29725583229887002556688371)
  ·
    refine ⟨44588374844830503835032557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725583229887002556688371 44588374844830503835032557)
    ·
      refine ⟨16720640566811438938137209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44588374844830503835032557 16720640566811438938137209)
      ·
        refine ⟨12540480425108579203602907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16720640566811438938137209 12540480425108579203602907)
        ·
          refine ⟨18810720637662868805404361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540480425108579203602907 18810720637662868805404361)
          ·
            refine ⟨14108040478247151604053271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18810720637662868805404361 14108040478247151604053271)
            ·
              refine ⟨21162060717370727406079907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108040478247151604053271 21162060717370727406079907)
              ·
                refine ⟨31743091076056091109119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162060717370727406079907 31743091076056091109119861)
                ·
                  refine ⟨2975914788380258541479987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31743091076056091109119861 2975914788380258541479987)
                  ·
                    refine ⟨4463872182570387812219981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975914788380258541479987 4463872182570387812219981)
                    ·
                      refine ⟨1673952068463895429582493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463872182570387812219981 1673952068463895429582493)
                      ·
                        rfl

theorem cell23_3260010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3260010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260010 prefixEnd_3260010 := by exact prefixLift 3260010
  have htrace : WordTrace (prefixWord ++ tailWord_3260010) baseStart_3260010 baseEnd_3260010 := by
    simpa [prefixWord, tailWord_3260010, baseEnd_3260010] using wordTrace_append hprefix tailTrace_3260010
  have hstable : (prefixWord ++ tailWord_3260010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260010).length < 2 ^ (prefixWord ++ tailWord_3260010).sum := by decide
  have hdescent : baseEnd_3260010 < baseStart_3260010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260014 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_3260014 : Nat := 118140960795 + 3260014 * 2 ^ 59
def prefixEnd_3260014 : Nat := 4983230072969 + 3 ^ 40 * 3260014 * 2
def baseEnd_3260014 : Nat := 1673954122386513413932475

theorem tailTrace_3260014 : CollatzResearch.WordTrace tailWord_3260014 prefixEnd_3260014 1673954122386513413932475 := by
  unfold tailWord_3260014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14862809851441689863737387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79268319207689012606599397 14862809851441689863737387)
  ·
    refine ⟨22294214777162534795606081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14862809851441689863737387 22294214777162534795606081)
    ·
      refine ⟨16720661082871901096704561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22294214777162534795606081 16720661082871901096704561)
      ·
        refine ⟨12540495812153925822528421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16720661082871901096704561 12540495812153925822528421)
        ·
          refine ⟨2351342964778861091724079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12540495812153925822528421 2351342964778861091724079)
          ·
            refine ⟨3527014447168291637586119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351342964778861091724079 3527014447168291637586119)
            ·
              refine ⟨5290521670752437456379179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527014447168291637586119 5290521670752437456379179)
              ·
                refine ⟨7935782506128656184568769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290521670752437456379179 7935782506128656184568769)
                ·
                  refine ⟨5951836879596492138426577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7935782506128656184568769 5951836879596492138426577)
                  ·
                    refine ⟨4463877659697369103819933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951836879596492138426577 4463877659697369103819933)
                    ·
                      refine ⟨1673954122386513413932475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463877659697369103819933 1673954122386513413932475)
                      ·
                        rfl

theorem cell23_3260014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_3260014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260014 prefixEnd_3260014 := by exact prefixLift 3260014
  have htrace : WordTrace (prefixWord ++ tailWord_3260014) baseStart_3260014 baseEnd_3260014 := by
    simpa [prefixWord, tailWord_3260014, baseEnd_3260014] using wordTrace_append hprefix tailTrace_3260014
  have hstable : (prefixWord ++ tailWord_3260014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260014).length < 2 ^ (prefixWord ++ tailWord_3260014).sum := by decide
  have hdescent : baseEnd_3260014 < baseStart_3260014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3260026 : Nat := 118140960795 + 3260026 * 2 ^ 59
def prefixEnd_3260026 : Nat := 4983230072969 + 3 ^ 40 * 3260026 * 2
def baseEnd_3260026 : Nat := 557986761384789122327473

theorem tailTrace_3260026 : CollatzResearch.WordTrace tailWord_3260026 prefixEnd_3260026 557986761384789122327473 := by
  unfold tailWord_3260026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725729121872511239833983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79268610991660029972890621 29725729121872511239833983)
  ·
    refine ⟨44588593682808766859750975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725729121872511239833983 44588593682808766859750975)
    ·
      refine ⟨66882890524213150289626463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44588593682808766859750975 66882890524213150289626463)
      ·
        refine ⟨100324335786319725434439695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66882890524213150289626463 100324335786319725434439695)
        ·
          refine ⟨150486503679479588151659543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100324335786319725434439695 150486503679479588151659543)
          ·
            refine ⟨225729755519219382227489315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150486503679479588151659543 225729755519219382227489315)
            ·
              refine ⟨338594633278829073341233973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225729755519219382227489315 338594633278829073341233973)
              ·
                refine ⟨31743246869890225625740685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338594633278829073341233973 31743246869890225625740685)
                ·
                  refine ⟨11903717576208834609652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31743246869890225625740685 11903717576208834609652757)
                  ·
                    refine ⟨557986761384789122327473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11903717576208834609652757 557986761384789122327473)
                    ·
                      rfl

theorem cell23_3260026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3260026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260026 prefixEnd_3260026 := by exact prefixLift 3260026
  have htrace : WordTrace (prefixWord ++ tailWord_3260026) baseStart_3260026 baseEnd_3260026 := by
    simpa [prefixWord, tailWord_3260026, baseEnd_3260026] using wordTrace_append hprefix tailTrace_3260026
  have hstable : (prefixWord ++ tailWord_3260026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260026).length < 2 ^ (prefixWord ++ tailWord_3260026).sum := by decide
  have hdescent : baseEnd_3260026 < baseStart_3260026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260027 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 1, 1, 3]
def baseStart_3260027 : Nat := 118140960795 + 3260027 * 2 ^ 59
def prefixEnd_3260027 : Nat := 4983230072969 + 3 ^ 40 * 3260027 * 2
def baseEnd_3260027 : Nat := 1673960797635021863069915

theorem tailTrace_3260027 : CollatzResearch.WordTrace tailWord_3260027 prefixEnd_3260027 1673960797635021863069915 := by
  unfold tailWord_3260027
  simp only [CollatzResearch.WordTrace]
  refine ⟨118902952960486422130122335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79268635306990948086748223 118902952960486422130122335)
  ·
    refine ⟨178354429440729633195183503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118902952960486422130122335 178354429440729633195183503)
    ·
      refine ⟨267531644161094449792775255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178354429440729633195183503 267531644161094449792775255)
      ·
        refine ⟨401297466241641674689162883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267531644161094449792775255 401297466241641674689162883)
        ·
          refine ⟨601946199362462512033744325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401297466241641674689162883 601946199362462512033744325)
          ·
            refine ⟨112864912380461721006327061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 601946199362462512033744325 112864912380461721006327061)
            ·
              refine ⟨5290542767834143172171581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112864912380461721006327061 5290542767834143172171581)
              ·
                refine ⟨1983953537937803689564343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5290542767834143172171581 1983953537937803689564343)
                ·
                  refine ⟨2975930306906705534346515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983953537937803689564343 2975930306906705534346515)
                  ·
                    refine ⟨4463895460360058301519773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975930306906705534346515 4463895460360058301519773)
                    ·
                      refine ⟨1673960797635021863069915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463895460360058301519773 1673960797635021863069915)
                      ·
                        rfl

theorem cell23_3260027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 1, 3].length) (baseStart_3260027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260027 prefixEnd_3260027 := by exact prefixLift 3260027
  have htrace : WordTrace (prefixWord ++ tailWord_3260027) baseStart_3260027 baseEnd_3260027 := by
    simpa [prefixWord, tailWord_3260027, baseEnd_3260027] using wordTrace_append hprefix tailTrace_3260027
  have hstable : (prefixWord ++ tailWord_3260027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260027).length < 2 ^ (prefixWord ++ tailWord_3260027).sum := by decide
  have hdescent : baseEnd_3260027 < baseStart_3260027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260043 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 4, 4]
def baseStart_3260043 : Nat := 118140960795 + 3260043 * 2 ^ 59
def prefixEnd_3260043 : Nat := 4983230072969 + 3 ^ 40 * 3260043 * 2
def baseEnd_3260043 : Nat := 557989671108497933489947

theorem tailTrace_3260043 : CollatzResearch.WordTrace tailWord_3260043 prefixEnd_3260043 557989671108497933489947 := by
  unfold tailWord_3260043
  simp only [CollatzResearch.WordTrace]
  refine ⟨118903536528428456862704783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79269024352285637908469855 118903536528428456862704783)
  ·
    refine ⟨178355304792642685294057175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118903536528428456862704783 178355304792642685294057175)
    ·
      refine ⟨267532957188964027941085763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178355304792642685294057175 267532957188964027941085763)
      ·
        refine ⟨401299435783446041911628645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267532957188964027941085763 401299435783446041911628645)
        ·
          refine ⟨75243644209396132858430371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401299435783446041911628645 75243644209396132858430371)
          ·
            refine ⟨112865466314094199287645557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75243644209396132858430371 112865466314094199287645557)
            ·
              refine ⟨10581137466946331183216771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112865466314094199287645557 10581137466946331183216771)
              ·
                refine ⟨15871706200419496774825157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581137466946331183216771 15871706200419496774825157)
                ·
                  refine ⟨2975944912578655645279717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15871706200419496774825157 2975944912578655645279717)
                  ·
                    refine ⟨557989671108497933489947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975944912578655645279717 557989671108497933489947)
                    ·
                      rfl

theorem cell23_3260043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 4].length) (baseStart_3260043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260043 prefixEnd_3260043 := by exact prefixLift 3260043
  have htrace : WordTrace (prefixWord ++ tailWord_3260043) baseStart_3260043 baseEnd_3260043 := by
    simpa [prefixWord, tailWord_3260043, baseEnd_3260043] using wordTrace_append hprefix tailTrace_3260043
  have hstable : (prefixWord ++ tailWord_3260043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260043).length < 2 ^ (prefixWord ++ tailWord_3260043).sum := by decide
  have hdescent : baseEnd_3260043 < baseStart_3260043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260053 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_3260053 : Nat := 118140960795 + 3260053 * 2 ^ 59
def prefixEnd_3260053 : Nat := 4983230072969 + 3 ^ 40 * 3260053 * 2
def baseEnd_3260053 : Nat := 1673974148132038761344795

theorem tailTrace_3260053 : CollatzResearch.WordTrace tailWord_3260053 prefixEnd_3260053 1673974148132038761344795 := by
  unfold tailWord_3260053
  simp only [CollatzResearch.WordTrace]
  refine ⟨118903901258392228570568813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79269267505594819047045875 118903901258392228570568813)
  ·
    refine ⟨44588962971897085713963305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118903901258392228570568813 44588962971897085713963305)
    ·
      refine ⟨33441722228922814285472479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44588962971897085713963305 33441722228922814285472479)
      ·
        refine ⟨50162583343384221428208719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33441722228922814285472479 50162583343384221428208719)
        ·
          refine ⟨75243875015076332142313079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50162583343384221428208719 75243875015076332142313079)
          ·
            refine ⟨112865812522614498213469619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75243875015076332142313079 112865812522614498213469619)
            ·
              refine ⟨169298718783921747320204429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112865812522614498213469619 169298718783921747320204429)
              ·
                refine ⟨63487019543970655245076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169298718783921747320204429 63487019543970655245076661)
                ·
                  refine ⟨5951908082247248929225937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63487019543970655245076661 5951908082247248929225937)
                  ·
                    refine ⟨4463931061685436696919453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951908082247248929225937 4463931061685436696919453)
                    ·
                      refine ⟨1673974148132038761344795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463931061685436696919453 1673974148132038761344795)
                      ·
                        rfl

theorem cell23_3260053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_3260053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260053 prefixEnd_3260053 := by exact prefixLift 3260053
  have htrace : WordTrace (prefixWord ++ tailWord_3260053) baseStart_3260053 baseEnd_3260053 := by
    simpa [prefixWord, tailWord_3260053, baseEnd_3260053] using wordTrace_append hprefix tailTrace_3260053
  have hstable : (prefixWord ++ tailWord_3260053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260053).length < 2 ^ (prefixWord ++ tailWord_3260053).sum := by decide
  have hdescent : baseEnd_3260053 < baseStart_3260053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260076 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3260076 : Nat := 118140960795 + 3260076 * 2 ^ 59
def prefixEnd_3260076 : Nat := 4983230072969 + 3 ^ 40 * 3260076 * 2
def baseEnd_3260076 : Nat := 1673985958187092171357189

theorem tailTrace_3260076 : CollatzResearch.WordTrace tailWord_3260076 prefixEnd_3260076 1673985958187092171357189 := by
  unfold tailWord_3260076
  simp only [CollatzResearch.WordTrace]
  refine ⟨59452370068654451749328041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79269826758205935665770721 59452370068654451749328041)
  ·
    refine ⟨44589277551490838811996031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59452370068654451749328041 44589277551490838811996031)
    ·
      refine ⟨66883916327236258217994047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44589277551490838811996031 66883916327236258217994047)
      ·
        refine ⟨100325874490854387326991071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66883916327236258217994047 100325874490854387326991071)
        ·
          refine ⟨150488811736281580990486607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100325874490854387326991071 150488811736281580990486607)
          ·
            refine ⟨225733217604422371485729911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150488811736281580990486607 225733217604422371485729911)
            ·
              refine ⟨338599826406633557228594867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225733217604422371485729911 338599826406633557228594867)
              ·
                refine ⟨507899739609950335842892301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338599826406633557228594867 507899739609950335842892301)
                ·
                  refine ⟨190462402353731375941084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507899739609950335842892301 190462402353731375941084613)
                  ·
                    refine ⟨35711700441324632988953365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190462402353731375941084613 35711700441324632988953365)
                    ·
                      refine ⟨1673985958187092171357189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35711700441324632988953365 1673985958187092171357189)
                      ·
                        rfl

theorem cell23_3260076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3260076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260076 prefixEnd_3260076 := by exact prefixLift 3260076
  have htrace : WordTrace (prefixWord ++ tailWord_3260076) baseStart_3260076 baseEnd_3260076 := by
    simpa [prefixWord, tailWord_3260076, baseEnd_3260076] using wordTrace_append hprefix tailTrace_3260076
  have hstable : (prefixWord ++ tailWord_3260076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260076).length < 2 ^ (prefixWord ++ tailWord_3260076).sum := by decide
  have hdescent : baseEnd_3260076 < baseStart_3260076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260078 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3260078 : Nat := 118140960795 + 3260078 * 2 ^ 59
def prefixEnd_3260078 : Nat := 4983230072969 + 3 ^ 40 * 3260078 * 2
def baseEnd_3260078 : Nat := 1673986985148401163532181

theorem tailTrace_3260078 : CollatzResearch.WordTrace tailWord_3260078 prefixEnd_3260078 1673986985148401163532181 := by
  unfold tailWord_3260078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863101635412707230028611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79269875388867771893485925 14863101635412707230028611)
  ·
    refine ⟨22294652453119060845042917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863101635412707230028611 22294652453119060845042917)
    ·
      refine ⟨4180247334959823908445547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22294652453119060845042917 4180247334959823908445547)
      ·
        refine ⟨6270371002439735862668321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180247334959823908445547 6270371002439735862668321)
        ·
          refine ⟨4702778251829801897001241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270371002439735862668321 4702778251829801897001241)
          ·
            refine ⟨3527083688872351422750931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702778251829801897001241 3527083688872351422750931)
            ·
              refine ⟨5290625533308527134126397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527083688872351422750931 5290625533308527134126397)
              ·
                refine ⟨1983984574990697675297399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5290625533308527134126397 1983984574990697675297399)
                ·
                  refine ⟨2975976862486046512946099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983984574990697675297399 2975976862486046512946099)
                  ·
                    refine ⟨4463965293729069769419149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975976862486046512946099 4463965293729069769419149)
                    ·
                      refine ⟨1673986985148401163532181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463965293729069769419149 1673986985148401163532181)
                      ·
                        rfl

theorem cell23_3260078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3260078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260078 prefixEnd_3260078 := by exact prefixLift 3260078
  have htrace : WordTrace (prefixWord ++ tailWord_3260078) baseStart_3260078 baseEnd_3260078 := by
    simpa [prefixWord, tailWord_3260078, baseEnd_3260078] using wordTrace_append hprefix tailTrace_3260078
  have hstable : (prefixWord ++ tailWord_3260078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260078).length < 2 ^ (prefixWord ++ tailWord_3260078).sum := by decide
  have hdescent : baseEnd_3260078 < baseStart_3260078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260083 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3]
def baseStart_3260083 : Nat := 118140960795 + 3260083 * 2 ^ 59
def prefixEnd_3260083 : Nat := 4983230072969 + 3 ^ 40 * 3260083 * 2
def baseEnd_3260083 : Nat := 1673989552551673643969657

theorem tailTrace_3260083 : CollatzResearch.WordTrace tailWord_3260083 prefixEnd_3260083 1673989552551673643969657 := by
  unfold tailWord_3260083
  simp only [CollatzResearch.WordTrace]
  refine ⟨118904995448283543694160903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79269996965522362462773935 118904995448283543694160903)
  ·
    refine ⟨178357493172425315541241355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118904995448283543694160903 178357493172425315541241355)
    ·
      refine ⟨267536239758637973311862033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178357493172425315541241355 267536239758637973311862033)
      ·
        refine ⟨200652179818978479983896525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267536239758637973311862033 200652179818978479983896525)
        ·
          refine ⟨75244567432116929993961197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200652179818978479983896525 75244567432116929993961197)
          ·
            refine ⟨28216712787043848747735449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75244567432116929993961197 28216712787043848747735449)
            ·
              refine ⟨21162534590282886560801587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28216712787043848747735449 21162534590282886560801587)
              ·
                refine ⟨31743801885424329841202381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162534590282886560801587 31743801885424329841202381)
                ·
                  refine ⟨11903925707034123690450893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31743801885424329841202381 11903925707034123690450893)
                  ·
                    refine ⟨4463972140137796383919085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903925707034123690450893 4463972140137796383919085)
                    ·
                      refine ⟨1673989552551673643969657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4463972140137796383919085 1673989552551673643969657)
                      ·
                        rfl

theorem cell23_3260083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_3260083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260083 prefixEnd_3260083 := by exact prefixLift 3260083
  have htrace : WordTrace (prefixWord ++ tailWord_3260083) baseStart_3260083 baseEnd_3260083 := by
    simpa [prefixWord, tailWord_3260083, baseEnd_3260083] using wordTrace_append hprefix tailTrace_3260083
  have hstable : (prefixWord ++ tailWord_3260083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260083).length < 2 ^ (prefixWord ++ tailWord_3260083).sum := by decide
  have hdescent : baseEnd_3260083 < baseStart_3260083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260118 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3260118 : Nat := 118140960795 + 3260118 * 2 ^ 59
def prefixEnd_3260118 : Nat := 4983230072969 + 3 ^ 40 * 3260118 * 2
def baseEnd_3260118 : Nat := 1674007524374581007031997

theorem tailTrace_3260118 : CollatzResearch.WordTrace tailWord_3260118 prefixEnd_3260118 1674007524374581007031997 := by
  unfold tailWord_3260118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431642000197296541980313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79270848002104496447790005 7431642000197296541980313)
  ·
    refine ⟨5573731500147972406485235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7431642000197296541980313 5573731500147972406485235)
    ·
      refine ⟨8360597250221958609727853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573731500147972406485235 8360597250221958609727853)
      ·
        refine ⟨3135223968833234478647945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8360597250221958609727853 3135223968833234478647945)
        ·
          refine ⟨2351417976624925858985959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3135223968833234478647945 2351417976624925858985959)
          ·
            refine ⟨3527126964937388788478939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351417976624925858985959 3527126964937388788478939)
            ·
              refine ⟨5290690447406083182718409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527126964937388788478939 5290690447406083182718409)
              ·
                refine ⟨3968017835554562387038807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290690447406083182718409 3968017835554562387038807)
                ·
                  refine ⟨5952026753331843580558211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968017835554562387038807 5952026753331843580558211)
                  ·
                    refine ⟨8928040129997765370837317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952026753331843580558211 8928040129997765370837317)
                    ·
                      refine ⟨1674007524374581007031997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8928040129997765370837317 1674007524374581007031997)
                      ·
                        rfl

theorem cell23_3260118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3260118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260118 prefixEnd_3260118 := by exact prefixLift 3260118
  have htrace : WordTrace (prefixWord ++ tailWord_3260118) baseStart_3260118 baseEnd_3260118 := by
    simpa [prefixWord, tailWord_3260118, baseEnd_3260118] using wordTrace_append hprefix tailTrace_3260118
  have hstable : (prefixWord ++ tailWord_3260118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260118).length < 2 ^ (prefixWord ++ tailWord_3260118).sum := by decide
  have hdescent : baseEnd_3260118 < baseStart_3260118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260140 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_3260140 : Nat := 118140960795 + 3260140 * 2 ^ 59
def prefixEnd_3260140 : Nat := 4983230072969 + 3 ^ 40 * 3260140 * 2
def baseEnd_3260140 : Nat := 1674018820948979920956895

theorem tailTrace_3260140 : CollatzResearch.WordTrace tailWord_3260140 prefixEnd_3260140 1674018820948979920956895 := by
  unfold tailWord_3260140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59453537204538521214492937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79271382939384694952657249 59453537204538521214492937)
  ·
    refine ⟨44590152903403890910869703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59453537204538521214492937 44590152903403890910869703)
    ·
      refine ⟨66885229355105836366304555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44590152903403890910869703 66885229355105836366304555)
      ·
        refine ⟨100327844032658754549456833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66885229355105836366304555 100327844032658754549456833)
        ·
          refine ⟨75245883024494065912092625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100327844032658754549456833 75245883024494065912092625)
          ·
            refine ⟨56434412268370549434069469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75245883024494065912092625 56434412268370549434069469)
            ·
              refine ⟨21162904600638956037776051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56434412268370549434069469 21162904600638956037776051)
              ·
                refine ⟨31744356900958434056664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162904600638956037776051 31744356900958434056664077)
                ·
                  refine ⟨11904133837859412771249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31744356900958434056664077 11904133837859412771249029)
                  ·
                    refine ⟨2232025094598639894609193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11904133837859412771249029 2232025094598639894609193)
                    ·
                      refine ⟨1674018820948979920956895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232025094598639894609193 1674018820948979920956895)
                      ·
                        rfl

theorem cell23_3260140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_3260140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260140 prefixEnd_3260140 := by exact prefixLift 3260140
  have htrace : WordTrace (prefixWord ++ tailWord_3260140) baseStart_3260140 baseEnd_3260140 := by
    simpa [prefixWord, tailWord_3260140, baseEnd_3260140] using wordTrace_append hprefix tailTrace_3260140
  have hstable : (prefixWord ++ tailWord_3260140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260140).length < 2 ^ (prefixWord ++ tailWord_3260140).sum := by decide
  have hdescent : baseEnd_3260140 < baseStart_3260140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260143 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_3260143 : Nat := 118140960795 + 3260143 * 2 ^ 59
def prefixEnd_3260143 : Nat := 4983230072969 + 3 ^ 40 * 3260143 * 2
def baseEnd_3260143 : Nat := 1674020361390943409219381

theorem tailTrace_3260143 : CollatzResearch.WordTrace tailWord_3260143 prefixEnd_3260143 1674020361390943409219381 := by
  unfold tailWord_3260143
  simp only [CollatzResearch.WordTrace]
  refine ⟨118907183828066173941345083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79271455885377449294230055 118907183828066173941345083)
  ·
    refine ⟨178360775742099260912017625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118907183828066173941345083 178360775742099260912017625)
    ·
      refine ⟨133770581806574445684013219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178360775742099260912017625 133770581806574445684013219)
      ·
        refine ⟨200655872709861668526019829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133770581806574445684013219 200655872709861668526019829)
        ·
          refine ⟨18811488066549531424314359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200655872709861668526019829 18811488066549531424314359)
          ·
            refine ⟨28217232099824297136471539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811488066549531424314359 28217232099824297136471539)
            ·
              refine ⟨42325848149736445704707309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28217232099824297136471539 42325848149736445704707309)
              ·
                refine ⟨15872193056151167139265241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42325848149736445704707309 15872193056151167139265241)
                ·
                  refine ⟨11904144792113375354448931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15872193056151167139265241 11904144792113375354448931)
                  ·
                    refine ⟨17856217188170063031673397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11904144792113375354448931 17856217188170063031673397)
                    ·
                      refine ⟨1674020361390943409219381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17856217188170063031673397 1674020361390943409219381)
                      ·
                        rfl

theorem cell23_3260143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_3260143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260143 prefixEnd_3260143 := by exact prefixLift 3260143
  have htrace : WordTrace (prefixWord ++ tailWord_3260143) baseStart_3260143 baseEnd_3260143 := by
    simpa [prefixWord, tailWord_3260143, baseEnd_3260143] using wordTrace_append hprefix tailTrace_3260143
  have hstable : (prefixWord ++ tailWord_3260143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260143).length < 2 ^ (prefixWord ++ tailWord_3260143).sum := by decide
  have hdescent : baseEnd_3260143 < baseStart_3260143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260170 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3260170 : Nat := 118140960795 + 3260170 * 2 ^ 59
def prefixEnd_3260170 : Nat := 4983230072969 + 3 ^ 40 * 3260170 * 2
def baseEnd_3260170 : Nat := 1674034225368614803581757

theorem tailTrace_3260170 : CollatzResearch.WordTrace tailWord_3260170 prefixEnd_3260170 1674034225368614803581757 := by
  unfold tailWord_3260170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727042149742089388144491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79272112399312238368385309 29727042149742089388144491)
  ·
    refine ⟨44590563224613134082216737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29727042149742089388144491 44590563224613134082216737)
    ·
      refine ⟨33442922418459850561662553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44590563224613134082216737 33442922418459850561662553)
      ·
        refine ⟨25082191813844887921246915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33442922418459850561662553 25082191813844887921246915)
        ·
          refine ⟨37623287720767331881870373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25082191813844887921246915 37623287720767331881870373)
          ·
            refine ⟨7054366447643874727850695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37623287720767331881870373 7054366447643874727850695)
            ·
              refine ⟨10581549671465812091776043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054366447643874727850695 10581549671465812091776043)
              ·
                refine ⟨15872324507198718137664065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581549671465812091776043 15872324507198718137664065)
                ·
                  refine ⟨11904243380399038603248049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15872324507198718137664065 11904243380399038603248049)
                  ·
                    refine ⟨8928182535299278952436037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11904243380399038603248049 8928182535299278952436037)
                    ·
                      refine ⟨1674034225368614803581757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8928182535299278952436037 1674034225368614803581757)
                      ·
                        rfl

theorem cell23_3260170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3260170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260170 prefixEnd_3260170 := by exact prefixLift 3260170
  have htrace : WordTrace (prefixWord ++ tailWord_3260170) baseStart_3260170 baseEnd_3260170 := by
    simpa [prefixWord, tailWord_3260170, baseEnd_3260170] using wordTrace_append hprefix tailTrace_3260170
  have hstable : (prefixWord ++ tailWord_3260170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260170).length < 2 ^ (prefixWord ++ tailWord_3260170).sum := by decide
  have hdescent : baseEnd_3260170 < baseStart_3260170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260174 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3260174 : Nat := 118140960795 + 3260174 * 2 ^ 59
def prefixEnd_3260174 : Nat := 4983230072969 + 3 ^ 40 * 3260174 * 2
def baseEnd_3260174 : Nat := 1674036279291232787931739

theorem tailTrace_3260174 : CollatzResearch.WordTrace tailWord_3260174 prefixEnd_3260174 1674036279291232787931739 := by
  unfold tailWord_3260174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863539311369233279465447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79272209660635910823815717 14863539311369233279465447)
  ·
    refine ⟨22295308967053849919198171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863539311369233279465447 22295308967053849919198171)
    ·
      refine ⟨33442963450580774878797257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22295308967053849919198171 33442963450580774878797257)
      ·
        refine ⟨25082222587935581159097943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33442963450580774878797257 25082222587935581159097943)
        ·
          refine ⟨37623333881903371738646915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25082222587935581159097943 37623333881903371738646915)
          ·
            refine ⟨56435000822855057607970373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37623333881903371738646915 56435000822855057607970373)
            ·
              refine ⟨10581562654285323301494445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56435000822855057607970373 10581562654285323301494445)
              ·
                refine ⟨3968085995356996238060417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10581562654285323301494445 3968085995356996238060417)
                ·
                  refine ⟨2976064496517747178545313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3968085995356996238060417 2976064496517747178545313)
                  ·
                    refine ⟨2232048372388310383908985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2976064496517747178545313 2232048372388310383908985)
                    ·
                      refine ⟨1674036279291232787931739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232048372388310383908985 1674036279291232787931739)
                      ·
                        rfl

theorem cell23_3260174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3260174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260174 prefixEnd_3260174 := by exact prefixLift 3260174
  have htrace : WordTrace (prefixWord ++ tailWord_3260174) baseStart_3260174 baseEnd_3260174 := by
    simpa [prefixWord, tailWord_3260174, baseEnd_3260174] using wordTrace_append hprefix tailTrace_3260174
  have hstable : (prefixWord ++ tailWord_3260174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260174).length < 2 ^ (prefixWord ++ tailWord_3260174).sum := by decide
  have hdescent : baseEnd_3260174 < baseStart_3260174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260197 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 5]
def baseStart_3260197 : Nat := 118140960795 + 3260197 * 2 ^ 59
def prefixEnd_3260197 : Nat := 4983230072969 + 3 ^ 40 * 3260197 * 2
def baseEnd_3260197 : Nat := 186005343260698466438237

theorem tailTrace_3260197 : CollatzResearch.WordTrace tailWord_3260197 prefixEnd_3260197 186005343260698466438237 := by
  unfold tailWord_3260197
  simp only [CollatzResearch.WordTrace]
  refine ⟨118909153369870541163810845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79272768913247027442540563 118909153369870541163810845)
  ·
    refine ⟨44590932513701452936429067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118909153369870541163810845 44590932513701452936429067)
    ·
      refine ⟨66886398770552179404643601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44590932513701452936429067 66886398770552179404643601)
      ·
        refine ⟨50164799077914134553482701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66886398770552179404643601 50164799077914134553482701)
        ·
          refine ⟨18811799654217800457556013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50164799077914134553482701 18811799654217800457556013)
          ·
            refine ⟨7054424870331675171583505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18811799654217800457556013 7054424870331675171583505)
            ·
              refine ⟨5290818652748756378687629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054424870331675171583505 5290818652748756378687629)
              ·
                refine ⟨1984056994780783642007861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5290818652748756378687629 1984056994780783642007861)
                ·
                  refine ⟨186005343260698466438237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984056994780783642007861 186005343260698466438237)
                  ·
                    rfl

theorem cell23_3260197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_3260197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260197 prefixEnd_3260197 := by exact prefixLift 3260197
  have htrace : WordTrace (prefixWord ++ tailWord_3260197) baseStart_3260197 baseEnd_3260197 := by
    simpa [prefixWord, tailWord_3260197, baseEnd_3260197] using wordTrace_append hprefix tailTrace_3260197
  have hstable : (prefixWord ++ tailWord_3260197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260197).length < 2 ^ (prefixWord ++ tailWord_3260197).sum := by decide
  have hdescent : baseEnd_3260197 < baseStart_3260197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260214 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3260214 : Nat := 118140960795 + 3260214 * 2 ^ 59
def prefixEnd_3260214 : Nat := 4983230072969 + 3 ^ 40 * 3260214 * 2
def baseEnd_3260214 : Nat := 186006313168601403492395

theorem tailTrace_3260214 : CollatzResearch.WordTrace tailWord_3260214 prefixEnd_3260214 186006313168601403492395 := by
  unfold tailWord_3260214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431860838175559566698731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79273182273872635378119797 7431860838175559566698731)
  ·
    refine ⟨11147791257263339350048097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431860838175559566698731 11147791257263339350048097)
    ·
      refine ⟨8360843442947504512536073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11147791257263339350048097 8360843442947504512536073)
      ·
        refine ⟨6270632582210628384402055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8360843442947504512536073 6270632582210628384402055)
        ·
          refine ⟨9405948873315942576603083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270632582210628384402055 9405948873315942576603083)
          ·
            refine ⟨14108923309973913864904625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405948873315942576603083 14108923309973913864904625)
            ·
              refine ⟨10581692482480435398678469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14108923309973913864904625 10581692482480435398678469)
              ·
                refine ⟨1984067340465081637252213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10581692482480435398678469 1984067340465081637252213)
                ·
                  refine ⟨186006313168601403492395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984067340465081637252213 186006313168601403492395)
                  ·
                    rfl

theorem cell23_3260214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3260214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260214 prefixEnd_3260214 := by exact prefixLift 3260214
  have htrace : WordTrace (prefixWord ++ tailWord_3260214) baseStart_3260214 baseEnd_3260214 := by
    simpa [prefixWord, tailWord_3260214, baseEnd_3260214] using wordTrace_append hprefix tailTrace_3260214
  have hstable : (prefixWord ++ tailWord_3260214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260214).length < 2 ^ (prefixWord ++ tailWord_3260214).sum := by decide
  have hdescent : baseEnd_3260214 < baseStart_3260214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260250 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3260250 : Nat := 118140960795 + 3260250 * 2 ^ 59
def prefixEnd_3260250 : Nat := 4983230072969 + 3 ^ 40 * 3260250 * 2
def baseEnd_3260250 : Nat := 1674075303820974490581389

theorem tailTrace_3260250 : CollatzResearch.WordTrace tailWord_3260250 prefixEnd_3260250 1674075303820974490581389 := by
  unfold tailWord_3260250
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727771609669632803872551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79274057625785687476993469 29727771609669632803872551)
  ·
    refine ⟨44591657414504449205808827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29727771609669632803872551 44591657414504449205808827)
    ·
      refine ⟨66887486121756673808713241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44591657414504449205808827 66887486121756673808713241)
      ·
        refine ⟨50165614591317505356534931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66887486121756673808713241 50165614591317505356534931)
        ·
          refine ⟨75248421886976258034802397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50165614591317505356534931 75248421886976258034802397)
          ·
            refine ⟨28218158207616096763050899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75248421886976258034802397 28218158207616096763050899)
            ·
              refine ⟨42327237311424145144576349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28218158207616096763050899 42327237311424145144576349)
              ·
                refine ⟨15872713991784054429216131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42327237311424145144576349 15872713991784054429216131)
                ·
                  refine ⟨23809070987676081643824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15872713991784054429216131 23809070987676081643824197)
                  ·
                    refine ⟨4464200810189265308217037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23809070987676081643824197 4464200810189265308217037)
                    ·
                      refine ⟨1674075303820974490581389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4464200810189265308217037 1674075303820974490581389)
                      ·
                        rfl

theorem cell23_3260250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3260250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260250 prefixEnd_3260250 := by exact prefixLift 3260250
  have htrace : WordTrace (prefixWord ++ tailWord_3260250) baseStart_3260250 baseEnd_3260250 := by
    simpa [prefixWord, tailWord_3260250, baseEnd_3260250] using wordTrace_append hprefix tailTrace_3260250
  have hstable : (prefixWord ++ tailWord_3260250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260250).length < 2 ^ (prefixWord ++ tailWord_3260250).sum := by decide
  have hdescent : baseEnd_3260250 < baseStart_3260250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260283 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 9]
def baseStart_3260283 : Nat := 118140960795 + 3260283 * 2 ^ 59
def prefixEnd_3260283 : Nat := 4983230072969 + 3 ^ 40 * 3260283 * 2
def baseEnd_3260283 : Nat := 558030749560857620489579

theorem tailTrace_3260283 : CollatzResearch.WordTrace tailWord_3260283 prefixEnd_3260283 558030749560857620489579 := by
  unfold tailWord_3260283
  simp only [CollatzResearch.WordTrace]
  refine ⟨118912290047558977851441503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79274860031705985234294335 118912290047558977851441503)
  ·
    refine ⟨178368435071338466777162255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118912290047558977851441503 178368435071338466777162255)
    ·
      refine ⟨267552652607007700165743383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178368435071338466777162255 267552652607007700165743383)
      ·
        refine ⟨401328978910511550248615075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267552652607007700165743383 401328978910511550248615075)
        ·
          refine ⟨601993468365767325372922613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401328978910511550248615075 601993468365767325372922613)
          ·
            refine ⟨56436887659290686753711495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 601993468365767325372922613 56436887659290686753711495)
            ·
              refine ⟨84655331488936030130567243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56436887659290686753711495 84655331488936030130567243)
              ·
                refine ⟨126982997233404045195850865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84655331488936030130567243 126982997233404045195850865)
                ·
                  refine ⟨95237247925053033896888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126982997233404045195850865 95237247925053033896888149)
                  ·
                    refine ⟨558030749560857620489579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95237247925053033896888149 558030749560857620489579)
                    ·
                      rfl

theorem cell23_3260283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_3260283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260283 prefixEnd_3260283 := by exact prefixLift 3260283
  have htrace : WordTrace (prefixWord ++ tailWord_3260283) baseStart_3260283 baseEnd_3260283 := by
    simpa [prefixWord, tailWord_3260283, baseEnd_3260283] using wordTrace_append hprefix tailTrace_3260283
  have hstable : (prefixWord ++ tailWord_3260283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260283).length < 2 ^ (prefixWord ++ tailWord_3260283).sum := by decide
  have hdescent : baseEnd_3260283 < baseStart_3260283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260297 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_3260297 : Nat := 118140960795 + 3260297 * 2 ^ 59
def prefixEnd_3260297 : Nat := 4983230072969 + 3 ^ 40 * 3260297 * 2
def baseEnd_3260297 : Nat := 1674099437411735806693673

theorem tailTrace_3260297 : CollatzResearch.WordTrace tailWord_3260297 prefixEnd_3260297 1674099437411735806693673 := by
  unfold tailWord_3260297
  simp only [CollatzResearch.WordTrace]
  refine ⟨118912800669508258242451145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79275200446338838828300763 118912800669508258242451145)
  ·
    refine ⟨89184600502131193681838359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118912800669508258242451145 89184600502131193681838359)
    ·
      refine ⟨133776900753196790522757539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89184600502131193681838359 133776900753196790522757539)
      ·
        refine ⟨200665351129795185784136309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133776900753196790522757539 200665351129795185784136309)
        ·
          refine ⟨18812376668418298667262779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200665351129795185784136309 18812376668418298667262779)
          ·
            refine ⟨28218565002627448000894169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18812376668418298667262779 28218565002627448000894169)
            ·
              refine ⟨21163923751970586000670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28218565002627448000894169 21163923751970586000670627)
              ·
                refine ⟨31745885627955879001005941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21163923751970586000670627 31745885627955879001005941)
                ·
                  refine ⟨2976176777620863656344307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31745885627955879001005941 2976176777620863656344307)
                  ·
                    refine ⟨4464265166431295484516461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2976176777620863656344307 4464265166431295484516461)
                    ·
                      refine ⟨1674099437411735806693673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4464265166431295484516461 1674099437411735806693673)
                      ·
                        rfl

theorem cell23_3260297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_3260297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260297 prefixEnd_3260297 := by exact prefixLift 3260297
  have htrace : WordTrace (prefixWord ++ tailWord_3260297) baseStart_3260297 baseEnd_3260297 := by
    simpa [prefixWord, tailWord_3260297, baseEnd_3260297] using wordTrace_append hprefix tailTrace_3260297
  have hstable : (prefixWord ++ tailWord_3260297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260297).length < 2 ^ (prefixWord ++ tailWord_3260297).sum := by decide
  have hdescent : baseEnd_3260297 < baseStart_3260297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260324 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_3260324 : Nat := 118140960795 + 3260324 * 2 ^ 59
def prefixEnd_3260324 : Nat := 4983230072969 + 3 ^ 40 * 3260324 * 2
def baseEnd_3260324 : Nat := 1674113301389407201056049

theorem tailTrace_3260324 : CollatzResearch.WordTrace tailWord_3260324 prefixEnd_3260324 1674113301389407201056049 := by
  unfold tailWord_3260324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59456892720205220926842013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79275856960273627902456017 59456892720205220926842013)
  ·
    refine ⟨22296334770076957847565755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59456892720205220926842013 22296334770076957847565755)
    ·
      refine ⟨33444502155115436771348633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22296334770076957847565755 33444502155115436771348633)
      ·
        refine ⟨25083376616336577578511475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33444502155115436771348633 25083376616336577578511475)
        ·
          refine ⟨37625064924504866367767213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25083376616336577578511475 37625064924504866367767213)
          ·
            refine ⟨14109399346689324887912705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37625064924504866367767213 14109399346689324887912705)
            ·
              refine ⟨10582049510016993665934529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14109399346689324887912705 10582049510016993665934529)
              ·
                refine ⟨7936537132512745249450897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10582049510016993665934529 7936537132512745249450897)
                ·
                  refine ⟨5952402849384558937088173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7936537132512745249450897 5952402849384558937088173)
                  ·
                    refine ⟨2232151068519209601408065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5952402849384558937088173 2232151068519209601408065)
                    ·
                      refine ⟨1674113301389407201056049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232151068519209601408065 1674113301389407201056049)
                      ·
                        rfl

theorem cell23_3260324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_3260324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260324 prefixEnd_3260324 := by exact prefixLift 3260324
  have htrace : WordTrace (prefixWord ++ tailWord_3260324) baseStart_3260324 baseEnd_3260324 := by
    simpa [prefixWord, tailWord_3260324, baseEnd_3260324] using wordTrace_append hprefix tailTrace_3260324
  have hstable : (prefixWord ++ tailWord_3260324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260324).length < 2 ^ (prefixWord ++ tailWord_3260324).sum := by decide
  have hdescent : baseEnd_3260324 < baseStart_3260324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260337 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3260337 : Nat := 118140960795 + 3260337 * 2 ^ 59
def prefixEnd_3260337 : Nat := 4983230072969 + 3 ^ 40 * 3260337 * 2
def baseEnd_3260337 : Nat := 1674119976637915650193489

theorem tailTrace_3260337 : CollatzResearch.WordTrace tailWord_3260337 prefixEnd_3260337 1674119976637915650193489 := by
  unfold tailWord_3260337
  simp only [CollatzResearch.WordTrace]
  refine ⟨118914259589363345073907265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79276173059575563382604843 118914259589363345073907265)
  ·
    refine ⟨89185694692022508805430449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118914259589363345073907265 89185694692022508805430449)
    ·
      refine ⟨66889271019016881604072837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89185694692022508805430449 66889271019016881604072837)
      ·
        refine ⟨12541738316065665300763657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66889271019016881604072837 12541738316065665300763657)
        ·
          refine ⟨9406303737049248975572743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12541738316065665300763657 9406303737049248975572743)
          ·
            refine ⟨14109455605573873463359115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406303737049248975572743 14109455605573873463359115)
            ·
              refine ⟨21164183408360810195038673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109455605573873463359115 21164183408360810195038673)
              ·
                refine ⟨15873137556270607646279005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21164183408360810195038673 15873137556270607646279005)
                ·
                  refine ⟨5952426583601477867354627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15873137556270607646279005 5952426583601477867354627)
                  ·
                    refine ⟨8928639875402216801031941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952426583601477867354627 8928639875402216801031941)
                    ·
                      refine ⟨1674119976637915650193489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8928639875402216801031941 1674119976637915650193489)
                      ·
                        rfl

theorem cell23_3260337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3260337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260337 prefixEnd_3260337 := by exact prefixLift 3260337
  have htrace : WordTrace (prefixWord ++ tailWord_3260337) baseStart_3260337 baseEnd_3260337 := by
    simpa [prefixWord, tailWord_3260337, baseEnd_3260337] using wordTrace_append hprefix tailTrace_3260337
  have hstable : (prefixWord ++ tailWord_3260337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260337).length < 2 ^ (prefixWord ++ tailWord_3260337).sum := by decide
  have hdescent : baseEnd_3260337 < baseStart_3260337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260401 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_3260401 : Nat := 118140960795 + 3260401 * 2 ^ 59
def prefixEnd_3260401 : Nat := 4983230072969 + 3 ^ 40 * 3260401 * 2
def baseEnd_3260401 : Nat := 1674152839399803399793195

theorem tailTrace_3260401 : CollatzResearch.WordTrace tailWord_3260401 prefixEnd_3260401 1674152839399803399793195 := by
  unfold tailWord_3260401
  simp only [CollatzResearch.WordTrace]
  refine ⟨118916593861131484004237057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79277729240754322669491371 118916593861131484004237057)
  ·
    refine ⟨89187445395848613003177793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118916593861131484004237057 89187445395848613003177793)
    ·
      refine ⟨66890584046886459752383345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89187445395848613003177793 66890584046886459752383345)
      ·
        refine ⟨50167938035164844814287509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66890584046886459752383345 50167938035164844814287509)
        ·
          refine ⟨2351622095398352100669727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50167938035164844814287509 2351622095398352100669727)
          ·
            refine ⟨3527433143097528151004591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351622095398352100669727 3527433143097528151004591)
            ·
              refine ⟨5291149714646292226506887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527433143097528151004591 5291149714646292226506887)
              ·
                refine ⟨7936724571969438339760331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291149714646292226506887 7936724571969438339760331)
                ·
                  refine ⟨11905086857954157509640497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936724571969438339760331 11905086857954157509640497)
                  ·
                    refine ⟨8928815143465618132230373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11905086857954157509640497 8928815143465618132230373)
                    ·
                      refine ⟨1674152839399803399793195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8928815143465618132230373 1674152839399803399793195)
                      ·
                        rfl

theorem cell23_3260401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_3260401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260401 prefixEnd_3260401 := by exact prefixLift 3260401
  have htrace : WordTrace (prefixWord ++ tailWord_3260401) baseStart_3260401 baseEnd_3260401 := by
    simpa [prefixWord, tailWord_3260401, baseEnd_3260401] using wordTrace_append hprefix tailTrace_3260401
  have hstable : (prefixWord ++ tailWord_3260401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260401).length < 2 ^ (prefixWord ++ tailWord_3260401).sum := by decide
  have hdescent : baseEnd_3260401 < baseStart_3260401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260447 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3260447 : Nat := 118140960795 + 3260447 * 2 ^ 59
def prefixEnd_3260447 : Nat := 4983230072969 + 3 ^ 40 * 3260447 * 2
def baseEnd_3260447 : Nat := 1674176459509910219817983

theorem tailTrace_3260447 : CollatzResearch.WordTrace tailWord_3260447 prefixEnd_3260447 1674176459509910219817983 := by
  unfold tailWord_3260447
  simp only [CollatzResearch.WordTrace]
  refine ⟨118918271618964833860411595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79278847745976555906941063 118918271618964833860411595)
  ·
    refine ⟨178377407428447250790617393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118918271618964833860411595 178377407428447250790617393)
    ·
      refine ⟨133783055571335438092963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178377407428447250790617393 133783055571335438092963045)
      ·
        refine ⟨25084322919625394642430571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133783055571335438092963045 25084322919625394642430571)
        ·
          refine ⟨37626484379438091963645857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25084322919625394642430571 37626484379438091963645857)
          ·
            refine ⟨28219863284578568972734393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37626484379438091963645857 28219863284578568972734393)
            ·
              refine ⟨21164897463433926729550795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28219863284578568972734393 21164897463433926729550795)
              ·
                refine ⟨31747346195150890094326193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21164897463433926729550795 31747346195150890094326193)
                ·
                  refine ⟨23810509646363167570744645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31747346195150890094326193 23810509646363167570744645)
                  ·
                    refine ⟨4464470558693093919514621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23810509646363167570744645 4464470558693093919514621)
                    ·
                      refine ⟨1674176459509910219817983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4464470558693093919514621 1674176459509910219817983)
                      ·
                        rfl

theorem cell23_3260447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3260447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260447 prefixEnd_3260447 := by exact prefixLift 3260447
  have htrace : WordTrace (prefixWord ++ tailWord_3260447) baseStart_3260447 baseEnd_3260447 := by
    simpa [prefixWord, tailWord_3260447, baseEnd_3260447] using wordTrace_append hprefix tailTrace_3260447
  have hstable : (prefixWord ++ tailWord_3260447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260447).length < 2 ^ (prefixWord ++ tailWord_3260447).sum := by decide
  have hdescent : baseEnd_3260447 < baseStart_3260447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260478 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3260478 : Nat := 118140960795 + 3260478 * 2 ^ 59
def prefixEnd_3260478 : Nat := 4983230072969 + 3 ^ 40 * 3260478 * 2
def baseEnd_3260478 : Nat := 1674192377410199598530341

theorem tailTrace_3260478 : CollatzResearch.WordTrace tailWord_3260478 prefixEnd_3260478 1674192377410199598530341 := by
  unfold tailWord_3260478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14864925285231565769348761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79279601521235017436526725 14864925285231565769348761)
  ·
    refine ⟨11148693963923674327011571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14864925285231565769348761 11148693963923674327011571)
    ·
      refine ⟨16723040945885511490517357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148693963923674327011571 16723040945885511490517357)
      ·
        refine ⟨6271140354707066808944009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16723040945885511490517357 6271140354707066808944009)
        ·
          refine ⟨4703355266030300106708007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271140354707066808944009 4703355266030300106708007)
          ·
            refine ⟨7055032899045450160062011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703355266030300106708007 7055032899045450160062011)
            ·
              refine ⟨10582549348568175240093017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055032899045450160062011 10582549348568175240093017)
              ·
                refine ⟨7936912011426131430069763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10582549348568175240093017 7936912011426131430069763)
                ·
                  refine ⟨11905368017139197145104645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936912011426131430069763 11905368017139197145104645)
                  ·
                    refine ⟨2232256503213599464707121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11905368017139197145104645 2232256503213599464707121)
                    ·
                      refine ⟨1674192377410199598530341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232256503213599464707121 1674192377410199598530341)
                      ·
                        rfl

theorem cell23_3260478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3260478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260478 prefixEnd_3260478 := by exact prefixLift 3260478
  have htrace : WordTrace (prefixWord ++ tailWord_3260478) baseStart_3260478 baseEnd_3260478 := by
    simpa [prefixWord, tailWord_3260478, baseEnd_3260478] using wordTrace_append hprefix tailTrace_3260478
  have hstable : (prefixWord ++ tailWord_3260478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260478).length < 2 ^ (prefixWord ++ tailWord_3260478).sum := by decide
  have hdescent : baseEnd_3260478 < baseStart_3260478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260501 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 5]
def baseStart_3260501 : Nat := 118140960795 + 3260501 * 2 ^ 59
def prefixEnd_3260501 : Nat := 4983230072969 + 3 ^ 40 * 3260501 * 2
def baseEnd_3260501 : Nat := 186022687496139223171415

theorem tailTrace_3260501 : CollatzResearch.WordTrace tailWord_3260501 prefixEnd_3260501 186022687496139223171415 := by
  unfold tailWord_3260501
  simp only [CollatzResearch.WordTrace]
  refine ⟨118920241160769201082877357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79280160773846134055251571 118920241160769201082877357)
  ·
    refine ⟨44595090435288450406079009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118920241160769201082877357 44595090435288450406079009)
    ·
      refine ⟨33446317826466337804559257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44595090435288450406079009 33446317826466337804559257)
      ·
        refine ⟨25084738369849753353419443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33446317826466337804559257 25084738369849753353419443)
        ·
          refine ⟨37627107554774630030129165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25084738369849753353419443 37627107554774630030129165)
          ·
            refine ⟨14110165333040486261298437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37627107554774630030129165 14110165333040486261298437)
            ·
              refine ⟨2645655999945091173993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14110165333040486261298437 2645655999945091173993457)
              ·
                refine ⟨1984241999958818380495093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645655999945091173993457 1984241999958818380495093)
                ·
                  refine ⟨186022687496139223171415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984241999958818380495093 186022687496139223171415)
                  ·
                    rfl

theorem cell23_3260501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_3260501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260501 prefixEnd_3260501 := by exact prefixLift 3260501
  have htrace : WordTrace (prefixWord ++ tailWord_3260501) baseStart_3260501 baseEnd_3260501 := by
    simpa [prefixWord, tailWord_3260501, baseEnd_3260501] using wordTrace_append hprefix tailTrace_3260501
  have hstable : (prefixWord ++ tailWord_3260501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260501).length < 2 ^ (prefixWord ++ tailWord_3260501).sum := by decide
  have hdescent : baseEnd_3260501 < baseStart_3260501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260504 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_3260504 : Nat := 118140960795 + 3260504 * 2 ^ 59
def prefixEnd_3260504 : Nat := 4983230072969 + 3 ^ 40 * 3260504 * 2
def baseEnd_3260504 : Nat := 1674205727907216496805221

theorem tailTrace_3260504 : CollatzResearch.WordTrace tailWord_3260504 prefixEnd_3260504 1674205727907216496805221 := by
  unfold tailWord_3260504
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460175289879166297618283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79280233719838888396824377 59460175289879166297618283)
  ·
    refine ⟨89190262934818749446427425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59460175289879166297618283 89190262934818749446427425)
    ·
      refine ⟨66892697201114062084820569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89190262934818749446427425 66892697201114062084820569)
      ·
        refine ⟨50169522900835546563615427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66892697201114062084820569 50169522900835546563615427)
        ·
          refine ⟨75254284351253319845423141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50169522900835546563615427 75254284351253319845423141)
          ·
            refine ⟨14110178315859997471016839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75254284351253319845423141 14110178315859997471016839)
            ·
              refine ⟨21165267473789996206525259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14110178315859997471016839 21165267473789996206525259)
              ·
                refine ⟨31747901210684994309787889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21165267473789996206525259 31747901210684994309787889)
                ·
                  refine ⟨23810925908013745732340917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31747901210684994309787889 23810925908013745732340917)
                  ·
                    refine ⟨2232274303876288662406961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23810925908013745732340917 2232274303876288662406961)
                    ·
                      refine ⟨1674205727907216496805221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232274303876288662406961 1674205727907216496805221)
                      ·
                        rfl

theorem cell23_3260504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_3260504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260504 prefixEnd_3260504 := by exact prefixLift 3260504
  have htrace : WordTrace (prefixWord ++ tailWord_3260504) baseStart_3260504 baseEnd_3260504 := by
    simpa [prefixWord, tailWord_3260504, baseEnd_3260504] using wordTrace_append hprefix tailTrace_3260504
  have hstable : (prefixWord ++ tailWord_3260504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260504).length < 2 ^ (prefixWord ++ tailWord_3260504).sum := by decide
  have hdescent : baseEnd_3260504 < baseStart_3260504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260547 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_3260547 : Nat := 118140960795 + 3260547 * 2 ^ 59
def prefixEnd_3260547 : Nat := 4983230072969 + 3 ^ 40 * 3260547 * 2
def baseEnd_3260547 : Nat := 1674227807575359828567523

theorem tailTrace_3260547 : CollatzResearch.WordTrace tailWord_3260547 prefixEnd_3260547 1674227807575359828567523 := by
  unfold tailWord_3260547
  simp only [CollatzResearch.WordTrace]
  refine ⟨118921918918602550939051895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79281279279068367292701263 118921918918602550939051895)
  ·
    refine ⟨178382878377903826408577843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118921918918602550939051895 178382878377903826408577843)
    ·
      refine ⟨267574317566855739612866765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178382878377903826408577843 267574317566855739612866765)
      ·
        refine ⟨100340369087570902354825037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267574317566855739612866765 100340369087570902354825037)
        ·
          refine ⟨37627638407839088383059389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100340369087570902354825037 37627638407839088383059389)
          ·
            refine ⟨14110364402939658143647271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37627638407839088383059389 14110364402939658143647271)
            ·
              refine ⟨21165546604409487215470907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14110364402939658143647271 21165546604409487215470907)
              ·
                refine ⟨31748319906614230823206361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21165546604409487215470907 31748319906614230823206361)
                ·
                  refine ⟨23811239929960673117404771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31748319906614230823206361 23811239929960673117404771)
                  ·
                    refine ⟨35716859894941009676107157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23811239929960673117404771 35716859894941009676107157)
                    ·
                      refine ⟨1674227807575359828567523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35716859894941009676107157 1674227807575359828567523)
                      ·
                        rfl

theorem cell23_3260547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_3260547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260547 prefixEnd_3260547 := by exact prefixLift 3260547
  have htrace : WordTrace (prefixWord ++ tailWord_3260547) baseStart_3260547 baseEnd_3260547 := by
    simpa [prefixWord, tailWord_3260547, baseEnd_3260547] using wordTrace_append hprefix tailTrace_3260547
  have hstable : (prefixWord ++ tailWord_3260547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260547).length < 2 ^ (prefixWord ++ tailWord_3260547).sum := by decide
  have hdescent : baseEnd_3260547 < baseStart_3260547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260587 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 9, 5]
def baseStart_3260587 : Nat := 118140960795 + 3260587 * 2 ^ 59
def prefixEnd_3260587 : Nat := 4983230072969 + 3 ^ 40 * 3260587 * 2
def baseEnd_3260587 : Nat := 558082782267179890689113

theorem tailTrace_3260587 : CollatzResearch.WordTrace tailWord_3260587 prefixEnd_3260587 558082782267179890689113 := by
  unfold tailWord_3260587
  simp only [CollatzResearch.WordTrace]
  refine ⟨118923377838457637770508015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79282251892305091847005343 118923377838457637770508015)
  ·
    refine ⟨178385066757686456655762023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118923377838457637770508015 178385066757686456655762023)
    ·
      refine ⟨267577600136529684983643035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178385066757686456655762023 267577600136529684983643035)
      ·
        refine ⟨401366400204794527475464553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267577600136529684983643035 401366400204794527475464553)
        ·
          refine ⟨301024800153595895606598415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401366400204794527475464553 301024800153595895606598415)
          ·
            refine ⟨451537200230393843409897623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301024800153595895606598415 451537200230393843409897623)
            ·
              refine ⟨677305800345590765114846435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451537200230393843409897623 677305800345590765114846435)
              ·
                refine ⟨1015958700518386147672269653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677305800345590765114846435 1015958700518386147672269653)
                ·
                  refine ⟨5952883010849918834017205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1015958700518386147672269653 5952883010849918834017205)
                  ·
                    refine ⟨558082782267179890689113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5952883010849918834017205 558082782267179890689113)
                    ·
                      rfl

theorem cell23_3260587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].length) (baseStart_3260587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260587 prefixEnd_3260587 := by exact prefixLift 3260587
  have htrace : WordTrace (prefixWord ++ tailWord_3260587) baseStart_3260587 baseEnd_3260587 := by
    simpa [prefixWord, tailWord_3260587, baseEnd_3260587] using wordTrace_append hprefix tailTrace_3260587
  have hstable : (prefixWord ++ tailWord_3260587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260587).length < 2 ^ (prefixWord ++ tailWord_3260587).sum := by decide
  have hdescent : baseEnd_3260587 < baseStart_3260587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260617 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_3260617 : Nat := 118140960795 + 3260617 * 2 ^ 59
def prefixEnd_3260617 : Nat := 4983230072969 + 3 ^ 40 * 3260617 * 2
def baseEnd_3260617 : Nat := 558087917073724851564067

theorem tailTrace_3260617 : CollatzResearch.WordTrace tailWord_3260617 prefixEnd_3260617 558087917073724851564067 := by
  unfold tailWord_3260617
  simp only [CollatzResearch.WordTrace]
  refine ⟨118924472028348952894100105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79282981352232635262733403 118924472028348952894100105)
  ·
    refine ⟨89193354021261714670575079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118924472028348952894100105 89193354021261714670575079)
    ·
      refine ⟨133790031031892572005862619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89193354021261714670575079 133790031031892572005862619)
      ·
        refine ⟨200685046547838858008793929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133790031031892572005862619 200685046547838858008793929)
        ·
          refine ⟨150513784910879143506595447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200685046547838858008793929 150513784910879143506595447)
          ·
            refine ⟨225770677366318715259893171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150513784910879143506595447 225770677366318715259893171)
            ·
              refine ⟨338656016049478072889839757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225770677366318715259893171 338656016049478072889839757)
              ·
                refine ⟨126996006018554277333689909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338656016049478072889839757 126996006018554277333689909)
                ·
                  refine ⟨11905875564239463500033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126996006018554277333689909 11905875564239463500033429)
                  ·
                    refine ⟨558087917073724851564067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11905875564239463500033429 558087917073724851564067)
                    ·
                      rfl

theorem cell23_3260617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_3260617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260617 prefixEnd_3260617 := by exact prefixLift 3260617
  have htrace : WordTrace (prefixWord ++ tailWord_3260617) baseStart_3260617 baseEnd_3260617 := by
    simpa [prefixWord, tailWord_3260617, baseEnd_3260617] using wordTrace_append hprefix tailTrace_3260617
  have hstable : (prefixWord ++ tailWord_3260617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260617).length < 2 ^ (prefixWord ++ tailWord_3260617).sum := by decide
  have hdescent : baseEnd_3260617 < baseStart_3260617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260667 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_3260667 : Nat := 118140960795 + 3260667 * 2 ^ 59
def prefixEnd_3260667 : Nat := 4983230072969 + 3 ^ 40 * 3260667 * 2
def baseEnd_3260667 : Nat := 1674289425253899359066971

theorem tailTrace_3260667 : CollatzResearch.WordTrace tailWord_3260667 prefixEnd_3260667 1674289425253899359066971 := by
  unfold tailWord_3260667
  simp only [CollatzResearch.WordTrace]
  refine ⟨118926295678167811433420255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79284197118778540955613503 118926295678167811433420255)
  ·
    refine ⟨178389443517251717150130383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118926295678167811433420255 178389443517251717150130383)
    ·
      refine ⟨267584165275877575725195575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178389443517251717150130383 267584165275877575725195575)
      ·
        refine ⟨401376247913816363587793363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267584165275877575725195575 401376247913816363587793363)
        ·
          refine ⟨602064371870724545381690045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401376247913816363587793363 602064371870724545381690045)
          ·
            refine ⟨225774139451521704518133767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602064371870724545381690045 225774139451521704518133767)
            ·
              refine ⟨338661209177282556777200651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225774139451521704518133767 338661209177282556777200651)
              ·
                refine ⟨507991813765923835165800977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338661209177282556777200651 507991813765923835165800977)
                ·
                  refine ⟨380993860324442876374350733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507991813765923835165800977 380993860324442876374350733)
                  ·
                    refine ⟨142872697621666078640381525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380993860324442876374350733 142872697621666078640381525)
                    ·
                      refine ⟨1674289425253899359066971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142872697621666078640381525 1674289425253899359066971)
                      ·
                        rfl

theorem cell23_3260667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_3260667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260667 prefixEnd_3260667 := by exact prefixLift 3260667
  have htrace : WordTrace (prefixWord ++ tailWord_3260667) baseStart_3260667 baseEnd_3260667 := by
    simpa [prefixWord, tailWord_3260667, baseEnd_3260667] using wordTrace_append hprefix tailTrace_3260667
  have hstable : (prefixWord ++ tailWord_3260667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260667).length < 2 ^ (prefixWord ++ tailWord_3260667).sum := by decide
  have hdescent : baseEnd_3260667 < baseStart_3260667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260668 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3260668 : Nat := 118140960795 + 3260668 * 2 ^ 59
def prefixEnd_3260668 : Nat := 4983230072969 + 3 ^ 40 * 3260668 * 2
def baseEnd_3260668 : Nat := 558096646244851285051489

theorem tailTrace_3260668 : CollatzResearch.WordTrace tailWord_3260668 prefixEnd_3260668 558096646244851285051489 := by
  unfold tailWord_3260668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59463166075582094302103329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79284221434109459069471105 59463166075582094302103329)
  ·
    refine ⟨44597374556686570726577497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59463166075582094302103329 44597374556686570726577497)
    ·
      refine ⟨33448030917514928044933123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44597374556686570726577497 33448030917514928044933123)
      ·
        refine ⟨50172046376272392067399685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33448030917514928044933123 50172046376272392067399685)
        ·
          refine ⟨9407258695551073512637441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50172046376272392067399685 9407258695551073512637441)
          ·
            refine ⟨7055444021663305134478081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9407258695551073512637441 7055444021663305134478081)
            ·
              refine ⟨5291583016247478850858561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055444021663305134478081 5291583016247478850858561)
              ·
                refine ⟨3968687262185609138143921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5291583016247478850858561 3968687262185609138143921)
                ·
                  refine ⟨2976515446639206853607941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3968687262185609138143921 2976515446639206853607941)
                  ·
                    refine ⟨558096646244851285051489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976515446639206853607941 558096646244851285051489)
                    ·
                      rfl

theorem cell23_3260668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3260668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260668 prefixEnd_3260668 := by exact prefixLift 3260668
  have htrace : WordTrace (prefixWord ++ tailWord_3260668) baseStart_3260668 baseEnd_3260668 := by
    simpa [prefixWord, tailWord_3260668, baseEnd_3260668] using wordTrace_append hprefix tailTrace_3260668
  have hstable : (prefixWord ++ tailWord_3260668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260668).length < 2 ^ (prefixWord ++ tailWord_3260668).sum := by decide
  have hdescent : baseEnd_3260668 < baseStart_3260668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260675 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 1, 2, 2]
def baseStart_3260675 : Nat := 118140960795 + 3260675 * 2 ^ 59
def prefixEnd_3260675 : Nat := 4983230072969 + 3 ^ 40 * 3260675 * 2
def baseEnd_3260675 : Nat := 1674293533099135327766935

theorem tailTrace_3260675 : CollatzResearch.WordTrace tailWord_3260675 prefixEnd_3260675 1674293533099135327766935 := by
  unfold tailWord_3260675
  simp only [CollatzResearch.WordTrace]
  refine ⟨118926587462138828799711479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79284391641425885866474319 118926587462138828799711479)
  ·
    refine ⟨178389881193208243199567219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118926587462138828799711479 178389881193208243199567219)
    ·
      refine ⟨267584821789812364799350829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178389881193208243199567219 267584821789812364799350829)
      ·
        refine ⟨100344308171179636799756561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267584821789812364799350829 100344308171179636799756561)
        ·
          refine ⟨75258231128384727599817421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100344308171179636799756561 75258231128384727599817421)
          ·
            refine ⟨28221836673144272849931533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75258231128384727599817421 28221836673144272849931533)
            ·
              refine ⟨10583188752429102318724325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28221836673144272849931533 10583188752429102318724325)
              ·
                refine ⟨1984347891080456684760811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10583188752429102318724325 1984347891080456684760811)
                ·
                  refine ⟨2976521836620685027141217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984347891080456684760811 2976521836620685027141217)
                  ·
                    refine ⟨2232391377465513770355913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2976521836620685027141217 2232391377465513770355913)
                    ·
                      refine ⟨1674293533099135327766935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232391377465513770355913 1674293533099135327766935)
                      ·
                        rfl

theorem cell23_3260675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_3260675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260675 prefixEnd_3260675 := by exact prefixLift 3260675
  have htrace : WordTrace (prefixWord ++ tailWord_3260675) baseStart_3260675 baseEnd_3260675 := by
    simpa [prefixWord, tailWord_3260675, baseEnd_3260675] using wordTrace_append hprefix tailTrace_3260675
  have hstable : (prefixWord ++ tailWord_3260675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260675).length < 2 ^ (prefixWord ++ tailWord_3260675).sum := by decide
  have hdescent : baseEnd_3260675 < baseStart_3260675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260712 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3260712 : Nat := 118140960795 + 3260712 * 2 ^ 59
def prefixEnd_3260712 : Nat := 4983230072969 + 3 ^ 40 * 3260712 * 2
def baseEnd_3260712 : Nat := 1674312531883351683004265

theorem tailTrace_3260712 : CollatzResearch.WordTrace tailWord_3260712 prefixEnd_3260712 1674312531883351683004265 := by
  unfold tailWord_3260712
  simp only [CollatzResearch.WordTrace]
  refine ⟨59463968481502392059404195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79285291308669856079205593 59463968481502392059404195)
  ·
    refine ⟨89195952722253588089106293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59463968481502392059404195 89195952722253588089106293)
    ·
      refine ⟨8362120567711273883353715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89195952722253588089106293 8362120567711273883353715)
      ·
        refine ⟨12543180851566910825030573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362120567711273883353715 12543180851566910825030573)
        ·
          refine ⟨4703692819337591559386465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12543180851566910825030573 4703692819337591559386465)
          ·
            refine ⟨3527769614503193669539849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703692819337591559386465 3527769614503193669539849)
            ·
              refine ⟨2645827210877395252154887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527769614503193669539849 2645827210877395252154887)
              ·
                refine ⟨3968740816316092878232331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645827210877395252154887 3968740816316092878232331)
                ·
                  refine ⟨5953111224474139317348497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968740816316092878232331 5953111224474139317348497)
                  ·
                    refine ⟨4464833418355604488011373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953111224474139317348497 4464833418355604488011373)
                    ·
                      refine ⟨1674312531883351683004265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4464833418355604488011373 1674312531883351683004265)
                      ·
                        rfl

theorem cell23_3260712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3260712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260712 prefixEnd_3260712 := by exact prefixLift 3260712
  have htrace : WordTrace (prefixWord ++ tailWord_3260712) baseStart_3260712 baseEnd_3260712 := by
    simpa [prefixWord, tailWord_3260712, baseEnd_3260712] using wordTrace_append hprefix tailTrace_3260712
  have hstable : (prefixWord ++ tailWord_3260712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260712).length < 2 ^ (prefixWord ++ tailWord_3260712).sum := by decide
  have hdescent : baseEnd_3260712 < baseStart_3260712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260888 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3260888 : Nat := 118140960795 + 3260888 * 2 ^ 59
def prefixEnd_3260888 : Nat := 4983230072969 + 3 ^ 40 * 3260888 * 2
def baseEnd_3260888 : Nat := 1674402904478542994403455

theorem tailTrace_3260888 : CollatzResearch.WordTrace tailWord_3260888 prefixEnd_3260888 1674402904478542994403455 := by
  unfold tailWord_3260888
  simp only [CollatzResearch.WordTrace]
  refine ⟨59467178105183583088607659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79289570806911444118143545 59467178105183583088607659)
  ·
    refine ⟨89200767157775374632911489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59467178105183583088607659 89200767157775374632911489)
    ·
      refine ⟨66900575368331530974683617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89200767157775374632911489 66900575368331530974683617)
      ·
        refine ⟨50175431526248648231012713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66900575368331530974683617 50175431526248648231012713)
        ·
          refine ⟨37631573644686486173259535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50175431526248648231012713 37631573644686486173259535)
          ·
            refine ⟨56447360467029729259889303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37631573644686486173259535 56447360467029729259889303)
            ·
              refine ⟨84671040700544593889833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56447360467029729259889303 84671040700544593889833955)
              ·
                refine ⟨127006561050816890834750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84671040700544593889833955 127006561050816890834750933)
                ·
                  refine ⟨2976716274628520878939475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127006561050816890834750933 2976716274628520878939475)
                  ·
                    refine ⟨4465074411942781318409213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2976716274628520878939475 4465074411942781318409213)
                    ·
                      refine ⟨1674402904478542994403455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465074411942781318409213 1674402904478542994403455)
                      ·
                        rfl

theorem cell23_3260888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3260888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260888 prefixEnd_3260888 := by exact prefixLift 3260888
  have htrace : WordTrace (prefixWord ++ tailWord_3260888) baseStart_3260888 baseEnd_3260888 := by
    simpa [prefixWord, tailWord_3260888, baseEnd_3260888] using wordTrace_append hprefix tailTrace_3260888
  have hstable : (prefixWord ++ tailWord_3260888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260888).length < 2 ^ (prefixWord ++ tailWord_3260888).sum := by decide
  have hdescent : baseEnd_3260888 < baseStart_3260888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260931 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_3260931 : Nat := 118140960795 + 3260931 * 2 ^ 59
def prefixEnd_3260931 : Nat := 4983230072969 + 3 ^ 40 * 3260931 * 2
def baseEnd_3260931 : Nat := 1674424984146686326165757

theorem tailTrace_3260931 : CollatzResearch.WordTrace tailWord_3260931 prefixEnd_3260931 1674424984146686326165757 := by
  unfold tailWord_3260931
  simp only [CollatzResearch.WordTrace]
  refine ⟨118935924549211384521030647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79290616366140923014020431 118935924549211384521030647)
  ·
    refine ⟨178403886823817076781545971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118935924549211384521030647 178403886823817076781545971)
    ·
      refine ⟨267605830235725615172318957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178403886823817076781545971 267605830235725615172318957)
      ·
        refine ⟨100352186338397105689619609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267605830235725615172318957 100352186338397105689619609)
        ·
          refine ⟨75264139753797829267214707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100352186338397105689619609 75264139753797829267214707)
          ·
            refine ⟨112896209630696743900822061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75264139753797829267214707 112896209630696743900822061)
            ·
              refine ⟨42336078611511278962808273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112896209630696743900822061 42336078611511278962808273)
              ·
                refine ⟨31752058958633459222106205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42336078611511278962808273 31752058958633459222106205)
                ·
                  refine ⟨11907022109487547208289827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31752058958633459222106205 11907022109487547208289827)
                  ·
                    refine ⟨17860533164231320812434741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11907022109487547208289827 17860533164231320812434741)
                    ·
                      refine ⟨1674424984146686326165757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17860533164231320812434741 1674424984146686326165757)
                      ·
                        rfl

theorem cell23_3260931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_3260931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260931 prefixEnd_3260931 := by exact prefixLift 3260931
  have htrace : WordTrace (prefixWord ++ tailWord_3260931) baseStart_3260931 baseEnd_3260931 := by
    simpa [prefixWord, tailWord_3260931, baseEnd_3260931] using wordTrace_append hprefix tailTrace_3260931
  have hstable : (prefixWord ++ tailWord_3260931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260931).length < 2 ^ (prefixWord ++ tailWord_3260931).sum := by decide
  have hdescent : baseEnd_3260931 < baseStart_3260931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260938 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3260938 : Nat := 118140960795 + 3260938 * 2 ^ 59
def prefixEnd_3260938 : Nat := 4983230072969 + 3 ^ 40 * 3260938 * 2
def baseEnd_3260938 : Nat := 558142859503755932926075

theorem tailTrace_3260938 : CollatzResearch.WordTrace tailWord_3260938 prefixEnd_3260938 558142859503755932926075 := by
  unfold tailWord_3260938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734044965046506179133867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79290786573457349811023645 29734044965046506179133867)
  ·
    refine ⟨44601067447569759268700801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29734044965046506179133867 44601067447569759268700801)
    ·
      refine ⟨33450800585677319451525601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44601067447569759268700801 33450800585677319451525601)
      ·
        refine ⟨25088100439257989588644201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33450800585677319451525601 25088100439257989588644201)
        ·
          refine ⟨18816075329443492191483151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25088100439257989588644201 18816075329443492191483151)
          ·
            refine ⟨28224112994165238287224727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18816075329443492191483151 28224112994165238287224727)
            ·
              refine ⟨42336169491247857430837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28224112994165238287224727 42336169491247857430837091)
              ·
                refine ⟨63504254236871786146255637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42336169491247857430837091 63504254236871786146255637)
                ·
                  refine ⟨2976761917353364975605733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63504254236871786146255637 2976761917353364975605733)
                  ·
                    refine ⟨558142859503755932926075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976761917353364975605733 558142859503755932926075)
                    ·
                      rfl

theorem cell23_3260938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3260938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260938 prefixEnd_3260938 := by exact prefixLift 3260938
  have htrace : WordTrace (prefixWord ++ tailWord_3260938) baseStart_3260938 baseEnd_3260938 := by
    simpa [prefixWord, tailWord_3260938, baseEnd_3260938] using wordTrace_append hprefix tailTrace_3260938
  have hstable : (prefixWord ++ tailWord_3260938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260938).length < 2 ^ (prefixWord ++ tailWord_3260938).sum := by decide
  have hdescent : baseEnd_3260938 < baseStart_3260938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260939 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 1, 1, 3]
def baseStart_3260939 : Nat := 118140960795 + 3260939 * 2 ^ 59
def prefixEnd_3260939 : Nat := 4983230072969 + 3 ^ 40 * 3260939 * 2
def baseEnd_3260939 : Nat := 1674429091991922294865721

theorem tailTrace_3260939 : CollatzResearch.WordTrace tailWord_3260939 prefixEnd_3260939 1674429091991922294865721 := by
  unfold tailWord_3260939
  simp only [CollatzResearch.WordTrace]
  refine ⟨118936216333182401887321871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79290810888788267924881247 118936216333182401887321871)
  ·
    refine ⟨178404324499773602830982807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118936216333182401887321871 178404324499773602830982807)
    ·
      refine ⟨267606486749660404246474211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178404324499773602830982807 267606486749660404246474211)
      ·
        refine ⟨401409730124490606369711317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267606486749660404246474211 401409730124490606369711317)
        ·
          refine ⟨9408040549792748586790109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 401409730124490606369711317 9408040549792748586790109)
          ·
            refine ⟨3528015206172280720046291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9408040549792748586790109 3528015206172280720046291)
            ·
              refine ⟨5292022809258421080069437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528015206172280720046291 5292022809258421080069437)
              ·
                refine ⟨1984508553471907905026039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5292022809258421080069437 1984508553471907905026039)
                ·
                  refine ⟨2976762830207861857539059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984508553471907905026039 2976762830207861857539059)
                  ·
                    refine ⟨4465144245311792786308589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2976762830207861857539059 4465144245311792786308589)
                    ·
                      refine ⟨1674429091991922294865721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465144245311792786308589 1674429091991922294865721)
                      ·
                        rfl

theorem cell23_3260939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 1, 3].length) (baseStart_3260939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260939 prefixEnd_3260939 := by exact prefixLift 3260939
  have htrace : WordTrace (prefixWord ++ tailWord_3260939) baseStart_3260939 baseEnd_3260939 := by
    simpa [prefixWord, tailWord_3260939, baseEnd_3260939] using wordTrace_append hprefix tailTrace_3260939
  have hstable : (prefixWord ++ tailWord_3260939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260939).length < 2 ^ (prefixWord ++ tailWord_3260939).sum := by decide
  have hdescent : baseEnd_3260939 < baseStart_3260939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260968 : List Nat := [2, 1, 5, 2, 1, 1, 1, 10]
def baseStart_3260968 : Nat := 118140960795 + 3260968 * 2 ^ 59
def prefixEnd_3260968 : Nat := 4983230072969 + 3 ^ 40 * 3260968 * 2
def baseEnd_3260968 : Nat := 62016443812255654866781

theorem tailTrace_3260968 : CollatzResearch.WordTrace tailWord_3260968 prefixEnd_3260968 62016443812255654866781 := by
  unfold tailWord_3260968
  simp only [CollatzResearch.WordTrace]
  refine ⟨59468637025038669920063779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79291516033384893226751705 59468637025038669920063779)
  ·
    refine ⟨89202955537558004880095669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59468637025038669920063779 89202955537558004880095669)
    ·
      refine ⟨8362777081646062957508969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89202955537558004880095669 8362777081646062957508969)
      ·
        refine ⟨6272082811234547218131727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8362777081646062957508969 6272082811234547218131727)
        ·
          refine ⟨9408124216851820827197591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272082811234547218131727 9408124216851820827197591)
          ·
            refine ⟨14112186325277731240796387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408124216851820827197591 14112186325277731240796387)
            ·
              refine ⟨21168279487916596861194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14112186325277731240796387 21168279487916596861194581)
              ·
                refine ⟨62016443812255654866781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21168279487916596861194581 62016443812255654866781)
                ·
                  rfl

theorem cell23_3260968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 10].length) (baseStart_3260968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260968 prefixEnd_3260968 := by exact prefixLift 3260968
  have htrace : WordTrace (prefixWord ++ tailWord_3260968) baseStart_3260968 baseEnd_3260968 := by
    simpa [prefixWord, tailWord_3260968, baseEnd_3260968] using wordTrace_append hprefix tailTrace_3260968
  have hstable : (prefixWord ++ tailWord_3260968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260968).length < 2 ^ (prefixWord ++ tailWord_3260968).sum := by decide
  have hdescent : baseEnd_3260968 < baseStart_3260968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3260982 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3260982 : Nat := 118140960795 + 3260982 * 2 ^ 59
def prefixEnd_3260982 : Nat := 4983230072969 + 3 ^ 40 * 3260982 * 2
def baseEnd_3260982 : Nat := 1674451171660065626628023

theorem tailTrace_3260982 : CollatzResearch.WordTrace tailWord_3260982 prefixEnd_3260982 1674451171660065626628023 := by
  unfold tailWord_3260982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433611542001663764446075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79291856448017746820758133 7433611542001663764446075)
  ·
    refine ⟨11150417313002495646669113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7433611542001663764446075 11150417313002495646669113)
    ·
      refine ⟨8362812984751871735001835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11150417313002495646669113 8362812984751871735001835)
      ·
        refine ⟨12544219477127807602502753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362812984751871735001835 12544219477127807602502753)
        ·
          refine ⟨9408164607845855701877065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544219477127807602502753 9408164607845855701877065)
          ·
            refine ⟨7056123455884391776407799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9408164607845855701877065 7056123455884391776407799)
            ·
              refine ⟨10584185183826587664611699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056123455884391776407799 10584185183826587664611699)
              ·
                refine ⟨15876277775739881496917549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584185183826587664611699 15876277775739881496917549)
                ·
                  refine ⟨5953604165902455561344081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15876277775739881496917549 5953604165902455561344081)
                  ·
                    refine ⟨4465203124426841671008061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953604165902455561344081 4465203124426841671008061)
                    ·
                      refine ⟨1674451171660065626628023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465203124426841671008061 1674451171660065626628023)
                      ·
                        rfl

theorem cell23_3260982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3260982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3260982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3260982 prefixEnd_3260982 := by exact prefixLift 3260982
  have htrace : WordTrace (prefixWord ++ tailWord_3260982) baseStart_3260982 baseEnd_3260982 := by
    simpa [prefixWord, tailWord_3260982, baseEnd_3260982] using wordTrace_append hprefix tailTrace_3260982
  have hstable : (prefixWord ++ tailWord_3260982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3260982).length < 2 ^ (prefixWord ++ tailWord_3260982).sum := by decide
  have hdescent : baseEnd_3260982 < baseStart_3260982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3260982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261012 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3261012 : Nat := 118140960795 + 3261012 * 2 ^ 59
def prefixEnd_3261012 : Nat := 4983230072969 + 3 ^ 40 * 3261012 * 2
def baseEnd_3261012 : Nat := 1674466576079700509252885

theorem tailTrace_3261012 : CollatzResearch.WordTrace tailWord_3261012 prefixEnd_3261012 1674466576079700509252885 := by
  unfold tailWord_3261012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59469439430958967677364645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79292585907945290236486193 59469439430958967677364645)
  ·
    refine ⟨11150519893304806439505871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59469439430958967677364645 11150519893304806439505871)
    ·
      refine ⟨16725779839957209659258807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150519893304806439505871 16725779839957209659258807)
      ·
        refine ⟨25088669759935814488888211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16725779839957209659258807 25088669759935814488888211)
        ·
          refine ⟨37633004639903721733332317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25088669759935814488888211 37633004639903721733332317)
          ·
            refine ⟨14112376739963895649999619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37633004639903721733332317 14112376739963895649999619)
            ·
              refine ⟨21168565109945843474999429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14112376739963895649999619 21168565109945843474999429)
              ·
                refine ⟨3969105958114845651562393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21168565109945843474999429 3969105958114845651562393)
                ·
                  refine ⟨2976829468586134238671795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969105958114845651562393 2976829468586134238671795)
                  ·
                    refine ⟨4465244202879201358007693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2976829468586134238671795 4465244202879201358007693)
                    ·
                      refine ⟨1674466576079700509252885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465244202879201358007693 1674466576079700509252885)
                      ·
                        rfl

theorem cell23_3261012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3261012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261012 prefixEnd_3261012 := by exact prefixLift 3261012
  have htrace : WordTrace (prefixWord ++ tailWord_3261012) baseStart_3261012 baseEnd_3261012 := by
    simpa [prefixWord, tailWord_3261012, baseEnd_3261012] using wordTrace_append hprefix tailTrace_3261012
  have hstable : (prefixWord ++ tailWord_3261012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261012).length < 2 ^ (prefixWord ++ tailWord_3261012).sum := by decide
  have hdescent : baseEnd_3261012 < baseStart_3261012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261028 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3261028 : Nat := 118140960795 + 3261028 * 2 ^ 59
def prefixEnd_3261028 : Nat := 4983230072969 + 3 ^ 40 * 3261028 * 2
def baseEnd_3261028 : Nat := 558158263923390815550937

theorem tailTrace_3261028 : CollatzResearch.WordTrace tailWord_3261028 prefixEnd_3261028 558158263923390815550937 := by
  unfold tailWord_3261028
  simp only [CollatzResearch.WordTrace]
  refine ⟨59469731214929985043655869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79292974953239980058207825 59469731214929985043655869)
  ·
    refine ⟨22301149205598744391370951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59469731214929985043655869 22301149205598744391370951)
    ·
      refine ⟨33451723808398116587056427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22301149205598744391370951 33451723808398116587056427)
      ·
        refine ⟨50177585712597174880584641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33451723808398116587056427 50177585712597174880584641)
        ·
          refine ⟨37633189284447881160438481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50177585712597174880584641 37633189284447881160438481)
          ·
            refine ⟨28224891963335910870328861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37633189284447881160438481 28224891963335910870328861)
            ·
              refine ⟨10584334486250966576373323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28224891963335910870328861 10584334486250966576373323)
              ·
                refine ⟨15876501729376449864559985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584334486250966576373323 15876501729376449864559985)
                ·
                  refine ⟨11907376297032337398419989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15876501729376449864559985 11907376297032337398419989)
                  ·
                    refine ⟨558158263923390815550937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11907376297032337398419989 558158263923390815550937)
                    ·
                      rfl

theorem cell23_3261028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3261028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261028 prefixEnd_3261028 := by exact prefixLift 3261028
  have htrace : WordTrace (prefixWord ++ tailWord_3261028) baseStart_3261028 baseEnd_3261028 := by
    simpa [prefixWord, tailWord_3261028, baseEnd_3261028] using wordTrace_append hprefix tailTrace_3261028
  have hstable : (prefixWord ++ tailWord_3261028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261028).length < 2 ^ (prefixWord ++ tailWord_3261028).sum := by decide
  have hdescent : baseEnd_3261028 < baseStart_3261028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261085 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3261085 : Nat := 118140960795 + 3261085 * 2 ^ 59
def prefixEnd_3261085 : Nat := 4983230072969 + 3 ^ 40 * 3261085 * 2
def baseEnd_3261085 : Nat := 1674504060167478723640049

theorem tailTrace_3261085 : CollatzResearch.WordTrace tailWord_3261085 prefixEnd_3261085 1674504060167478723640049 := by
  unfold tailWord_3261085
  simp only [CollatzResearch.WordTrace]
  refine ⟨118941541390653468822136709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79294360927102312548091139 118941541390653468822136709)
  ·
    refine ⟨22301539010747525404150633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118941541390653468822136709 22301539010747525404150633)
    ·
      refine ⟨16726154258060644053112975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22301539010747525404150633 16726154258060644053112975)
      ·
        refine ⟨25089231387090966079669463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16726154258060644053112975 25089231387090966079669463)
        ·
          refine ⟨37633847080636449119504195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25089231387090966079669463 37633847080636449119504195)
          ·
            refine ⟨56450770620954673679256293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37633847080636449119504195 56450770620954673679256293)
            ·
              refine ⟨10584519491429001314860555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56450770620954673679256293 10584519491429001314860555)
              ·
                refine ⟨15876779237143501972290833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584519491429001314860555 15876779237143501972290833)
                ·
                  refine ⟨11907584427857626479218125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15876779237143501972290833 11907584427857626479218125)
                  ·
                    refine ⟨4465344160446609929706797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11907584427857626479218125 4465344160446609929706797)
                    ·
                      refine ⟨1674504060167478723640049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465344160446609929706797 1674504060167478723640049)
                      ·
                        rfl

theorem cell23_3261085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3261085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261085 prefixEnd_3261085 := by exact prefixLift 3261085
  have htrace : WordTrace (prefixWord ++ tailWord_3261085) baseStart_3261085 baseEnd_3261085 := by
    simpa [prefixWord, tailWord_3261085, baseEnd_3261085] using wordTrace_append hprefix tailTrace_3261085
  have hstable : (prefixWord ++ tailWord_3261085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261085).length < 2 ^ (prefixWord ++ tailWord_3261085).sum := by decide
  have hdescent : baseEnd_3261085 < baseStart_3261085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261109 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 5]
def baseStart_3261109 : Nat := 118140960795 + 3261109 * 2 ^ 59
def prefixEnd_3261109 : Nat := 4983230072969 + 3 ^ 40 * 3261109 * 2
def baseEnd_3261109 : Nat := 186057375967020736637771

theorem tailTrace_3261109 : CollatzResearch.WordTrace tailWord_3261109 prefixEnd_3261109 186057375967020736637771 := by
  unfold tailWord_3261109
  simp only [CollatzResearch.WordTrace]
  refine ⟨118942416742566520921010381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79294944495044347280673587 118942416742566520921010381)
  ·
    refine ⟨44603406278462445345378893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118942416742566520921010381 44603406278462445345378893)
    ·
      refine ⟨16726277354423417004517085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44603406278462445345378893 16726277354423417004517085)
      ·
        refine ⟨6272354007908781376693907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16726277354423417004517085 6272354007908781376693907)
        ·
          refine ⟨9408531011863172065040861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272354007908781376693907 9408531011863172065040861)
          ·
            refine ⟨3528199129448689524390323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9408531011863172065040861 3528199129448689524390323)
            ·
              refine ⟨5292298694173034286585485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528199129448689524390323 5292298694173034286585485)
              ·
                refine ⟨1984612010314887857469557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5292298694173034286585485 1984612010314887857469557)
                ·
                  refine ⟨186057375967020736637771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984612010314887857469557 186057375967020736637771)
                  ·
                    rfl

theorem cell23_3261109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_3261109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261109 prefixEnd_3261109 := by exact prefixLift 3261109
  have htrace : WordTrace (prefixWord ++ tailWord_3261109) baseStart_3261109 baseEnd_3261109 := by
    simpa [prefixWord, tailWord_3261109, baseEnd_3261109] using wordTrace_append hprefix tailTrace_3261109
  have hstable : (prefixWord ++ tailWord_3261109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261109).length < 2 ^ (prefixWord ++ tailWord_3261109).sum := by decide
  have hdescent : baseEnd_3261109 < baseStart_3261109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261126 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3261126 : Nat := 118140960795 + 3261126 * 2 ^ 59
def prefixEnd_3261126 : Nat := 4983230072969 + 3 ^ 40 * 3261126 * 2
def baseEnd_3261126 : Nat := 186058345874923673691929

theorem tailTrace_3261126 : CollatzResearch.WordTrace tailWord_3261126 prefixEnd_3261126 186058345874923673691929 := by
  unfold tailWord_3261126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716969899484529150761851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79295357855669955216252821 3716969899484529150761851)
  ·
    refine ⟨5575454849226793726142777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3716969899484529150761851 5575454849226793726142777)
    ·
      refine ⟨4181591136920095294607083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5575454849226793726142777 4181591136920095294607083)
      ·
        refine ⟨6272386705380142941910625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181591136920095294607083 6272386705380142941910625)
        ·
          refine ⟨4704290029035107206432969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6272386705380142941910625 4704290029035107206432969)
          ·
            refine ⟨3528217521776330404824727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704290029035107206432969 3528217521776330404824727)
            ·
              refine ⟨5292326282664495607237091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528217521776330404824727 5292326282664495607237091)
              ·
                refine ⟨7938489423996743410855637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292326282664495607237091 7938489423996743410855637)
                ·
                  refine ⟨186058345874923673691929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7938489423996743410855637 186058345874923673691929)
                  ·
                    rfl

theorem cell23_3261126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3261126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261126 prefixEnd_3261126 := by exact prefixLift 3261126
  have htrace : WordTrace (prefixWord ++ tailWord_3261126) baseStart_3261126 baseEnd_3261126 := by
    simpa [prefixWord, tailWord_3261126, baseEnd_3261126] using wordTrace_append hprefix tailTrace_3261126
  have hstable : (prefixWord ++ tailWord_3261126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261126).length < 2 ^ (prefixWord ++ tailWord_3261126).sum := by decide
  have hdescent : baseEnd_3261126 < baseStart_3261126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261145 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_3261145 : Nat := 118140960795 + 3261145 * 2 ^ 59
def prefixEnd_3261145 : Nat := 4983230072969 + 3 ^ 40 * 3261145 * 2
def baseEnd_3261145 : Nat := 1674534869006748488889773

theorem tailTrace_3261145 : CollatzResearch.WordTrace tailWord_3261145 prefixEnd_3261145 1674534869006748488889773 := by
  unfold tailWord_3261145
  simp only [CollatzResearch.WordTrace]
  refine ⟨118943729770436099069320889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79295819846957399379547259 118943729770436099069320889)
  ·
    refine ⟨89207797327827074301990667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118943729770436099069320889 89207797327827074301990667)
    ·
      refine ⟨133811695991740611452986001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89207797327827074301990667 133811695991740611452986001)
      ·
        refine ⟨100358771993805458589739501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133811695991740611452986001 100358771993805458589739501)
        ·
          refine ⟨37634539497677046971152313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100358771993805458589739501 37634539497677046971152313)
          ·
            refine ⟨28225904623257785228364235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37634539497677046971152313 28225904623257785228364235)
            ·
              refine ⟨42338856934886677842546353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28225904623257785228364235 42338856934886677842546353)
              ·
                refine ⟨31754142701165008381909765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42338856934886677842546353 31754142701165008381909765)
                ·
                  refine ⟨5953901756468439071608081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31754142701165008381909765 5953901756468439071608081)
                  ·
                    refine ⟨4465426317351329303706061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953901756468439071608081 4465426317351329303706061)
                    ·
                      refine ⟨1674534869006748488889773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465426317351329303706061 1674534869006748488889773)
                      ·
                        rfl

theorem cell23_3261145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_3261145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261145 prefixEnd_3261145 := by exact prefixLift 3261145
  have htrace : WordTrace (prefixWord ++ tailWord_3261145) baseStart_3261145 baseEnd_3261145 := by
    simpa [prefixWord, tailWord_3261145, baseEnd_3261145] using wordTrace_append hprefix tailTrace_3261145
  have hstable : (prefixWord ++ tailWord_3261145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261145).length < 2 ^ (prefixWord ++ tailWord_3261145).sum := by decide
  have hdescent : baseEnd_3261145 < baseStart_3261145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261182 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_3261182 : Nat := 118140960795 + 3261182 * 2 ^ 59
def prefixEnd_3261182 : Nat := 4983230072969 + 3 ^ 40 * 3261182 * 2
def baseEnd_3261182 : Nat := 186061540865662760458567

theorem tailTrace_3261182 : CollatzResearch.WordTrace tailWord_3261182 prefixEnd_3261182 186061540865662760458567 := by
  unfold tailWord_3261182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868134908912756798552225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79296719514201369592278533 14868134908912756798552225)
  ·
    refine ⟨11151101181684567598914169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14868134908912756798552225 11151101181684567598914169)
    ·
      refine ⟨8363325886263425699185627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11151101181684567598914169 8363325886263425699185627)
      ·
        refine ⟨12544988829395138548778441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363325886263425699185627 12544988829395138548778441)
        ·
          refine ⟨9408741622046353911583831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544988829395138548778441 9408741622046353911583831)
          ·
            refine ⟨14113112433069530867375747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408741622046353911583831 14113112433069530867375747)
            ·
              refine ⟨21169668649604296301063621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14113112433069530867375747 21169668649604296301063621)
              ·
                refine ⟨3969312871800805556449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21169668649604296301063621 3969312871800805556449429)
                ·
                  refine ⟨186061540865662760458567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3969312871800805556449429 186061540865662760458567)
                  ·
                    rfl

theorem cell23_3261182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_3261182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261182 prefixEnd_3261182 := by exact prefixLift 3261182
  have htrace : WordTrace (prefixWord ++ tailWord_3261182) baseStart_3261182 baseEnd_3261182 := by
    simpa [prefixWord, tailWord_3261182, baseEnd_3261182] using wordTrace_append hprefix tailTrace_3261182
  have hstable : (prefixWord ++ tailWord_3261182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261182).length < 2 ^ (prefixWord ++ tailWord_3261182).sum := by decide
  have hdescent : baseEnd_3261182 < baseStart_3261182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261186 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3261186 : Nat := 118140960795 + 3261186 * 2 ^ 59
def prefixEnd_3261186 : Nat := 4983230072969 + 3 ^ 40 * 3261186 * 2
def baseEnd_3261186 : Nat := 558185307237860942825695

theorem tailTrace_3261186 : CollatzResearch.WordTrace tailWord_3261186 prefixEnd_3261186 558185307237860942825695 := by
  unfold tailWord_3261186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29736306290821890767890853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79296816775525042047708941 29736306290821890767890853)
  ·
    refine ⟨5575557429529104518979535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29736306290821890767890853 5575557429529104518979535)
    ·
      refine ⟨8363336144293656778469303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5575557429529104518979535 8363336144293656778469303)
      ·
        refine ⟨12545004216440485167703955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363336144293656778469303 12545004216440485167703955)
        ·
          refine ⟨18817506324660727751555933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12545004216440485167703955 18817506324660727751555933)
          ·
            refine ⟨7056564871747772906833475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18817506324660727751555933 7056564871747772906833475)
            ·
              refine ⟨10584847307621659360250213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056564871747772906833475 10584847307621659360250213)
              ·
                refine ⟨1984658870179061130046915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10584847307621659360250213 1984658870179061130046915)
                ·
                  refine ⟨2976988305268591695070373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984658870179061130046915 2976988305268591695070373)
                  ·
                    refine ⟨558185307237860942825695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976988305268591695070373 558185307237860942825695)
                    ·
                      rfl

theorem cell23_3261186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3261186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261186 prefixEnd_3261186 := by exact prefixLift 3261186
  have htrace : WordTrace (prefixWord ++ tailWord_3261186) baseStart_3261186 baseEnd_3261186 := by
    simpa [prefixWord, tailWord_3261186, baseEnd_3261186] using wordTrace_append hprefix tailTrace_3261186
  have hstable : (prefixWord ++ tailWord_3261186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261186).length < 2 ^ (prefixWord ++ tailWord_3261186).sum := by decide
  have hdescent : baseEnd_3261186 < baseStart_3261186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261213 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3261213 : Nat := 118140960795 + 3261213 * 2 ^ 59
def prefixEnd_3261213 : Nat := 4983230072969 + 3 ^ 40 * 3261213 * 2
def baseEnd_3261213 : Nat := 1674569785691254222839461

theorem tailTrace_3261213 : CollatzResearch.WordTrace tailWord_3261213 prefixEnd_3261213 1674569785691254222839461 := by
  unfold tailWord_3261213
  simp only [CollatzResearch.WordTrace]
  refine ⟨118946209934189746682796293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79297473289459831121864195 118946209934189746682796293)
  ·
    refine ⟨22302414362660577503024305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118946209934189746682796293 22302414362660577503024305)
    ·
      refine ⟨16726810771995433127268229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22302414362660577503024305 16726810771995433127268229)
      ·
        refine ⟨3136277019749143711362793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16726810771995433127268229 3136277019749143711362793)
        ·
          refine ⟨2352207764811857783522095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136277019749143711362793 2352207764811857783522095)
          ·
            refine ⟨3528311647217786675283143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352207764811857783522095 3528311647217786675283143)
            ·
              refine ⟨5292467470826680012924715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528311647217786675283143 5292467470826680012924715)
              ·
                refine ⟨7938701206240020019387073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292467470826680012924715 7938701206240020019387073)
                ·
                  refine ⟨5954025904680015014540305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938701206240020019387073 5954025904680015014540305)
                  ·
                    refine ⟨4465519428510011260905229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954025904680015014540305 4465519428510011260905229)
                    ·
                      refine ⟨1674569785691254222839461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465519428510011260905229 1674569785691254222839461)
                      ·
                        rfl

theorem cell23_3261213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3261213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261213 prefixEnd_3261213 := by exact prefixLift 3261213
  have htrace : WordTrace (prefixWord ++ tailWord_3261213) baseStart_3261213 baseEnd_3261213 := by
    simpa [prefixWord, tailWord_3261213, baseEnd_3261213] using wordTrace_append hprefix tailTrace_3261213
  have hstable : (prefixWord ++ tailWord_3261213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261213).length < 2 ^ (prefixWord ++ tailWord_3261213).sum := by decide
  have hdescent : baseEnd_3261213 < baseStart_3261213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261225 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_3261225 : Nat := 118140960795 + 3261225 * 2 ^ 59
def prefixEnd_3261225 : Nat := 4983230072969 + 3 ^ 40 * 3261225 * 2
def baseEnd_3261225 : Nat := 558191982486369391963135

theorem tailTrace_3261225 : CollatzResearch.WordTrace tailWord_3261225 prefixEnd_3261225 558191982486369391963135 := by
  unfold tailWord_3261225
  simp only [CollatzResearch.WordTrace]
  refine ⟨118946647610146272732233129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79297765073430848488155419 118946647610146272732233129)
  ·
    refine ⟨89209985707609704549174847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118946647610146272732233129 89209985707609704549174847)
    ·
      refine ⟨133814978561414556823762271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89209985707609704549174847 133814978561414556823762271)
      ·
        refine ⟨200722467842121835235643407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133814978561414556823762271 200722467842121835235643407)
        ·
          refine ⟨301083701763182752853465111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200722467842121835235643407 301083701763182752853465111)
          ·
            refine ⟨451625552644774129280197667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301083701763182752853465111 451625552644774129280197667)
            ·
              refine ⟨677438328967161193920296501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451625552644774129280197667 677438328967161193920296501)
              ·
                refine ⟨63509843340671361930027797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677438328967161193920296501 63509843340671361930027797)
                ·
                  refine ⟨2977023906593970090470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63509843340671361930027797 2977023906593970090470053)
                  ·
                    refine ⟨558191982486369391963135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2977023906593970090470053 558191982486369391963135)
                    ·
                      rfl

theorem cell23_3261225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_3261225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261225 prefixEnd_3261225 := by exact prefixLift 3261225
  have htrace : WordTrace (prefixWord ++ tailWord_3261225) baseStart_3261225 baseEnd_3261225 := by
    simpa [prefixWord, tailWord_3261225, baseEnd_3261225] using wordTrace_append hprefix tailTrace_3261225
  have hstable : (prefixWord ++ tailWord_3261225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261225).length < 2 ^ (prefixWord ++ tailWord_3261225).sum := by decide
  have hdescent : baseEnd_3261225 < baseStart_3261225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261269 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3261269 : Nat := 118140960795 + 3261269 * 2 ^ 59
def prefixEnd_3261269 : Nat := 4983230072969 + 3 ^ 40 * 3261269 * 2
def baseEnd_3261269 : Nat := 1674598540607906003739203

theorem tailTrace_3261269 : CollatzResearch.WordTrace tailWord_3261269 prefixEnd_3261269 1674598540607906003739203 := by
  unfold tailWord_3261269
  simp only [CollatzResearch.WordTrace]
  refine ⟨118948252421986868246834861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79298834947991245497889907 118948252421986868246834861)
  ·
    refine ⟨44605594658245075592563073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118948252421986868246834861 44605594658245075592563073)
    ·
      refine ⟨33454195993683806694422305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44605594658245075592563073 33454195993683806694422305)
      ·
        refine ⟨25090646995262855020816729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33454195993683806694422305 25090646995262855020816729)
        ·
          refine ⟨18817985246447141265612547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25090646995262855020816729 18817985246447141265612547)
          ·
            refine ⟨28226977869670711898418821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18817985246447141265612547 28226977869670711898418821)
            ·
              refine ⟨5292558350563258480953529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28226977869670711898418821 5292558350563258480953529)
              ·
                refine ⟨3969418762922443860715147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292558350563258480953529 3969418762922443860715147)
                ·
                  refine ⟨5954128144383665791072721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969418762922443860715147 5954128144383665791072721)
                  ·
                    refine ⟨4465596108287749343304541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954128144383665791072721 4465596108287749343304541)
                    ·
                      refine ⟨1674598540607906003739203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4465596108287749343304541 1674598540607906003739203)
                      ·
                        rfl

theorem cell23_3261269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3261269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261269 prefixEnd_3261269 := by exact prefixLift 3261269
  have htrace : WordTrace (prefixWord ++ tailWord_3261269) baseStart_3261269 baseEnd_3261269 := by
    simpa [prefixWord, tailWord_3261269, baseEnd_3261269] using wordTrace_append hprefix tailTrace_3261269
  have hstable : (prefixWord ++ tailWord_3261269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261269).length < 2 ^ (prefixWord ++ tailWord_3261269).sum := by decide
  have hdescent : baseEnd_3261269 < baseStart_3261269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261283 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 1, 2, 2]
def baseStart_3261283 : Nat := 118140960795 + 3261283 * 2 ^ 59
def prefixEnd_3261283 : Nat := 4983230072969 + 3 ^ 40 * 3261283 * 2
def baseEnd_3261283 : Nat := 1674605729337068948964139

theorem tailTrace_3261283 : CollatzResearch.WordTrace tailWord_3261283 prefixEnd_3261283 1674605729337068948964139 := by
  unfold tailWord_3261283
  simp only [CollatzResearch.WordTrace]
  refine ⟨118948763043936148637844503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79299175362624099091896335 118948763043936148637844503)
  ·
    refine ⟨178423144565904222956766755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118948763043936148637844503 178423144565904222956766755)
    ·
      refine ⟨267634716848856334435150133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178423144565904222956766755 267634716848856334435150133)
      ·
        refine ⟨25090754704580281353295325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267634716848856334435150133 25090754704580281353295325)
        ·
          refine ⟨9409033014217605507485747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25090754704580281353295325 9409033014217605507485747)
          ·
            refine ⟨14113549521326408261228621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9409033014217605507485747 14113549521326408261228621)
            ·
              refine ⟨5292581070497403097960733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14113549521326408261228621 5292581070497403097960733)
              ·
                refine ⟨1984717901436526161735275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5292581070497403097960733 1984717901436526161735275)
                ·
                  refine ⟨2977076852154789242602913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984717901436526161735275 2977076852154789242602913)
                  ·
                    refine ⟨2232807639116091931952185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977076852154789242602913 2232807639116091931952185)
                    ·
                      refine ⟨1674605729337068948964139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232807639116091931952185 1674605729337068948964139)
                      ·
                        rfl

theorem cell23_3261283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_3261283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261283 prefixEnd_3261283 := by exact prefixLift 3261283
  have htrace : WordTrace (prefixWord ++ tailWord_3261283) baseStart_3261283 baseEnd_3261283 := by
    simpa [prefixWord, tailWord_3261283, baseEnd_3261283] using wordTrace_append hprefix tailTrace_3261283
  have hstable : (prefixWord ++ tailWord_3261283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261283).length < 2 ^ (prefixWord ++ tailWord_3261283).sum := by decide
  have hdescent : baseEnd_3261283 < baseStart_3261283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261310 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3261310 : Nat := 118140960795 + 3261310 * 2 ^ 59
def prefixEnd_3261310 : Nat := 4983230072969 + 3 ^ 40 * 3261310 * 2
def baseEnd_3261310 : Nat := 558206531104913447775505

theorem tailTrace_3261310 : CollatzResearch.WordTrace tailWord_3261310 prefixEnd_3261310 558206531104913447775505 := by
  unfold tailWord_3261310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868718476854791531134673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79299831876558888166051589 14868718476854791531134673)
  ·
    refine ⟨11151538857641093648351005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14868718476854791531134673 11151538857641093648351005)
    ·
      refine ⟨4181827071615410118131627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11151538857641093648351005 4181827071615410118131627)
      ·
        refine ⟨6272740607423115177197441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181827071615410118131627 6272740607423115177197441)
        ·
          refine ⟨4704555455567336382898081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6272740607423115177197441 4704555455567336382898081)
          ·
            refine ⟨3528416591675502287173561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704555455567336382898081 3528416591675502287173561)
            ·
              refine ⟨2646312443756626715380171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528416591675502287173561 2646312443756626715380171)
              ·
                refine ⟨3969468665634940073070257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646312443756626715380171 3969468665634940073070257)
                ·
                  refine ⟨2977101499226205054802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969468665634940073070257 2977101499226205054802693)
                  ·
                    refine ⟨558206531104913447775505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2977101499226205054802693 558206531104913447775505)
                    ·
                      rfl

theorem cell23_3261310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3261310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261310 prefixEnd_3261310 := by exact prefixLift 3261310
  have htrace : WordTrace (prefixWord ++ tailWord_3261310) baseStart_3261310 baseEnd_3261310 := by
    simpa [prefixWord, tailWord_3261310, baseEnd_3261310] using wordTrace_append hprefix tailTrace_3261310
  have hstable : (prefixWord ++ tailWord_3261310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261310).length < 2 ^ (prefixWord ++ tailWord_3261310).sum := by decide
  have hdescent : baseEnd_3261310 < baseStart_3261310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261315 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 8]
def baseStart_3261315 : Nat := 118140960795 + 3261315 * 2 ^ 59
def prefixEnd_3261315 : Nat := 4983230072969 + 3 ^ 40 * 3261315 * 2
def baseEnd_3261315 : Nat := 558207386906004274587997

theorem tailTrace_3261315 : CollatzResearch.WordTrace tailWord_3261315 prefixEnd_3261315 558207386906004274587997 := by
  unfold tailWord_3261315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118949930179820218103009399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79299953453213478735339599 118949930179820218103009399)
  ·
    refine ⟨178424895269730327154514099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118949930179820218103009399 178424895269730327154514099)
    ·
      refine ⟨267637342904595490731771149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178424895269730327154514099 267637342904595490731771149)
      ·
        refine ⟨100364003589223309024414181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267637342904595490731771149 100364003589223309024414181)
        ·
          refine ⟨18818250672979370442077659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100364003589223309024414181 18818250672979370442077659)
          ·
            refine ⟨28227376009469055663116489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18818250672979370442077659 28227376009469055663116489)
            ·
              refine ⟨21170532007101791747337367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28227376009469055663116489 21170532007101791747337367)
              ·
                refine ⟨31755798010652687621006051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21170532007101791747337367 31755798010652687621006051)
                ·
                  refine ⟨47633697015979031431509077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31755798010652687621006051 47633697015979031431509077)
                  ·
                    refine ⟨558207386906004274587997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47633697015979031431509077 558207386906004274587997)
                    ·
                      rfl

theorem cell23_3261315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_3261315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261315 prefixEnd_3261315 := by exact prefixLift 3261315
  have htrace : WordTrace (prefixWord ++ tailWord_3261315) baseStart_3261315 baseEnd_3261315 := by
    simpa [prefixWord, tailWord_3261315, baseEnd_3261315] using wordTrace_append hprefix tailTrace_3261315
  have hstable : (prefixWord ++ tailWord_3261315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261315).length < 2 ^ (prefixWord ++ tailWord_3261315).sum := by decide
  have hdescent : baseEnd_3261315 < baseStart_3261315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261343 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3261343 : Nat := 118140960795 + 3261343 * 2 ^ 59
def prefixEnd_3261343 : Nat := 4983230072969 + 3 ^ 40 * 3261343 * 2
def baseEnd_3261343 : Nat := 1674636538176338714213863

theorem tailTrace_3261343 : CollatzResearch.WordTrace tailWord_3261343 prefixEnd_3261343 1674636538176338714213863 := by
  unfold tailWord_3261343
  simp only [CollatzResearch.WordTrace]
  refine ⟨118950951423718778885028683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79300634282479185923352455 118950951423718778885028683)
  ·
    refine ⟨178426427135578168327543025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118950951423718778885028683 178426427135578168327543025)
    ·
      refine ⟨133819820351683626245657269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178426427135578168327543025 133819820351683626245657269)
      ·
        refine ⟨12545608157970339960530369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133819820351683626245657269 12545608157970339960530369)
        ·
          refine ⟨9409206118477754970397777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12545608157970339960530369 9409206118477754970397777)
          ·
            refine ⟨7056904588858316227798333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409206118477754970397777 7056904588858316227798333)
            ·
              refine ⟨2646339220821868585424375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7056904588858316227798333 2646339220821868585424375)
              ·
                refine ⟨3969508831232802878136563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646339220821868585424375 3969508831232802878136563)
                ·
                  refine ⟨5954263246849204317204845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969508831232802878136563 5954263246849204317204845)
                  ·
                    refine ⟨2232848717568451618951817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5954263246849204317204845 2232848717568451618951817)
                    ·
                      refine ⟨1674636538176338714213863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232848717568451618951817 1674636538176338714213863)
                      ·
                        rfl

theorem cell23_3261343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3261343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261343 prefixEnd_3261343 := by exact prefixLift 3261343
  have htrace : WordTrace (prefixWord ++ tailWord_3261343) baseStart_3261343 baseEnd_3261343 := by
    simpa [prefixWord, tailWord_3261343, baseEnd_3261343] using wordTrace_append hprefix tailTrace_3261343
  have hstable : (prefixWord ++ tailWord_3261343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261343).length < 2 ^ (prefixWord ++ tailWord_3261343).sum := by decide
  have hdescent : baseEnd_3261343 < baseStart_3261343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261396 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3261396 : Nat := 118140960795 + 3261396 * 2 ^ 59
def prefixEnd_3261396 : Nat := 4983230072969 + 3 ^ 40 * 3261396 * 2
def baseEnd_3261396 : Nat := 186073750294558556316791

theorem tailTrace_3261396 : CollatzResearch.WordTrace tailWord_3261396 prefixEnd_3261396 186073750294558556316791 := by
  unfold tailWord_3261396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59476442246263384468354021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79301922995017845957805361 59476442246263384468354021)
  ·
    refine ⟨11151832921174384587816379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59476442246263384468354021 11151832921174384587816379)
    ·
      refine ⟨16727749381761576881724569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11151832921174384587816379 16727749381761576881724569)
      ·
        refine ⟨12545812036321182661293427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16727749381761576881724569 12545812036321182661293427)
        ·
          refine ⟨18818718054481773991940141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12545812036321182661293427 18818718054481773991940141)
          ·
            refine ⟨7057019270430665246977553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18818718054481773991940141 7057019270430665246977553)
            ·
              refine ⟨5292764452822998935233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057019270430665246977553 5292764452822998935233165)
              ·
                refine ⟨1984786669808624600712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5292764452822998935233165 1984786669808624600712437)
                ·
                  refine ⟨186073750294558556316791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984786669808624600712437 186073750294558556316791)
                  ·
                    rfl

theorem cell23_3261396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3261396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261396 prefixEnd_3261396 := by exact prefixLift 3261396
  have htrace : WordTrace (prefixWord ++ tailWord_3261396) baseStart_3261396 baseEnd_3261396 := by
    simpa [prefixWord, tailWord_3261396, baseEnd_3261396] using wordTrace_append hprefix tailTrace_3261396
  have hstable : (prefixWord ++ tailWord_3261396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261396).length < 2 ^ (prefixWord ++ tailWord_3261396).sum := by decide
  have hdescent : baseEnd_3261396 < baseStart_3261396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261452 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 8]
def baseStart_3261452 : Nat := 118140960795 + 3261452 * 2 ^ 59
def prefixEnd_3261452 : Nat := 4983230072969 + 3 ^ 40 * 3261452 * 2
def baseEnd_3261452 : Nat := 186076945285297643083429

theorem tailTrace_3261452 : CollatzResearch.WordTrace tailWord_3261452 prefixEnd_3261452 186076945285297643083429 := by
  unfold tailWord_3261452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477463490161945250373305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79303284653549260333831073 59477463490161945250373305)
  ·
    refine ⟨44608097617621458937779979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59477463490161945250373305 44608097617621458937779979)
    ·
      refine ⟨66912146426432188406669969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44608097617621458937779979 66912146426432188406669969)
      ·
        refine ⟨50184109819824141305002477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66912146426432188406669969 50184109819824141305002477)
        ·
          refine ⟨18819041182434052989375929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50184109819824141305002477 18819041182434052989375929)
          ·
            refine ⟨14114280886825539742031947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18819041182434052989375929 14114280886825539742031947)
            ·
              refine ⟨21171421330238309613047921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14114280886825539742031947 21171421330238309613047921)
              ·
                refine ⟨15878565997678732209785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21171421330238309613047921 15878565997678732209785941)
                ·
                  refine ⟨186076945285297643083429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15878565997678732209785941 186076945285297643083429)
                  ·
                    rfl

theorem cell23_3261452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_3261452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261452 prefixEnd_3261452 := by exact prefixLift 3261452
  have htrace : WordTrace (prefixWord ++ tailWord_3261452) baseStart_3261452 baseEnd_3261452 := by
    simpa [prefixWord, tailWord_3261452, baseEnd_3261452] using wordTrace_append hprefix tailTrace_3261452
  have hstable : (prefixWord ++ tailWord_3261452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261452).length < 2 ^ (prefixWord ++ tailWord_3261452).sum := by decide
  have hdescent : baseEnd_3261452 < baseStart_3261452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261546 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3261546 : Nat := 118140960795 + 3261546 * 2 ^ 59
def prefixEnd_3261546 : Nat := 4983230072969 + 3 ^ 40 * 3261546 * 2
def baseEnd_3261546 : Nat := 558246924916400473325143

theorem tailTrace_3261546 : CollatzResearch.WordTrace tailWord_3261546 prefixEnd_3261546 558246924916400473325143 := by
  unfold tailWord_3261546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29739588860495836138667123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79305570294655563036445661 29739588860495836138667123)
  ·
    refine ⟨44609383290743754208000685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29739588860495836138667123 44609383290743754208000685)
    ·
      refine ⟨16728518734028907828000257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44609383290743754208000685 16728518734028907828000257)
      ·
        refine ⟨12546389050521680871000193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16728518734028907828000257 12546389050521680871000193)
        ·
          refine ⟨9409791787891260653250145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12546389050521680871000193 9409791787891260653250145)
          ·
            refine ⟨7057343840918445489937609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409791787891260653250145 7057343840918445489937609)
            ·
              refine ⟨5293007880688834117453207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057343840918445489937609 5293007880688834117453207)
              ·
                refine ⟨7939511821033251176179811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293007880688834117453207 7939511821033251176179811)
                ·
                  refine ⟨11909267731549876764269717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939511821033251176179811 11909267731549876764269717)
                  ·
                    refine ⟨558246924916400473325143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11909267731549876764269717 558246924916400473325143)
                    ·
                      rfl

theorem cell23_3261546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3261546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261546 prefixEnd_3261546 := by exact prefixLift 3261546
  have htrace : WordTrace (prefixWord ++ tailWord_3261546) baseStart_3261546 baseEnd_3261546 := by
    simpa [prefixWord, tailWord_3261546, baseEnd_3261546] using wordTrace_append hprefix tailTrace_3261546
  have hstable : (prefixWord ++ tailWord_3261546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261546).length < 2 ^ (prefixWord ++ tailWord_3261546).sum := by decide
  have hdescent : baseEnd_3261546 < baseStart_3261546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261557 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3261557 : Nat := 118140960795 + 3261557 * 2 ^ 59
def prefixEnd_3261557 : Nat := 4983230072969 + 3 ^ 40 * 3261557 * 2
def baseEnd_3261557 : Nat := 1674746423036400876937879

theorem tailTrace_3261557 : CollatzResearch.WordTrace tailWord_3261557 prefixEnd_3261557 1674746423036400876937879 := by
  unfold tailWord_3261557
  simp only [CollatzResearch.WordTrace]
  refine ⟨118958756644943493433318925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79305837763295662288879283 118958756644943493433318925)
  ·
    refine ⟨44609533741853810037494597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118958756644943493433318925 44609533741853810037494597)
    ·
      refine ⟨8364287576597589382030237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44609533741853810037494597 8364287576597589382030237)
      ·
        refine ⟨3136607841224096018261339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8364287576597589382030237 3136607841224096018261339)
        ·
          refine ⟨4704911761836144027392009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136607841224096018261339 4704911761836144027392009)
          ·
            refine ⟨3528683821377108020544007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704911761836144027392009 3528683821377108020544007)
            ·
              refine ⟨5293025732065662030816011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528683821377108020544007 5293025732065662030816011)
              ·
                refine ⟨7939538598098493046224017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293025732065662030816011 7939538598098493046224017)
                ·
                  refine ⟨5954653948573869784668013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939538598098493046224017 5954653948573869784668013)
                  ·
                    refine ⟨2232995230715201169250505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5954653948573869784668013 2232995230715201169250505)
                    ·
                      refine ⟨1674746423036400876937879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2232995230715201169250505 1674746423036400876937879)
                      ·
                        rfl

theorem cell23_3261557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3261557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261557 prefixEnd_3261557 := by exact prefixLift 3261557
  have htrace : WordTrace (prefixWord ++ tailWord_3261557) baseStart_3261557 baseEnd_3261557 := by
    simpa [prefixWord, tailWord_3261557, baseEnd_3261557] using wordTrace_append hprefix tailTrace_3261557
  have hstable : (prefixWord ++ tailWord_3261557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261557).length < 2 ^ (prefixWord ++ tailWord_3261557).sum := by decide
  have hdescent : baseEnd_3261557 < baseStart_3261557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261559 : List Nat := [1, 1, 3, 1, 1, 4, 5, 7]
def baseStart_3261559 : Nat := 118140960795 + 3261559 * 2 ^ 59
def prefixEnd_3261559 : Nat := 4983230072969 + 3 ^ 40 * 3261559 * 2
def baseEnd_3261559 : Nat := 62027683333248513670847

theorem tailTrace_3261559 : CollatzResearch.WordTrace tailWord_3261559 prefixEnd_3261559 62027683333248513670847 := by
  unfold tailWord_3261559
  simp only [CollatzResearch.WordTrace]
  refine ⟨118958829590936247774891731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79305886393957498516594487 118958829590936247774891731)
  ·
    refine ⟨178438244386404371662337597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118958829590936247774891731 178438244386404371662337597)
    ·
      refine ⟨66914341644901639373376599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178438244386404371662337597 66914341644901639373376599)
      ·
        refine ⟨100371512467352459060064899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66914341644901639373376599 100371512467352459060064899)
        ·
          refine ⟨150557268701028688590097349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100371512467352459060064899 150557268701028688590097349)
          ·
            refine ⟨28229487881442879110643253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150557268701028688590097349 28229487881442879110643253)
            ·
              refine ⟨2646514488885269916622805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28229487881442879110643253 2646514488885269916622805)
              ·
                refine ⟨62027683333248513670847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2646514488885269916622805 62027683333248513670847)
                ·
                  rfl

theorem cell23_3261559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 7].length) (baseStart_3261559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261559 prefixEnd_3261559 := by exact prefixLift 3261559
  have htrace : WordTrace (prefixWord ++ tailWord_3261559) baseStart_3261559 baseEnd_3261559 := by
    simpa [prefixWord, tailWord_3261559, baseEnd_3261559] using wordTrace_append hprefix tailTrace_3261559
  have hstable : (prefixWord ++ tailWord_3261559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261559).length < 2 ^ (prefixWord ++ tailWord_3261559).sum := by decide
  have hdescent : baseEnd_3261559 < baseStart_3261559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261573 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_3261573 : Nat := 118140960795 + 3261573 * 2 ^ 59
def prefixEnd_3261573 : Nat := 4983230072969 + 3 ^ 40 * 3261573 * 2
def baseEnd_3261573 : Nat := 1674754638726872814337805

theorem tailTrace_3261573 : CollatzResearch.WordTrace tailWord_3261573 prefixEnd_3261573 1674754638726872814337805 := by
  unfold tailWord_3261573
  simp only [CollatzResearch.WordTrace]
  refine ⟨118959340212885528165901373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79306226808590352110600915 118959340212885528165901373)
  ·
    refine ⟨44609752579832073062213015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118959340212885528165901373 44609752579832073062213015)
    ·
      refine ⟨66914628869748109593319523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44609752579832073062213015 66914628869748109593319523)
      ·
        refine ⟨100371943304622164389979285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66914628869748109593319523 100371943304622164389979285)
        ·
          refine ⟨4704934842404163955780279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100371943304622164389979285 4704934842404163955780279)
          ·
            refine ⟨7057402263606245933670419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704934842404163955780279 7057402263606245933670419)
            ·
              refine ⟨10586103395409368900505629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057402263606245933670419 10586103395409368900505629)
              ·
                refine ⟨3969788773278513337689611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10586103395409368900505629 3969788773278513337689611)
                ·
                  refine ⟨5954683159917770006534417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969788773278513337689611 5954683159917770006534417)
                  ·
                    refine ⟨4466012369938327504900813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954683159917770006534417 4466012369938327504900813)
                    ·
                      refine ⟨1674754638726872814337805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4466012369938327504900813 1674754638726872814337805)
                      ·
                        rfl

theorem cell23_3261573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_3261573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261573 prefixEnd_3261573 := by exact prefixLift 3261573
  have htrace : WordTrace (prefixWord ++ tailWord_3261573) baseStart_3261573 baseEnd_3261573 := by
    simpa [prefixWord, tailWord_3261573, baseEnd_3261573] using wordTrace_append hprefix tailTrace_3261573
  have hstable : (prefixWord ++ tailWord_3261573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261573).length < 2 ^ (prefixWord ++ tailWord_3261573).sum := by decide
  have hdescent : baseEnd_3261573 < baseStart_3261573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261626 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_3261626 : Nat := 118140960795 + 3261626 * 2 ^ 59
def prefixEnd_3261626 : Nat := 4983230072969 + 3 ^ 40 * 3261626 * 2
def baseEnd_3261626 : Nat := 1674781853201561106975061

theorem tailTrace_3261626 : CollatzResearch.WordTrace tailWord_3261626 prefixEnd_3261626 1674781853201561106975061 := by
  unfold tailWord_3261626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29740318320423379554395183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79307515521129012145053821 29740318320423379554395183)
  ·
    refine ⟨44610477480635069331592775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29740318320423379554395183 44610477480635069331592775)
    ·
      refine ⟨66915716220952603997389163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44610477480635069331592775 66915716220952603997389163)
      ·
        refine ⟨100373574331428905996083745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66915716220952603997389163 100373574331428905996083745)
        ·
          refine ⟨75280180748571679497062809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100373574331428905996083745 75280180748571679497062809)
          ·
            refine ⟨56460135561428759622797107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75280180748571679497062809 56460135561428759622797107)
            ·
              refine ⟨84690203342143139434195661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56460135561428759622797107 84690203342143139434195661)
              ·
                refine ⟨31758826253303677287823373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84690203342143139434195661 31758826253303677287823373)
                ·
                  refine ⟨11909559844988878982933765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31758826253303677287823373 11909559844988878982933765)
                  ·
                    refine ⟨2233042470935414809300081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11909559844988878982933765 2233042470935414809300081)
                    ·
                      refine ⟨1674781853201561106975061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233042470935414809300081 1674781853201561106975061)
                      ·
                        rfl

theorem cell23_3261626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_3261626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261626 prefixEnd_3261626 := by exact prefixLift 3261626
  have htrace : WordTrace (prefixWord ++ tailWord_3261626) baseStart_3261626 baseEnd_3261626 := by
    simpa [prefixWord, tailWord_3261626, baseEnd_3261626] using wordTrace_append hprefix tailTrace_3261626
  have hstable : (prefixWord ++ tailWord_3261626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261626).length < 2 ^ (prefixWord ++ tailWord_3261626).sum := by decide
  have hdescent : baseEnd_3261626 < baseStart_3261626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261629 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3261629 : Nat := 118140960795 + 3261629 * 2 ^ 59
def prefixEnd_3261629 : Nat := 4983230072969 + 3 ^ 40 * 3261629 * 2
def baseEnd_3261629 : Nat := 1674783393643524595237547

theorem tailTrace_3261629 : CollatzResearch.WordTrace tailWord_3261629 prefixEnd_3261629 1674783393643524595237547 := by
  unfold tailWord_3261629
  simp only [CollatzResearch.WordTrace]
  refine ⟨118961382700682649729939941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79307588467121766486626627 118961382700682649729939941)
  ·
    refine ⟨22305259256377996824363739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118961382700682649729939941 22305259256377996824363739)
    ·
      refine ⟨33457888884566995236545609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22305259256377996824363739 33457888884566995236545609)
      ·
        refine ⟨25093416663425246427409207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33457888884566995236545609 25093416663425246427409207)
        ·
          refine ⟨37640124995137869641113811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25093416663425246427409207 37640124995137869641113811)
          ·
            refine ⟨56460187492706804461670717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37640124995137869641113811 56460187492706804461670717)
            ·
              refine ⟨21172570309765051673126519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56460187492706804461670717 21172570309765051673126519)
              ·
                refine ⟨31758855464647577509689779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21172570309765051673126519 31758855464647577509689779)
                ·
                  refine ⟨47638283196971366264534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31758855464647577509689779 47638283196971366264534669)
                  ·
                    refine ⟨17864356198864262349200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47638283196971366264534669 17864356198864262349200501)
                    ·
                      refine ⟨1674783393643524595237547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17864356198864262349200501 1674783393643524595237547)
                      ·
                        rfl

theorem cell23_3261629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3261629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261629 prefixEnd_3261629 := by exact prefixLift 3261629
  have htrace : WordTrace (prefixWord ++ tailWord_3261629) baseStart_3261629 baseEnd_3261629 := by
    simpa [prefixWord, tailWord_3261629, baseEnd_3261629] using wordTrace_append hprefix tailTrace_3261629
  have hstable : (prefixWord ++ tailWord_3261629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261629).length < 2 ^ (prefixWord ++ tailWord_3261629).sum := by decide
  have hdescent : baseEnd_3261629 < baseStart_3261629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261630 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_3261630 : Nat := 118140960795 + 3261630 * 2 ^ 59
def prefixEnd_3261630 : Nat := 4983230072969 + 3 ^ 40 * 3261630 * 2
def baseEnd_3261630 : Nat := 1674783907124179091325043

theorem tailTrace_3261630 : CollatzResearch.WordTrace tailWord_3261630 prefixEnd_3261630 1674783907124179091325043 := by
  unfold tailWord_3261630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870177396709878362590793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79307612782452684600484229 14870177396709878362590793)
  ·
    refine ⟨11152633047532408771943095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14870177396709878362590793 11152633047532408771943095)
    ·
      refine ⟨16728949571298613157914643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152633047532408771943095 16728949571298613157914643)
      ·
        refine ⟨25093424356947919736871965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16728949571298613157914643 25093424356947919736871965)
        ·
          refine ⟨9410034133855469901326987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25093424356947919736871965 9410034133855469901326987)
          ·
            refine ⟨14115051200783204851990481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410034133855469901326987 14115051200783204851990481)
            ·
              refine ⟨10586288400587403638992861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14115051200783204851990481 10586288400587403638992861)
              ·
                refine ⟨3969858150220276364622323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10586288400587403638992861 3969858150220276364622323)
                ·
                  refine ⟨5954787225330414546933485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969858150220276364622323 5954787225330414546933485)
                  ·
                    refine ⟨2233045209498905455100057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5954787225330414546933485 2233045209498905455100057)
                    ·
                      refine ⟨1674783907124179091325043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233045209498905455100057 1674783907124179091325043)
                      ·
                        rfl

theorem cell23_3261630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_3261630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261630 prefixEnd_3261630 := by exact prefixLift 3261630
  have htrace : WordTrace (prefixWord ++ tailWord_3261630) baseStart_3261630 baseEnd_3261630 := by
    simpa [prefixWord, tailWord_3261630, baseEnd_3261630] using wordTrace_append hprefix tailTrace_3261630
  have hstable : (prefixWord ++ tailWord_3261630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261630).length < 2 ^ (prefixWord ++ tailWord_3261630).sum := by decide
  have hdescent : baseEnd_3261630 < baseStart_3261630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261638 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3261638 : Nat := 118140960795 + 3261638 * 2 ^ 59
def prefixEnd_3261638 : Nat := 4983230072969 + 3 ^ 40 * 3261638 * 2
def baseEnd_3261638 : Nat := 1674788014969415060025007

theorem tailTrace_3261638 : CollatzResearch.WordTrace tailWord_3261638 prefixEnd_3261638 1674788014969415060025007 := by
  unfold tailWord_3261638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717553467426563883344299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79307807305100029511345045 3717553467426563883344299)
  ·
    refine ⟨5576330201139845825016449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717553467426563883344299 5576330201139845825016449)
    ·
      refine ⟨4182247650854884368762337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5576330201139845825016449 4182247650854884368762337)
      ·
        refine ⟨3136685738141163276571753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182247650854884368762337 3136685738141163276571753)
        ·
          refine ⟨2352514303605872457428815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136685738141163276571753 2352514303605872457428815)
          ·
            refine ⟨3528771455408808686143223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352514303605872457428815 3528771455408808686143223)
            ·
              refine ⟨5293157183113213029214835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528771455408808686143223 5293157183113213029214835)
              ·
                refine ⟨7939735774669819543822253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293157183113213029214835 7939735774669819543822253)
                ·
                  refine ⟨2977400915501182328933345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7939735774669819543822253 2977400915501182328933345)
                  ·
                    refine ⟨2233050686625886746700009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977400915501182328933345 2233050686625886746700009)
                    ·
                      refine ⟨1674788014969415060025007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233050686625886746700009 1674788014969415060025007)
                      ·
                        rfl

theorem cell23_3261638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3261638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261638 prefixEnd_3261638 := by exact prefixLift 3261638
  have htrace : WordTrace (prefixWord ++ tailWord_3261638) baseStart_3261638 baseEnd_3261638 := by
    simpa [prefixWord, tailWord_3261638, baseEnd_3261638] using wordTrace_append hprefix tailTrace_3261638
  have hstable : (prefixWord ++ tailWord_3261638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261638).length < 2 ^ (prefixWord ++ tailWord_3261638).sum := by decide
  have hdescent : baseEnd_3261638 < baseStart_3261638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261639 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3261639 : Nat := 118140960795 + 3261639 * 2 ^ 59
def prefixEnd_3261639 : Nat := 4983230072969 + 3 ^ 40 * 3261639 * 2
def baseEnd_3261639 : Nat := 1674788528450069556112501

theorem tailTrace_3261639 : CollatzResearch.WordTrace tailWord_3261639 prefixEnd_3261639 1674788528450069556112501 := by
  unfold tailWord_3261639
  simp only [CollatzResearch.WordTrace]
  refine ⟨118961747430646421437803971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79307831620430947625202647 118961747430646421437803971)
  ·
    refine ⟨178442621145969632156705957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118961747430646421437803971 178442621145969632156705957)
    ·
      refine ⟨33457991464869306029382367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178442621145969632156705957 33457991464869306029382367)
      ·
        refine ⟨50186987197303959044073551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33457991464869306029382367 50186987197303959044073551)
        ·
          refine ⟨75280480795955938566110327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50186987197303959044073551 75280480795955938566110327)
          ·
            refine ⟨112920721193933907849165491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75280480795955938566110327 112920721193933907849165491)
            ·
              refine ⟨169381081790900861773748237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112920721193933907849165491 169381081790900861773748237)
              ·
                refine ⟨63517905671587823165155589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169381081790900861773748237 63517905671587823165155589)
                ·
                  refine ⟨11909607313422716843466673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63517905671587823165155589 11909607313422716843466673)
                  ·
                    refine ⟨8932205485067037632600005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11909607313422716843466673 8932205485067037632600005)
                    ·
                      refine ⟨1674788528450069556112501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8932205485067037632600005 1674788528450069556112501)
                      ·
                        rfl

theorem cell23_3261639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3261639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261639 prefixEnd_3261639 := by exact prefixLift 3261639
  have htrace : WordTrace (prefixWord ++ tailWord_3261639) baseStart_3261639 baseEnd_3261639 := by
    simpa [prefixWord, tailWord_3261639, baseEnd_3261639] using wordTrace_append hprefix tailTrace_3261639
  have hstable : (prefixWord ++ tailWord_3261639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261639).length < 2 ^ (prefixWord ++ tailWord_3261639).sum := by decide
  have hdescent : baseEnd_3261639 < baseStart_3261639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261689 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3261689 : Nat := 118140960795 + 3261689 * 2 ^ 59
def prefixEnd_3261689 : Nat := 4983230072969 + 3 ^ 40 * 3261689 * 2
def baseEnd_3261689 : Nat := 1674814202482794360487271

theorem tailTrace_3261689 : CollatzResearch.WordTrace tailWord_3261689 prefixEnd_3261689 1674814202482794360487271 := by
  unfold tailWord_3261689
  simp only [CollatzResearch.WordTrace]
  refine ⟨118963571080465279977124121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79309047386976853318082747 118963571080465279977124121)
  ·
    refine ⟨89222678310348959982843091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118963571080465279977124121 89222678310348959982843091)
    ·
      refine ⟨133834017465523439974264637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89222678310348959982843091 133834017465523439974264637)
      ·
        refine ⟨50187756549571289990349239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133834017465523439974264637 50187756549571289990349239)
        ·
          refine ⟨75281634824356934985523859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50187756549571289990349239 75281634824356934985523859)
          ·
            refine ⟨112922452236535402478285789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75281634824356934985523859 112922452236535402478285789)
            ·
              refine ⟨42345919588700775929357171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112922452236535402478285789 42345919588700775929357171)
              ·
                refine ⟨63518879383051163894035757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42345919588700775929357171 63518879383051163894035757)
                ·
                  refine ⟨23819579768644186460263409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63518879383051163894035757 23819579768644186460263409)
                  ·
                    refine ⟨17864684826483139845197557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23819579768644186460263409 17864684826483139845197557)
                    ·
                      refine ⟨1674814202482794360487271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17864684826483139845197557 1674814202482794360487271)
                      ·
                        rfl

theorem cell23_3261689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3261689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261689 prefixEnd_3261689 := by exact prefixLift 3261689
  have htrace : WordTrace (prefixWord ++ tailWord_3261689) baseStart_3261689 baseEnd_3261689 := by
    simpa [prefixWord, tailWord_3261689, baseEnd_3261689] using wordTrace_append hprefix tailTrace_3261689
  have hstable : (prefixWord ++ tailWord_3261689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261689).length < 2 ^ (prefixWord ++ tailWord_3261689).sum := by decide
  have hdescent : baseEnd_3261689 < baseStart_3261689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261700 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 5]
def baseStart_3261700 : Nat := 118140960795 + 3261700 * 2 ^ 59
def prefixEnd_3261700 : Nat := 4983230072969 + 3 ^ 40 * 3261700 * 2
def baseEnd_3261700 : Nat := 186091094529999313049969

theorem tailTrace_3261700 : CollatzResearch.WordTrace tailWord_3261700 prefixEnd_3261700 186091094529999313049969 := by
  unfold tailWord_3261700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59481986141712714427887277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79309314855616952570516369 59481986141712714427887277)
  ·
    refine ⟨22305744803142267910457729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59481986141712714427887277 22305744803142267910457729)
    ·
      refine ⟨16729308602356700932843297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22305744803142267910457729 16729308602356700932843297)
      ·
        refine ⟨12546981451767525699632473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16729308602356700932843297 12546981451767525699632473)
        ·
          refine ⟨9410236088825644274724355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12546981451767525699632473 9410236088825644274724355)
          ·
            refine ⟨14115354133238466412086533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410236088825644274724355 14115354133238466412086533)
            ·
              refine ⟨2646628899982212452266225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14115354133238466412086533 2646628899982212452266225)
              ·
                refine ⟨1984971674986659339199669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646628899982212452266225 1984971674986659339199669)
                ·
                  refine ⟨186091094529999313049969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984971674986659339199669 186091094529999313049969)
                  ·
                    rfl

theorem cell23_3261700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_3261700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261700 prefixEnd_3261700 := by exact prefixLift 3261700
  have htrace : WordTrace (prefixWord ++ tailWord_3261700) baseStart_3261700 baseEnd_3261700 := by
    simpa [prefixWord, tailWord_3261700, baseEnd_3261700] using wordTrace_append hprefix tailTrace_3261700
  have hstable : (prefixWord ++ tailWord_3261700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261700).length < 2 ^ (prefixWord ++ tailWord_3261700).sum := by decide
  have hdescent : baseEnd_3261700 < baseStart_3261700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261730 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3261730 : Nat := 118140960795 + 3261730 * 2 ^ 59
def prefixEnd_3261730 : Nat := 4983230072969 + 3 ^ 40 * 3261730 * 2
def baseEnd_3261730 : Nat := 558278418396542900024861

theorem tailTrace_3261730 : CollatzResearch.WordTrace tailWord_3261730 prefixEnd_3261730 558278418396542900024861 := by
  unfold tailWord_3261730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741266618329185994841661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79310044315544495986244429 29741266618329185994841661)
  ·
    refine ⟨11152974981873444748065623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29741266618329185994841661 11152974981873444748065623)
    ·
      refine ⟨16729462472810167122098435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152974981873444748065623 16729462472810167122098435)
      ·
        refine ⟨25094193709215250683147653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16729462472810167122098435 25094193709215250683147653)
        ·
          refine ⟨4705161320477859503090185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25094193709215250683147653 4705161320477859503090185)
          ·
            refine ⟨3528870990358394627317639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705161320477859503090185 3528870990358394627317639)
            ·
              refine ⟨5293306485537591940976459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528870990358394627317639 5293306485537591940976459)
              ·
                refine ⟨7939959728306387911464689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293306485537591940976459 7939959728306387911464689)
                ·
                  refine ⟨5954969796229790933598517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939959728306387911464689 5954969796229790933598517)
                  ·
                    refine ⟨558278418396542900024861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5954969796229790933598517 558278418396542900024861)
                    ·
                      rfl

theorem cell23_3261730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3261730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261730 prefixEnd_3261730 := by exact prefixLift 3261730
  have htrace : WordTrace (prefixWord ++ tailWord_3261730) baseStart_3261730 baseEnd_3261730 := by
    simpa [prefixWord, tailWord_3261730, baseEnd_3261730] using wordTrace_append hprefix tailTrace_3261730
  have hstable : (prefixWord ++ tailWord_3261730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261730).length < 2 ^ (prefixWord ++ tailWord_3261730).sum := by decide
  have hdescent : baseEnd_3261730 < baseStart_3261730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261733 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_3261733 : Nat := 118140960795 + 3261733 * 2 ^ 59
def prefixEnd_3261733 : Nat := 4983230072969 + 3 ^ 40 * 3261733 * 2
def baseEnd_3261733 : Nat := 1674836795631592188337069

theorem tailTrace_3261733 : CollatzResearch.WordTrace tailWord_3261733 prefixEnd_3261733 1674836795631592188337069 := by
  unfold tailWord_3261733
  simp only [CollatzResearch.WordTrace]
  refine ⟨118965175892305875491725853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79310117261537250327817235 118965175892305875491725853)
  ·
    refine ⟨44611940959614703309397195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118965175892305875491725853 44611940959614703309397195)
    ·
      refine ⟨66917911439422054964095793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44611940959614703309397195 66917911439422054964095793)
      ·
        refine ⟨50188433579566541223071845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66917911439422054964095793 50188433579566541223071845)
        ·
          refine ⟨9410331296168726479325971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50188433579566541223071845 9410331296168726479325971)
          ·
            refine ⟨14115496944253089718988957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410331296168726479325971 14115496944253089718988957)
            ·
              refine ⟨5293311354094908644620859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14115496944253089718988957 5293311354094908644620859)
              ·
                refine ⟨7939967031142362966931289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293311354094908644620859 7939967031142362966931289)
                ·
                  refine ⟨5954975273356772225198467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939967031142362966931289 5954975273356772225198467)
                  ·
                    refine ⟨8932462910035158337797701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954975273356772225198467 8932462910035158337797701)
                    ·
                      refine ⟨1674836795631592188337069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8932462910035158337797701 1674836795631592188337069)
                      ·
                        rfl

theorem cell23_3261733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_3261733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261733 prefixEnd_3261733 := by exact prefixLift 3261733
  have htrace : WordTrace (prefixWord ++ tailWord_3261733) baseStart_3261733 baseEnd_3261733 := by
    simpa [prefixWord, tailWord_3261733, baseEnd_3261733] using wordTrace_append hprefix tailTrace_3261733
  have hstable : (prefixWord ++ tailWord_3261733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261733).length < 2 ^ (prefixWord ++ tailWord_3261733).sum := by decide
  have hdescent : baseEnd_3261733 < baseStart_3261733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261746 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3261746 : Nat := 118140960795 + 3261746 * 2 ^ 59
def prefixEnd_3261746 : Nat := 4983230072969 + 3 ^ 40 * 3261746 * 2
def baseEnd_3261746 : Nat := 1674843470880100637474509

theorem tailTrace_3261746 : CollatzResearch.WordTrace tailWord_3261746 prefixEnd_3261746 1674843470880100637474509 := by
  unfold tailWord_3261746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741412510314694677987273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79310433360839185807966061 29741412510314694677987273)
  ·
    refine ⟨22306059382736021008490455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29741412510314694677987273 22306059382736021008490455)
    ·
      refine ⟨33459089074104031512735683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22306059382736021008490455 33459089074104031512735683)
      ·
        refine ⟨50188633611156047269103525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33459089074104031512735683 50188633611156047269103525)
        ·
          refine ⟨9410368802091758862956911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50188633611156047269103525 9410368802091758862956911)
          ·
            refine ⟨14115553203137638294435367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410368802091758862956911 14115553203137638294435367)
            ·
              refine ⟨21173329804706457441653051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14115553203137638294435367 21173329804706457441653051)
              ·
                refine ⟨31759994707059686162479577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21173329804706457441653051 31759994707059686162479577)
                ·
                  refine ⟨23819996030294764621859683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31759994707059686162479577 23819996030294764621859683)
                  ·
                    refine ⟨35729994045442146932789525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23819996030294764621859683 35729994045442146932789525)
                    ·
                      refine ⟨1674843470880100637474509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35729994045442146932789525 1674843470880100637474509)
                      ·
                        rfl

theorem cell23_3261746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3261746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261746 prefixEnd_3261746 := by exact prefixLift 3261746
  have htrace : WordTrace (prefixWord ++ tailWord_3261746) baseStart_3261746 baseEnd_3261746 := by
    simpa [prefixWord, tailWord_3261746, baseEnd_3261746] using wordTrace_append hprefix tailTrace_3261746
  have hstable : (prefixWord ++ tailWord_3261746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261746).length < 2 ^ (prefixWord ++ tailWord_3261746).sum := by decide
  have hdescent : baseEnd_3261746 < baseStart_3261746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261756 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 8]
def baseStart_3261756 : Nat := 118140960795 + 3261756 * 2 ^ 59
def prefixEnd_3261756 : Nat := 4983230072969 + 3 ^ 40 * 3261756 * 2
def baseEnd_3261756 : Nat := 186094289520738399816607

theorem tailTrace_3261756 : CollatzResearch.WordTrace tailWord_3261756 prefixEnd_3261756 186094289520738399816607 := by
  unfold tailWord_3261756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59483007385611275209906561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79310676514148366946542081 59483007385611275209906561)
  ·
    refine ⟨44612255539208456407429921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59483007385611275209906561 44612255539208456407429921)
    ·
      refine ⟨33459191654406342305572441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44612255539208456407429921 33459191654406342305572441)
      ·
        refine ⟨25094393740804756729179331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33459191654406342305572441 25094393740804756729179331)
        ·
          refine ⟨37641590611207135093768997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25094393740804756729179331 37641590611207135093768997)
          ·
            refine ⟨7057798239601337830081687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37641590611207135093768997 7057798239601337830081687)
            ·
              refine ⟨10586697359402006745122531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057798239601337830081687 10586697359402006745122531)
              ·
                refine ⟨15880046039103010117683797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10586697359402006745122531 15880046039103010117683797)
                ·
                  refine ⟨186094289520738399816607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15880046039103010117683797 186094289520738399816607)
                  ·
                    rfl

theorem cell23_3261756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_3261756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261756 prefixEnd_3261756 := by exact prefixLift 3261756
  have htrace : WordTrace (prefixWord ++ tailWord_3261756) baseStart_3261756 baseEnd_3261756 := by
    simpa [prefixWord, tailWord_3261756, baseEnd_3261756] using wordTrace_append hprefix tailTrace_3261756
  have hstable : (prefixWord ++ tailWord_3261756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261756).length < 2 ^ (prefixWord ++ tailWord_3261756).sum := by decide
  have hdescent : baseEnd_3261756 < baseStart_3261756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261786 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3261786 : Nat := 118140960795 + 3261786 * 2 ^ 59
def prefixEnd_3261786 : Nat := 4983230072969 + 3 ^ 40 * 3261786 * 2
def baseEnd_3261786 : Nat := 558288003368760160324775

theorem tailTrace_3261786 : CollatzResearch.WordTrace tailWord_3261786 prefixEnd_3261786 558288003368760160324775 := by
  unfold tailWord_3261786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741777240278466385851303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79311405974075910362270141 29741777240278466385851303)
  ·
    refine ⟨44612665860417699578776955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29741777240278466385851303 44612665860417699578776955)
    ·
      refine ⟨66918998790626549368165433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44612665860417699578776955 66918998790626549368165433)
      ·
        refine ⟨50189249092969912026124075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66918998790626549368165433 50189249092969912026124075)
        ·
          refine ⟨75283873639454868039186113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50189249092969912026124075 75283873639454868039186113)
          ·
            refine ⟨56462905229591151029389585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75283873639454868039186113 56462905229591151029389585)
            ·
              refine ⟨42347178922193363272042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56462905229591151029389585 42347178922193363272042189)
              ·
                refine ⟨15880192095822511227015821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42347178922193363272042189 15880192095822511227015821)
                ·
                  refine ⟨5955072035933441710130933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15880192095822511227015821 5955072035933441710130933)
                  ·
                    refine ⟨558288003368760160324775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5955072035933441710130933 558288003368760160324775)
                    ·
                      rfl

theorem cell23_3261786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3261786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261786 prefixEnd_3261786 := by exact prefixLift 3261786
  have htrace : WordTrace (prefixWord ++ tailWord_3261786) baseStart_3261786 baseEnd_3261786 := by
    simpa [prefixWord, tailWord_3261786, baseEnd_3261786] using wordTrace_append hprefix tailTrace_3261786
  have hstable : (prefixWord ++ tailWord_3261786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261786).length < 2 ^ (prefixWord ++ tailWord_3261786).sum := by decide
  have hdescent : baseEnd_3261786 < baseStart_3261786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261793 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_3261793 : Nat := 118140960795 + 3261793 * 2 ^ 59
def prefixEnd_3261793 : Nat := 4983230072969 + 3 ^ 40 * 3261793 * 2
def baseEnd_3261793 : Nat := 1674867604470861953586793

theorem tailTrace_3261793 : CollatzResearch.WordTrace tailWord_3261793 prefixEnd_3261793 1674867604470861953586793 := by
  unfold tailWord_3261793
  simp only [CollatzResearch.WordTrace]
  refine ⟨118967364272088505738910033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79311576181392337159273355 118967364272088505738910033)
  ·
    refine ⟨89225523204066379304182525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118967364272088505738910033 89225523204066379304182525)
    ·
      refine ⟨33459571201524892239068447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89225523204066379304182525 33459571201524892239068447)
      ·
        refine ⟨50189356802287338358602671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33459571201524892239068447 50189356802287338358602671)
        ·
          refine ⟨75284035203431007537904007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50189356802287338358602671 75284035203431007537904007)
          ·
            refine ⟨112926052805146511306856011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75284035203431007537904007 112926052805146511306856011)
            ·
              refine ⟨169389079207719766960284017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112926052805146511306856011 169389079207719766960284017)
              ·
                refine ⟨127041809405789825220213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169389079207719766960284017 127041809405789825220213013)
                ·
                  refine ⟨5955084815896398057197485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127041809405789825220213013 5955084815896398057197485)
                  ·
                    refine ⟨2233156805961149271449057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5955084815896398057197485 2233156805961149271449057)
                    ·
                      refine ⟨1674867604470861953586793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233156805961149271449057 1674867604470861953586793)
                      ·
                        rfl

theorem cell23_3261793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_3261793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261793 prefixEnd_3261793 := by exact prefixLift 3261793
  have htrace : WordTrace (prefixWord ++ tailWord_3261793) baseStart_3261793 baseEnd_3261793 := by
    simpa [prefixWord, tailWord_3261793, baseEnd_3261793] using wordTrace_append hprefix tailTrace_3261793
  have hstable : (prefixWord ++ tailWord_3261793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261793).length < 2 ^ (prefixWord ++ tailWord_3261793).sum := by decide
  have hdescent : baseEnd_3261793 < baseStart_3261793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261810 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3261810 : Nat := 118140960795 + 3261810 * 2 ^ 59
def prefixEnd_3261810 : Nat := 4983230072969 + 3 ^ 40 * 3261810 * 2
def baseEnd_3261810 : Nat := 1674876333641988387074215

theorem tailTrace_3261810 : CollatzResearch.WordTrace tailWord_3261810 prefixEnd_3261810 1674876333641988387074215 := by
  unfold tailWord_3261810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741996078256729410569721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79311989542017945094852589 29741996078256729410569721)
  ·
    refine ⟨22306497058692547057927291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29741996078256729410569721 22306497058692547057927291)
    ·
      refine ⟨33459745588038820586890937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22306497058692547057927291 33459745588038820586890937)
      ·
        refine ⟨25094809191029115440168203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33459745588038820586890937 25094809191029115440168203)
        ·
          refine ⟨37642213786543673160252305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25094809191029115440168203 37642213786543673160252305)
          ·
            refine ⟨28231660339907754870189229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37642213786543673160252305 28231660339907754870189229)
            ·
              refine ⟨10586872627465408076320961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28231660339907754870189229 10586872627465408076320961)
              ·
                refine ⟨7940154470599056057240721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10586872627465408076320961 7940154470599056057240721)
                ·
                  refine ⟨5955115852949292042930541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7940154470599056057240721 5955115852949292042930541)
                  ·
                    refine ⟨2233168444855984516098953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5955115852949292042930541 2233168444855984516098953)
                    ·
                      refine ⟨1674876333641988387074215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233168444855984516098953 1674876333641988387074215)
                      ·
                        rfl

theorem cell23_3261810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3261810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261810 prefixEnd_3261810 := by exact prefixLift 3261810
  have htrace : WordTrace (prefixWord ++ tailWord_3261810) baseStart_3261810 baseEnd_3261810 := by
    simpa [prefixWord, tailWord_3261810, baseEnd_3261810] using wordTrace_append hprefix tailTrace_3261810
  have hstable : (prefixWord ++ tailWord_3261810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261810).length < 2 ^ (prefixWord ++ tailWord_3261810).sum := by decide
  have hdescent : baseEnd_3261810 < baseStart_3261810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261836 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3261836 : Nat := 118140960795 + 3261836 * 2 ^ 59
def prefixEnd_3261836 : Nat := 4983230072969 + 3 ^ 40 * 3261836 * 2
def baseEnd_3261836 : Nat := 1674889684139005285349095

theorem tailTrace_3261836 : CollatzResearch.WordTrace tailWord_3261836 prefixEnd_3261836 1674889684139005285349095 := by
  unfold tailWord_3261836
  simp only [CollatzResearch.WordTrace]
  refine ⟨59484466305466362041362681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79312621740621816055150241 59484466305466362041362681)
  ·
    refine ⟨44613349729099771531022011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59484466305466362041362681 44613349729099771531022011)
    ·
      refine ⟨66920024593649657296533017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44613349729099771531022011 66920024593649657296533017)
      ·
        refine ⟨50190018445237242972399763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66920024593649657296533017 50190018445237242972399763)
        ·
          refine ⟨75285027667855864458599645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50190018445237242972399763 75285027667855864458599645)
          ·
            refine ⟨28231885375445949171974867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75285027667855864458599645 28231885375445949171974867)
            ·
              refine ⟨42347828063168923757962301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28231885375445949171974867 42347828063168923757962301)
              ·
                refine ⟨15880435523688346409235863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42347828063168923757962301 15880435523688346409235863)
                ·
                  refine ⟨23820653285532519613853795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15880435523688346409235863 23820653285532519613853795)
                  ·
                    refine ⟨35730979928298779420780693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23820653285532519613853795 35730979928298779420780693)
                    ·
                      refine ⟨1674889684139005285349095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35730979928298779420780693 1674889684139005285349095)
                      ·
                        rfl

theorem cell23_3261836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3261836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261836 prefixEnd_3261836 := by exact prefixLift 3261836
  have htrace : WordTrace (prefixWord ++ tailWord_3261836) baseStart_3261836 baseEnd_3261836 := by
    simpa [prefixWord, tailWord_3261836, baseEnd_3261836] using wordTrace_append hprefix tailTrace_3261836
  have hstable : (prefixWord ++ tailWord_3261836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261836).length < 2 ^ (prefixWord ++ tailWord_3261836).sum := by decide
  have hdescent : baseEnd_3261836 < baseStart_3261836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261853 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3261853 : Nat := 118140960795 + 3261853 * 2 ^ 59
def prefixEnd_3261853 : Nat := 4983230072969 + 3 ^ 40 * 3261853 * 2
def baseEnd_3261853 : Nat := 1674898413310131718836517

theorem tailTrace_3261853 : CollatzResearch.WordTrace tailWord_3261853 prefixEnd_3261853 1674898413310131718836517 := by
  unfold tailWord_3261853
  simp only [CollatzResearch.WordTrace]
  refine ⟨118969552651871135986094213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79313035101247423990729475 118969552651871135986094213)
  ·
    refine ⟨22306791122225837997392665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118969552651871135986094213 22306791122225837997392665)
    ·
      refine ⟨16730093341669378498044499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22306791122225837997392665 16730093341669378498044499)
      ·
        refine ⟨25095140012504067747066749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16730093341669378498044499 25095140012504067747066749)
        ·
          refine ⟨9410677504689025405150031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25095140012504067747066749 9410677504689025405150031)
          ·
            refine ⟨14116016257033538107725047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410677504689025405150031 14116016257033538107725047)
            ·
              refine ⟨21174024385550307161587571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116016257033538107725047 21174024385550307161587571)
              ·
                refine ⟨31761036578325460742381357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21174024385550307161587571 31761036578325460742381357)
                ·
                  refine ⟨11910388716872047778393009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31761036578325460742381357 11910388716872047778393009)
                  ·
                    refine ⟨8932791537654035833794757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11910388716872047778393009 8932791537654035833794757)
                    ·
                      refine ⟨1674898413310131718836517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8932791537654035833794757 1674898413310131718836517)
                      ·
                        rfl

theorem cell23_3261853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3261853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261853 prefixEnd_3261853 := by exact prefixLift 3261853
  have htrace : WordTrace (prefixWord ++ tailWord_3261853) baseStart_3261853 baseEnd_3261853 := by
    simpa [prefixWord, tailWord_3261853, baseEnd_3261853] using wordTrace_append hprefix tailTrace_3261853
  have hstable : (prefixWord ++ tailWord_3261853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261853).length < 2 ^ (prefixWord ++ tailWord_3261853).sum := by decide
  have hdescent : baseEnd_3261853 < baseStart_3261853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261854 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3261854 : Nat := 118140960795 + 3261854 * 2 ^ 59
def prefixEnd_3261854 : Nat := 4983230072969 + 3 ^ 40 * 3261854 * 2
def baseEnd_3261854 : Nat := 558299642263595404974671

theorem tailTrace_3261854 : CollatzResearch.WordTrace tailWord_3261854 prefixEnd_3261854 558299642263595404974671 := by
  unfold tailWord_3261854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871198640608439144610077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79313059416578342104587077 14871198640608439144610077)
  ·
    refine ⟨5576699490228164679228779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14871198640608439144610077 5576699490228164679228779)
    ·
      refine ⟨8365049235342247018843169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576699490228164679228779 8365049235342247018843169)
      ·
        refine ⟨6273786926506685264132377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8365049235342247018843169 6273786926506685264132377)
        ·
          refine ⟨4705340194880013948099283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6273786926506685264132377 4705340194880013948099283)
          ·
            refine ⟨7058010292320020922148925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705340194880013948099283 7058010292320020922148925)
            ·
              refine ⟨2646753859620007845805847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7058010292320020922148925 2646753859620007845805847)
              ·
                refine ⟨3970130789430011768708771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646753859620007845805847 3970130789430011768708771)
                ·
                  refine ⟨5955196184145017653063157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970130789430011768708771 5955196184145017653063157)
                  ·
                    refine ⟨558299642263595404974671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5955196184145017653063157 558299642263595404974671)
                    ·
                      rfl

theorem cell23_3261854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3261854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261854 prefixEnd_3261854 := by exact prefixLift 3261854
  have htrace : WordTrace (prefixWord ++ tailWord_3261854) baseStart_3261854 baseEnd_3261854 := by
    simpa [prefixWord, tailWord_3261854, baseEnd_3261854] using wordTrace_append hprefix tailTrace_3261854
  have hstable : (prefixWord ++ tailWord_3261854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261854).length < 2 ^ (prefixWord ++ tailWord_3261854).sum := by decide
  have hdescent : baseEnd_3261854 < baseStart_3261854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261873 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3261873 : Nat := 118140960795 + 3261873 * 2 ^ 59
def prefixEnd_3261873 : Nat := 4983230072969 + 3 ^ 40 * 3261873 * 2
def baseEnd_3261873 : Nat := 1674908682923221640586425

theorem tailTrace_3261873 : CollatzResearch.WordTrace tailWord_3261873 prefixEnd_3261873 1674908682923221640586425 := by
  unfold tailWord_3261873
  simp only [CollatzResearch.WordTrace]
  refine ⟨118970282111798679401822273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79313521407865786267881515 118970282111798679401822273)
  ·
    refine ⟨89227711583849009551366705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118970282111798679401822273 89227711583849009551366705)
    ·
      refine ⟨66920783687886757163525029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89227711583849009551366705 66920783687886757163525029)
      ·
        refine ⟨12547646941478766968160943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66920783687886757163525029 12547646941478766968160943)
        ·
          refine ⟨18821470412218150452241415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547646941478766968160943 18821470412218150452241415)
          ·
            refine ⟨28232205618327225678362123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18821470412218150452241415 28232205618327225678362123)
            ·
              refine ⟨42348308427490838517543185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28232205618327225678362123 42348308427490838517543185)
              ·
                refine ⟨31761231320618128888157389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42348308427490838517543185 31761231320618128888157389)
                ·
                  refine ⟨11910461745231798333059021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31761231320618128888157389 11910461745231798333059021)
                  ·
                    refine ⟨4466423154461924374897133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11910461745231798333059021 4466423154461924374897133)
                    ·
                      refine ⟨1674908682923221640586425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4466423154461924374897133 1674908682923221640586425)
                      ·
                        rfl

theorem cell23_3261873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3261873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261873 prefixEnd_3261873 := by exact prefixLift 3261873
  have htrace : WordTrace (prefixWord ++ tailWord_3261873) baseStart_3261873 baseEnd_3261873 := by
    simpa [prefixWord, tailWord_3261873, baseEnd_3261873] using wordTrace_append hprefix tailTrace_3261873
  have hstable : (prefixWord ++ tailWord_3261873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261873).length < 2 ^ (prefixWord ++ tailWord_3261873).sum := by decide
  have hdescent : baseEnd_3261873 < baseStart_3261873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261923 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 6]
def baseStart_3261923 : Nat := 118140960795 + 3261923 * 2 ^ 59
def prefixEnd_3261923 : Nat := 4983230072969 + 3 ^ 40 * 3261923 * 2
def baseEnd_3261923 : Nat := 558311452318648814987065

theorem tailTrace_3261923 : CollatzResearch.WordTrace tailWord_3261923 prefixEnd_3261923 558311452318648814987065 := by
  unfold tailWord_3261923
  simp only [CollatzResearch.WordTrace]
  refine ⟨118972105761617537941142423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79314737174411691960761615 118972105761617537941142423)
  ·
    refine ⟨178458158642426306911713635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118972105761617537941142423 178458158642426306911713635)
    ·
      refine ⟨267687237963639460367570453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178458158642426306911713635 267687237963639460367570453)
      ·
        refine ⟨12547839279545599704729865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267687237963639460367570453 12547839279545599704729865)
        ·
          refine ⟨9410879459659199778547399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12547839279545599704729865 9410879459659199778547399)
          ·
            refine ⟨14116319189488799667821099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410879459659199778547399 14116319189488799667821099)
            ·
              refine ⟨21174478784233199501731649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116319189488799667821099 21174478784233199501731649)
              ·
                refine ⟨15880859088174899626298737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21174478784233199501731649 15880859088174899626298737)
                ·
                  refine ⟨11910644316131174719724053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15880859088174899626298737 11910644316131174719724053)
                  ·
                    refine ⟨558311452318648814987065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11910644316131174719724053 558311452318648814987065)
                    ·
                      rfl

theorem cell23_3261923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_3261923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261923 prefixEnd_3261923 := by exact prefixLift 3261923
  have htrace : WordTrace (prefixWord ++ tailWord_3261923) baseStart_3261923 baseEnd_3261923 := by
    simpa [prefixWord, tailWord_3261923, baseEnd_3261923] using wordTrace_append hprefix tailTrace_3261923
  have hstable : (prefixWord ++ tailWord_3261923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261923).length < 2 ^ (prefixWord ++ tailWord_3261923).sum := by decide
  have hdescent : baseEnd_3261923 < baseStart_3261923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261941 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3261941 : Nat := 118140960795 + 3261941 * 2 ^ 59
def prefixEnd_3261941 : Nat := 4983230072969 + 3 ^ 40 * 3261941 * 2
def baseEnd_3261941 : Nat := 1674943599607727374536113

theorem tailTrace_3261941 : CollatzResearch.WordTrace tailWord_3261941 prefixEnd_3261941 1674943599607727374536113 := by
  unfold tailWord_3261941
  simp only [CollatzResearch.WordTrace]
  refine ⟨118972762275552327015297677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79315174850368218010198451 118972762275552327015297677)
  ·
    refine ⟨44614785853332122630736629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118972762275552327015297677 44614785853332122630736629)
    ·
      refine ⟨4182636173749886496631559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44614785853332122630736629 4182636173749886496631559)
      ·
        refine ⟨6273954260624829744947339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182636173749886496631559 6273954260624829744947339)
        ·
          refine ⟨9410931390937244617421009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273954260624829744947339 9410931390937244617421009)
          ·
            refine ⟨7058198543202933463065757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9410931390937244617421009 7058198543202933463065757)
            ·
              refine ⟨2646824453701100048649659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7058198543202933463065757 2646824453701100048649659)
              ·
                refine ⟨3970236680551650072974489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646824453701100048649659 3970236680551650072974489)
                ·
                  refine ⟨2977677510413737554730867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3970236680551650072974489 2977677510413737554730867)
                  ·
                    refine ⟨4466516265620606332096301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2977677510413737554730867 4466516265620606332096301)
                    ·
                      refine ⟨1674943599607727374536113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4466516265620606332096301 1674943599607727374536113)
                      ·
                        rfl

theorem cell23_3261941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3261941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261941 prefixEnd_3261941 := by exact prefixLift 3261941
  have htrace : WordTrace (prefixWord ++ tailWord_3261941) baseStart_3261941 baseEnd_3261941 := by
    simpa [prefixWord, tailWord_3261941, baseEnd_3261941] using wordTrace_append hprefix tailTrace_3261941
  have hstable : (prefixWord ++ tailWord_3261941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261941).length < 2 ^ (prefixWord ++ tailWord_3261941).sum := by decide
  have hdescent : baseEnd_3261941 < baseStart_3261941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261983 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 4, 5]
def baseStart_3261983 : Nat := 118140960795 + 3261983 * 2 ^ 59
def prefixEnd_3261983 : Nat := 4983230072969 + 3 ^ 40 * 3261983 * 2
def baseEnd_3261983 : Nat := 558321721931738736736973

theorem tailTrace_3261983 : CollatzResearch.WordTrace tailWord_3261983 prefixEnd_3261983 558321721931738736736973 := by
  unfold tailWord_3261983
  simp only [CollatzResearch.WordTrace]
  refine ⟨118974294141400168188326603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79316196094266778792217735 118974294141400168188326603)
  ·
    refine ⟨178461441212100252282489905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118974294141400168188326603 178461441212100252282489905)
    ·
      refine ⟨133846080909075189211867429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178461441212100252282489905 133846080909075189211867429)
      ·
        refine ⟨25096140170451597977225143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133846080909075189211867429 25096140170451597977225143)
        ·
          refine ⟨37644210255677396965837715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25096140170451597977225143 37644210255677396965837715)
          ·
            refine ⟨56466315383516095448756573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37644210255677396965837715 56466315383516095448756573)
            ·
              refine ⟨21174868268818535793283715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56466315383516095448756573 21174868268818535793283715)
              ·
                refine ⟨31762302403227803689925573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21174868268818535793283715 31762302403227803689925573)
                ·
                  refine ⟨5955431700605213191861045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31762302403227803689925573 5955431700605213191861045)
                  ·
                    refine ⟨558321721931738736736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5955431700605213191861045 558321721931738736736973)
                    ·
                      rfl

theorem cell23_3261983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_3261983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261983 prefixEnd_3261983 := by exact prefixLift 3261983
  have htrace : WordTrace (prefixWord ++ tailWord_3261983) baseStart_3261983 baseEnd_3261983 := by
    simpa [prefixWord, tailWord_3261983, baseEnd_3261983] using wordTrace_append hprefix tailTrace_3261983
  have hstable : (prefixWord ++ tailWord_3261983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261983).length < 2 ^ (prefixWord ++ tailWord_3261983).sum := by decide
  have hdescent : baseEnd_3261983 < baseStart_3261983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261987 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 7]
def baseStart_3261987 : Nat := 118140960795 + 3261987 * 2 ^ 59
def prefixEnd_3261987 : Nat := 4983230072969 + 3 ^ 40 * 3261987 * 2
def baseEnd_3261987 : Nat := 186107468857537132728989

theorem tailTrace_3261987 : CollatzResearch.WordTrace tailWord_3261987 prefixEnd_3261987 186107468857537132728989 := by
  unfold tailWord_3261987
  simp only [CollatzResearch.WordTrace]
  refine ⟨118974440033385676871472215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79316293355590451247648143 118974440033385676871472215)
  ·
    refine ⟨178461660050078515307208323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118974440033385676871472215 178461660050078515307208323)
    ·
      refine ⟨267692490075117772960812485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178461660050078515307208323 267692490075117772960812485)
      ·
        refine ⟨50192341889084582430152341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267692490075117772960812485 50192341889084582430152341)
        ·
          refine ⟨2352766026050839801413391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50192341889084582430152341 2352766026050839801413391)
          ·
            refine ⟨3529149039076259702120087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352766026050839801413391 3529149039076259702120087)
            ·
              refine ⟨5293723558614389553180131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529149039076259702120087 5293723558614389553180131)
              ·
                refine ⟨7940585337921584329770197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293723558614389553180131 7940585337921584329770197)
                ·
                  refine ⟨186107468857537132728989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7940585337921584329770197 186107468857537132728989)
                  ·
                    rfl

theorem cell23_3261987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 7].length) (baseStart_3261987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261987 prefixEnd_3261987 := by exact prefixLift 3261987
  have htrace : WordTrace (prefixWord ++ tailWord_3261987) baseStart_3261987 baseEnd_3261987 := by
    simpa [prefixWord, tailWord_3261987, baseEnd_3261987] using wordTrace_append hprefix tailTrace_3261987
  have hstable : (prefixWord ++ tailWord_3261987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261987).length < 2 ^ (prefixWord ++ tailWord_3261987).sum := by decide
  have hdescent : baseEnd_3261987 < baseStart_3261987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3261998 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3261998 : Nat := 118140960795 + 3261998 * 2 ^ 59
def prefixEnd_3261998 : Nat := 4983230072969 + 3 ^ 40 * 3261998 * 2
def baseEnd_3261998 : Nat := 1674972868005033651523351

theorem tailTrace_3261998 : CollatzResearch.WordTrace tailWord_3261998 prefixEnd_3261998 1674972868005033651523351 := by
  unfold tailWord_3261998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871855154543228218765331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79316560824230550500081765 14871855154543228218765331)
  ·
    refine ⟨22307782731814842328147997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14871855154543228218765331 22307782731814842328147997)
    ·
      refine ⟨8365418524430565873055499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22307782731814842328147997 8365418524430565873055499)
      ·
        refine ⟨12548127786645848809583249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8365418524430565873055499 12548127786645848809583249)
        ·
          refine ⟨9411095839984386607187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12548127786645848809583249 9411095839984386607187437)
          ·
            refine ⟨3529160939994144977695289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9411095839984386607187437 3529160939994144977695289)
            ·
              refine ⟨2646870704995608733271467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529160939994144977695289 2646870704995608733271467)
              ·
                refine ⟨3970306057493413099907201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646870704995608733271467 3970306057493413099907201)
                ·
                  refine ⟨2977729543120059824930401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3970306057493413099907201 2977729543120059824930401)
                  ·
                    refine ⟨2233297157340044868697801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977729543120059824930401 2233297157340044868697801)
                    ·
                      refine ⟨1674972868005033651523351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233297157340044868697801 1674972868005033651523351)
                      ·
                        rfl

theorem cell23_3261998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3261998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3261998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3261998 prefixEnd_3261998 := by exact prefixLift 3261998
  have htrace : WordTrace (prefixWord ++ tailWord_3261998) baseStart_3261998 baseEnd_3261998 := by
    simpa [prefixWord, tailWord_3261998, baseEnd_3261998] using wordTrace_append hprefix tailTrace_3261998
  have hstable : (prefixWord ++ tailWord_3261998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3261998).length < 2 ^ (prefixWord ++ tailWord_3261998).sum := by decide
  have hdescent : baseEnd_3261998 < baseStart_3261998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3261998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262033 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3262033 : Nat := 118140960795 + 3262033 * 2 ^ 59
def prefixEnd_3262033 : Nat := 4983230072969 + 3 ^ 40 * 3262033 * 2
def baseEnd_3262033 : Nat := 1674990839827941014585689

theorem tailTrace_3262033 : CollatzResearch.WordTrace tailWord_3262033 prefixEnd_3262033 1674990839827941014585689 := by
  unfold tailWord_3262033
  simp only [CollatzResearch.WordTrace]
  refine ⟨118976117791219026727646753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79317411860812684485097835 118976117791219026727646753)
  ·
    refine ⟨89232088343414270045735065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118976117791219026727646753 89232088343414270045735065)
    ·
      refine ⟨66924066257560702534301299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89232088343414270045735065 66924066257560702534301299)
      ·
        refine ⟨100386099386341053801451949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66924066257560702534301299 100386099386341053801451949)
        ·
          refine ⟨37644787269877895175544481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100386099386341053801451949 37644787269877895175544481)
          ·
            refine ⟨28233590452408421381658361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37644787269877895175544481 28233590452408421381658361)
            ·
              refine ⟨21175192839306316036243771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28233590452408421381658361 21175192839306316036243771)
              ·
                refine ⟨31762789258959474054365657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21175192839306316036243771 31762789258959474054365657)
                ·
                  refine ⟨23822091944219605540774243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31762789258959474054365657 23822091944219605540774243)
                  ·
                    refine ⟨35733137916329408311161365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23822091944219605540774243 35733137916329408311161365)
                    ·
                      refine ⟨1674990839827941014585689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35733137916329408311161365 1674990839827941014585689)
                      ·
                        rfl

theorem cell23_3262033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3262033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262033 prefixEnd_3262033 := by exact prefixLift 3262033
  have htrace : WordTrace (prefixWord ++ tailWord_3262033) baseStart_3262033 baseEnd_3262033 := by
    simpa [prefixWord, tailWord_3262033, baseEnd_3262033] using wordTrace_append hprefix tailTrace_3262033
  have hstable : (prefixWord ++ tailWord_3262033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262033).length < 2 ^ (prefixWord ++ tailWord_3262033).sum := by decide
  have hdescent : baseEnd_3262033 < baseStart_3262033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262083 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_3262083 : Nat := 118140960795 + 3262083 * 2 ^ 59
def prefixEnd_3262083 : Nat := 4983230072969 + 3 ^ 40 * 3262083 * 2
def baseEnd_3262083 : Nat := 1675016513860665818960459

theorem tailTrace_3262083 : CollatzResearch.WordTrace tailWord_3262083 prefixEnd_3262083 1675016513860665818960459 := by
  unfold tailWord_3262083
  simp only [CollatzResearch.WordTrace]
  refine ⟨118977941441037885266966903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79318627627358590177977935 118977941441037885266966903)
  ·
    refine ⟨178466912161556827900450355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118977941441037885266966903 178466912161556827900450355)
    ·
      refine ⟨267700368242335241850675533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178466912161556827900450355 267700368242335241850675533)
      ·
        refine ⟨100387638090875715694003325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267700368242335241850675533 100387638090875715694003325)
        ·
          refine ⟨37645364284078393385251247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100387638090875715694003325 37645364284078393385251247)
          ·
            refine ⟨56468046426117590077876871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37645364284078393385251247 56468046426117590077876871)
            ·
              refine ⟨84702069639176385116815307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56468046426117590077876871 84702069639176385116815307)
              ·
                refine ⟨127053104458764577675222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84702069639176385116815307 127053104458764577675222961)
                ·
                  refine ⟨95289828344073433256417221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127053104458764577675222961 95289828344073433256417221)
                  ·
                    refine ⟨17866842814513768735578229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95289828344073433256417221 17866842814513768735578229)
                    ·
                      refine ⟨1675016513860665818960459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17866842814513768735578229 1675016513860665818960459)
                      ·
                        rfl

theorem cell23_3262083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_3262083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262083 prefixEnd_3262083 := by exact prefixLift 3262083
  have htrace : WordTrace (prefixWord ++ tailWord_3262083) baseStart_3262083 baseEnd_3262083 := by
    simpa [prefixWord, tailWord_3262083, baseEnd_3262083] using wordTrace_append hprefix tailTrace_3262083
  have hstable : (prefixWord ++ tailWord_3262083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262083).length < 2 ^ (prefixWord ++ tailWord_3262083).sum := by decide
  have hdescent : baseEnd_3262083 < baseStart_3262083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262104 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3262104 : Nat := 118140960795 + 3262104 * 2 ^ 59
def prefixEnd_3262104 : Nat := 4983230072969 + 3 ^ 40 * 3262104 * 2
def baseEnd_3262104 : Nat := 1675027296954410236797863

theorem tailTrace_3262104 : CollatzResearch.WordTrace tailWord_3262104 prefixEnd_3262104 1675027296954410236797863 := by
  unfold tailWord_3262104
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489353686980902926740683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79319138249307870568987577 59489353686980902926740683)
  ·
    refine ⟨89234030530471354390111025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59489353686980902926740683 89234030530471354390111025)
    ·
      refine ⟨66925522897853515792583269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89234030530471354390111025 66925522897853515792583269)
      ·
        refine ⟨12548535543347534211109363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66925522897853515792583269 12548535543347534211109363)
        ·
          refine ⟨18822803315021301316664045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12548535543347534211109363 18822803315021301316664045)
          ·
            refine ⟨7058551243132987993749017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18822803315021301316664045 7058551243132987993749017)
            ·
              refine ⟨5293913432349740995311763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7058551243132987993749017 5293913432349740995311763)
              ·
                refine ⟨7940870148524611492967645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293913432349740995311763 7940870148524611492967645)
                ·
                  refine ⟨2977826305696729309862867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7940870148524611492967645 2977826305696729309862867)
                  ·
                    refine ⟨4466739458545093964794301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2977826305696729309862867 4466739458545093964794301)
                    ·
                      refine ⟨1675027296954410236797863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4466739458545093964794301 1675027296954410236797863)
                      ·
                        rfl

theorem cell23_3262104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3262104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262104 prefixEnd_3262104 := by exact prefixLift 3262104
  have htrace : WordTrace (prefixWord ++ tailWord_3262104) baseStart_3262104 baseEnd_3262104 := by
    simpa [prefixWord, tailWord_3262104, baseEnd_3262104] using wordTrace_append hprefix tailTrace_3262104
  have hstable : (prefixWord ++ tailWord_3262104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262104).length < 2 ^ (prefixWord ++ tailWord_3262104).sum := by decide
  have hdescent : baseEnd_3262104 < baseStart_3262104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262127 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_3262127 : Nat := 118140960795 + 3262127 * 2 ^ 59
def prefixEnd_3262127 : Nat := 4983230072969 + 3 ^ 40 * 3262127 * 2
def baseEnd_3262127 : Nat := 1675039107009463646810257

theorem tailTrace_3262127 : CollatzResearch.WordTrace tailWord_3262127 prefixEnd_3262127 1675039107009463646810257 := by
  unfold tailWord_3262127
  simp only [CollatzResearch.WordTrace]
  refine ⟨118979546252878480781568635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79319697501918987187712423 118979546252878480781568635)
  ·
    refine ⟨178469319379317721172352953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118979546252878480781568635 178469319379317721172352953)
    ·
      refine ⟨133851989534488290879264715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178469319379317721172352953 133851989534488290879264715)
      ·
        refine ⟨200777984301732436318897073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133851989534488290879264715 200777984301732436318897073)
        ·
          refine ⟨150583488226299327239172805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200777984301732436318897073 150583488226299327239172805)
          ·
            refine ⟨28234404042431123857344901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150583488226299327239172805 28234404042431123857344901)
            ·
              refine ⟨5293950757955835723252169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28234404042431123857344901 5293950757955835723252169)
              ·
                refine ⟨3970463068466876792439127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293950757955835723252169 3970463068466876792439127)
                ·
                  refine ⟨5955694602700315188658691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970463068466876792439127 5955694602700315188658691)
                  ·
                    refine ⟨8933541904050472782988037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955694602700315188658691 8933541904050472782988037)
                    ·
                      refine ⟨1675039107009463646810257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8933541904050472782988037 1675039107009463646810257)
                      ·
                        rfl

theorem cell23_3262127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_3262127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262127 prefixEnd_3262127 := by exact prefixLift 3262127
  have htrace : WordTrace (prefixWord ++ tailWord_3262127) baseStart_3262127 baseEnd_3262127 := by
    simpa [prefixWord, tailWord_3262127, baseEnd_3262127] using wordTrace_append hprefix tailTrace_3262127
  have hstable : (prefixWord ++ tailWord_3262127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262127).length < 2 ^ (prefixWord ++ tailWord_3262127).sum := by decide
  have hdescent : baseEnd_3262127 < baseStart_3262127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_3262160 : Nat := 118140960795 + 3262160 * 2 ^ 59
def prefixEnd_3262160 : Nat := 4983230072969 + 3 ^ 40 * 3262160 * 2
def baseEnd_3262160 : Nat := 1675056051871062017697605

theorem tailTrace_3262160 : CollatzResearch.WordTrace tailWord_3262160 prefixEnd_3262160 1675056051871062017697605 := by
  unfold tailWord_3262160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59490374930879463708759967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79320499907839284945013289 59490374930879463708759967)
  ·
    refine ⟨89235562396319195563139951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59490374930879463708759967 89235562396319195563139951)
    ·
      refine ⟨133853343594478793344709927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89235562396319195563139951 133853343594478793344709927)
      ·
        refine ⟨200780015391718190017064891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133853343594478793344709927 200780015391718190017064891)
        ·
          refine ⟨301170023087577285025597337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200780015391718190017064891 301170023087577285025597337)
          ·
            refine ⟨225877517315682963769198003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301170023087577285025597337 225877517315682963769198003)
            ·
              refine ⟨338816275973524445653797005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225877517315682963769198003 338816275973524445653797005)
              ·
                refine ⟨127056103490071667120173877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338816275973524445653797005 127056103490071667120173877)
                ·
                  refine ⟨11911509702194218792516301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127056103490071667120173877 11911509702194218792516301)
                  ·
                    refine ⟨4466816138322832047193613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11911509702194218792516301 4466816138322832047193613)
                    ·
                      refine ⟨1675056051871062017697605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4466816138322832047193613 1675056051871062017697605)
                      ·
                        rfl

theorem cell23_3262160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_3262160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262160 prefixEnd_3262160 := by exact prefixLift 3262160
  have htrace : WordTrace (prefixWord ++ tailWord_3262160) baseStart_3262160 baseEnd_3262160 := by
    simpa [prefixWord, tailWord_3262160, baseEnd_3262160] using wordTrace_append hprefix tailTrace_3262160
  have hstable : (prefixWord ++ tailWord_3262160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262160).length < 2 ^ (prefixWord ++ tailWord_3262160).sum := by decide
  have hdescent : baseEnd_3262160 < baseStart_3262160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262161 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_3262161 : Nat := 118140960795 + 3262161 * 2 ^ 59
def prefixEnd_3262161 : Nat := 4983230072969 + 3 ^ 40 * 3262161 * 2
def baseEnd_3262161 : Nat := 1675056565351716513785101

theorem tailTrace_3262161 : CollatzResearch.WordTrace tailWord_3262161 prefixEnd_3262161 1675056565351716513785101 := by
  unfold tailWord_3262161
  simp only [CollatzResearch.WordTrace]
  refine ⟨118980786334755304588306337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79320524223170203058870891 118980786334755304588306337)
  ·
    refine ⟨89235589751066478441229753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118980786334755304588306337 89235589751066478441229753)
    ·
      refine ⟨66926692313299858830922315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89235589751066478441229753 66926692313299858830922315)
      ·
        refine ⟨100390038469949788246383473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66926692313299858830922315 100390038469949788246383473)
        ·
          refine ⟨75292528852462341184787605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100390038469949788246383473 75292528852462341184787605)
          ·
            refine ⟨3529337289959172243036919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75292528852462341184787605 3529337289959172243036919)
            ·
              refine ⟨5294005934938758364555379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529337289959172243036919 5294005934938758364555379)
              ·
                refine ⟨7941008902408137546833069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294005934938758364555379 7941008902408137546833069)
                ·
                  refine ⟨2977878338403051580062401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7941008902408137546833069 2977878338403051580062401)
                  ·
                    refine ⟨2233408753802288685046801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977878338403051580062401 2233408753802288685046801)
                    ·
                      refine ⟨1675056565351716513785101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233408753802288685046801 1675056565351716513785101)
                      ·
                        rfl

theorem cell23_3262161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_3262161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262161 prefixEnd_3262161 := by exact prefixLift 3262161
  have htrace : WordTrace (prefixWord ++ tailWord_3262161) baseStart_3262161 baseEnd_3262161 := by
    simpa [prefixWord, tailWord_3262161, baseEnd_3262161] using wordTrace_append hprefix tailTrace_3262161
  have hstable : (prefixWord ++ tailWord_3262161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262161).length < 2 ^ (prefixWord ++ tailWord_3262161).sum := by decide
  have hdescent : baseEnd_3262161 < baseStart_3262161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 4, 2]
def baseStart_3262217 : Nat := 118140960795 + 3262217 * 2 ^ 59
def prefixEnd_3262217 : Nat := 4983230072969 + 3 ^ 40 * 3262217 * 2
def baseEnd_3262217 : Nat := 1675085320268368294684843

theorem tailTrace_3262217 : CollatzResearch.WordTrace tailWord_3262217 prefixEnd_3262217 1675085320268368294684843 := by
  unfold tailWord_3262217
  simp only [CollatzResearch.WordTrace]
  refine ⟨118982828822552426152344905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79321885881701617434896603 118982828822552426152344905)
  ·
    refine ⟨89237121616914319614258679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118982828822552426152344905 89237121616914319614258679)
    ·
      refine ⟨133855682425371479421388019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89237121616914319614258679 133855682425371479421388019)
      ·
        refine ⟨200783523638057219132082029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133855682425371479421388019 200783523638057219132082029)
        ·
          refine ⟨75293821364271457174530761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200783523638057219132082029 75293821364271457174530761)
          ·
            refine ⟨56470366023203592880898071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75293821364271457174530761 56470366023203592880898071)
            ·
              refine ⟨84705549034805389321347107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56470366023203592880898071 84705549034805389321347107)
              ·
                refine ⟨127058323552208083982020661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84705549034805389321347107 127058323552208083982020661)
                ·
                  refine ⟨11911717833019507873314437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127058323552208083982020661 11911717833019507873314437)
                  ·
                    refine ⟨2233447093691157726246457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11911717833019507873314437 2233447093691157726246457)
                    ·
                      refine ⟨1675085320268368294684843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233447093691157726246457 1675085320268368294684843)
                      ·
                        rfl

theorem cell23_3262217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4, 2].length) (baseStart_3262217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262217 prefixEnd_3262217 := by exact prefixLift 3262217
  have htrace : WordTrace (prefixWord ++ tailWord_3262217) baseStart_3262217 baseEnd_3262217 := by
    simpa [prefixWord, tailWord_3262217, baseEnd_3262217] using wordTrace_append hprefix tailTrace_3262217
  have hstable : (prefixWord ++ tailWord_3262217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262217).length < 2 ^ (prefixWord ++ tailWord_3262217).sum := by decide
  have hdescent : baseEnd_3262217 < baseStart_3262217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262220 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3262220 : Nat := 118140960795 + 3262220 * 2 ^ 59
def prefixEnd_3262220 : Nat := 4983230072969 + 3 ^ 40 * 3262220 * 2
def baseEnd_3262220 : Nat := 1675086860710331782947329

theorem tailTrace_3262220 : CollatzResearch.WordTrace tailWord_3262220 prefixEnd_3262220 1675086860710331782947329 := by
  unfold tailWord_3262220
  simp only [CollatzResearch.WordTrace]
  refine ⟨59491469120770778832352057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79321958827694371776469409 59491469120770778832352057)
  ·
    refine ⟨44618601840578084124264043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59491469120770778832352057 44618601840578084124264043)
    ·
      refine ⟨66927902760867126186396065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44618601840578084124264043 66927902760867126186396065)
      ·
        refine ⟨50195927070650344639797049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66927902760867126186396065 50195927070650344639797049)
        ·
          refine ⟨37646945302987758479847787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50195927070650344639797049 37646945302987758479847787)
          ·
            refine ⟨56470417954481637719771681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37646945302987758479847787 56470417954481637719771681)
            ·
              refine ⟨42352813465861228289828761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56470417954481637719771681 42352813465861228289828761)
              ·
                refine ⟨31764610099395921217371571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42352813465861228289828761 31764610099395921217371571)
                ·
                  refine ⟨47646915149093881826057357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31764610099395921217371571 47646915149093881826057357)
                  ·
                    refine ⟨17867593180910205684771509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47646915149093881826057357 17867593180910205684771509)
                    ·
                      refine ⟨1675086860710331782947329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17867593180910205684771509 1675086860710331782947329)
                      ·
                        rfl

theorem cell23_3262220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3262220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262220 prefixEnd_3262220 := by exact prefixLift 3262220
  have htrace : WordTrace (prefixWord ++ tailWord_3262220) baseStart_3262220 baseEnd_3262220 := by
    simpa [prefixWord, tailWord_3262220, baseEnd_3262220] using wordTrace_append hprefix tailTrace_3262220
  have hstable : (prefixWord ++ tailWord_3262220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262220).length < 2 ^ (prefixWord ++ tailWord_3262220).sum := by decide
  have hdescent : baseEnd_3262220 < baseStart_3262220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262234 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_3262234 : Nat := 118140960795 + 3262234 * 2 ^ 59
def prefixEnd_3262234 : Nat := 4983230072969 + 3 ^ 40 * 3262234 * 2
def baseEnd_3262234 : Nat := 1675094049439494728172265

theorem tailTrace_3262234 : CollatzResearch.WordTrace tailWord_3262234 prefixEnd_3262234 1675094049439494728172265 := by
  unfold tailWord_3262234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29745862215872709513928439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79322299242327225370475837 29745862215872709513928439)
  ·
    refine ⟨44618793323809064270892659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29745862215872709513928439 44618793323809064270892659)
    ·
      refine ⟨66928189985713596406338989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44618793323809064270892659 66928189985713596406338989)
      ·
        refine ⟨25098071244642598652377121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66928189985713596406338989 25098071244642598652377121)
        ·
          refine ⟨18823553433481948989282841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25098071244642598652377121 18823553433481948989282841)
          ·
            refine ⟨14117665075111461741962131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18823553433481948989282841 14117665075111461741962131)
            ·
              refine ⟨21176497612667192612943197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14117665075111461741962131 21176497612667192612943197)
              ·
                refine ⟨7941186604750197229853699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21176497612667192612943197 7941186604750197229853699)
                ·
                  refine ⟨11911779907125295844780549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941186604750197229853699 11911779907125295844780549)
                  ·
                    refine ⟨2233458732585992970896353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11911779907125295844780549 2233458732585992970896353)
                    ·
                      refine ⟨1675094049439494728172265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233458732585992970896353 1675094049439494728172265)
                      ·
                        rfl

theorem cell23_3262234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_3262234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262234 prefixEnd_3262234 := by exact prefixLift 3262234
  have htrace : WordTrace (prefixWord ++ tailWord_3262234) baseStart_3262234 baseEnd_3262234 := by
    simpa [prefixWord, tailWord_3262234, baseEnd_3262234] using wordTrace_append hprefix tailTrace_3262234
  have hstable : (prefixWord ++ tailWord_3262234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262234).length < 2 ^ (prefixWord ++ tailWord_3262234).sum := by decide
  have hdescent : baseEnd_3262234 < baseStart_3262234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262308 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 5]
def baseStart_3262308 : Nat := 118140960795 + 3262308 * 2 ^ 59
def prefixEnd_3262308 : Nat := 4983230072969 + 3 ^ 40 * 3262308 * 2
def baseEnd_3262308 : Nat := 186125783000880826516325

theorem tailTrace_3262308 : CollatzResearch.WordTrace tailWord_3262308 prefixEnd_3262308 186125783000880826516325 := by
  unfold tailWord_3262308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59493073932611374346953789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79324098576815165795938385 59493073932611374346953789)
  ·
    refine ⟨22309902724729265380107671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59493073932611374346953789 22309902724729265380107671)
    ·
      refine ⟨33464854087093898070161507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22309902724729265380107671 33464854087093898070161507)
      ·
        refine ⟨50197281130640847105242261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33464854087093898070161507 50197281130640847105242261)
        ·
          refine ⟨2352997552998789708058231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50197281130640847105242261 2352997552998789708058231)
          ·
            refine ⟨3529496329498184562087347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352997552998789708058231 3529496329498184562087347)
            ·
              refine ⟨5294244494247276843131021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529496329498184562087347 5294244494247276843131021)
              ·
                refine ⟨1985341685342728816174133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5294244494247276843131021 1985341685342728816174133)
                ·
                  refine ⟨186125783000880826516325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1985341685342728816174133 186125783000880826516325)
                  ·
                    rfl

theorem cell23_3262308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_3262308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262308 prefixEnd_3262308 := by exact prefixLift 3262308
  have htrace : WordTrace (prefixWord ++ tailWord_3262308) baseStart_3262308 baseEnd_3262308 := by
    simpa [prefixWord, tailWord_3262308, baseEnd_3262308] using wordTrace_append hprefix tailTrace_3262308
  have hstable : (prefixWord ++ tailWord_3262308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262308).length < 2 ^ (prefixWord ++ tailWord_3262308).sum := by decide
  have hdescent : baseEnd_3262308 < baseStart_3262308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262385 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 1, 4]
def baseStart_3262385 : Nat := 118140960795 + 3262385 * 2 ^ 59
def prefixEnd_3262385 : Nat := 4983230072969 + 3 ^ 40 * 3262385 * 2
def baseEnd_3262385 : Nat := 558390528339441212461357

theorem tailTrace_3262385 : CollatzResearch.WordTrace tailWord_3262385 prefixEnd_3262385 558390528339441212461357 := by
  unfold tailWord_3262385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118988956285943790844460609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79325970857295860562973739 118988956285943790844460609)
  ·
    refine ⟨89241717214457843133345457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118988956285943790844460609 89241717214457843133345457)
    ·
      refine ⟨66931287910843382350009093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89241717214457843133345457 66931287910843382350009093)
      ·
        refine ⟨12549616483283134190626705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66931287910843382350009093 12549616483283134190626705)
        ·
          refine ⟨9412212362462350642970029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549616483283134190626705 9412212362462350642970029)
          ·
            refine ⟨3529579635923381491113761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9412212362462350642970029 3529579635923381491113761)
            ·
              refine ⟨2647184726942536118335321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529579635923381491113761 2647184726942536118335321)
              ·
                refine ⟨1985388545206902088751491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647184726942536118335321 1985388545206902088751491)
                ·
                  refine ⟨2978082817810353133127237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985388545206902088751491 2978082817810353133127237)
                  ·
                    refine ⟨558390528339441212461357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978082817810353133127237 558390528339441212461357)
                    ·
                      rfl

theorem cell23_3262385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_3262385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262385 prefixEnd_3262385 := by exact prefixLift 3262385
  have htrace : WordTrace (prefixWord ++ tailWord_3262385) baseStart_3262385 baseEnd_3262385 := by
    simpa [prefixWord, tailWord_3262385, baseEnd_3262385] using wordTrace_append hprefix tailTrace_3262385
  have hstable : (prefixWord ++ tailWord_3262385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262385).length < 2 ^ (prefixWord ++ tailWord_3262385).sum := by decide
  have hdescent : baseEnd_3262385 < baseStart_3262385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262414 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3262414 : Nat := 118140960795 + 3262414 * 2 ^ 59
def prefixEnd_3262414 : Nat := 4983230072969 + 3 ^ 40 * 3262414 * 2
def baseEnd_3262414 : Nat := 1675186475957304023921437

theorem tailTrace_3262414 : CollatzResearch.WordTrace tailWord_3262414 prefixEnd_3262414 1675186475957304023921437 := by
  unfold tailWord_3262414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873751750354841099658287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79326676001892485864844197 14873751750354841099658287)
  ·
    refine ⟨22310627625532261649487431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14873751750354841099658287 22310627625532261649487431)
    ·
      refine ⟨33465941438298392474231147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22310627625532261649487431 33465941438298392474231147)
      ·
        refine ⟨50198912157447588711346721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33465941438298392474231147 50198912157447588711346721)
        ·
          refine ⟨37649184118085691533510041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50198912157447588711346721 37649184118085691533510041)
          ·
            refine ⟨28236888088564268650132531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37649184118085691533510041 28236888088564268650132531)
            ·
              refine ⟨42355332132846402975198797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28236888088564268650132531 42355332132846402975198797)
              ·
                refine ⟨15883249549817401115699549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42355332132846402975198797 15883249549817401115699549)
                ·
                  refine ⟨5956218581181525418387331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15883249549817401115699549 5956218581181525418387331)
                  ·
                    refine ⟨8934327871772288127580997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956218581181525418387331 8934327871772288127580997)
                    ·
                      refine ⟨1675186475957304023921437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8934327871772288127580997 1675186475957304023921437)
                      ·
                        rfl

theorem cell23_3262414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3262414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262414 prefixEnd_3262414 := by exact prefixLift 3262414
  have htrace : WordTrace (prefixWord ++ tailWord_3262414) baseStart_3262414 baseEnd_3262414 := by
    simpa [prefixWord, tailWord_3262414, baseEnd_3262414] using wordTrace_append hprefix tailTrace_3262414
  have hstable : (prefixWord ++ tailWord_3262414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262414).length < 2 ^ (prefixWord ++ tailWord_3262414).sum := by decide
  have hdescent : baseEnd_3262414 < baseStart_3262414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262417 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3262417 : Nat := 118140960795 + 3262417 * 2 ^ 59
def prefixEnd_3262417 : Nat := 4983230072969 + 3 ^ 40 * 3262417 * 2
def baseEnd_3262417 : Nat := 1675188016399267512183923

theorem tailTrace_3262417 : CollatzResearch.WordTrace tailWord_3262417 prefixEnd_3262417 1675188016399267512183923 := by
  unfold tailWord_3262417
  simp only [CollatzResearch.WordTrace]
  refine ⟨118990123421827860309625505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79326748947885240206417003 118990123421827860309625505)
  ·
    refine ⟨89242592566370895232219129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118990123421827860309625505 89242592566370895232219129)
    ·
      refine ⟨66931944424778171424164347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89242592566370895232219129 66931944424778171424164347)
      ·
        refine ⟨100397916637167257136246521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66931944424778171424164347 100397916637167257136246521)
        ·
          refine ⟨75298437477875442852184891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100397916637167257136246521 75298437477875442852184891)
          ·
            refine ⟨112947656216813164278277337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75298437477875442852184891 112947656216813164278277337)
            ·
              refine ⟨84710742162609873208708003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112947656216813164278277337 84710742162609873208708003)
              ·
                refine ⟨127066113243914809813062005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84710742162609873208708003 127066113243914809813062005)
                ·
                  refine ⟨11912448116617013419974563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127066113243914809813062005 11912448116617013419974563)
                  ·
                    refine ⟨17868672174925520129961845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11912448116617013419974563 17868672174925520129961845)
                    ·
                      refine ⟨1675188016399267512183923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17868672174925520129961845 1675188016399267512183923)
                      ·
                        rfl

theorem cell23_3262417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3262417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262417 prefixEnd_3262417 := by exact prefixLift 3262417
  have htrace : WordTrace (prefixWord ++ tailWord_3262417) baseStart_3262417 baseEnd_3262417 := by
    simpa [prefixWord, tailWord_3262417, baseEnd_3262417] using wordTrace_append hprefix tailTrace_3262417
  have hstable : (prefixWord ++ tailWord_3262417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262417).length < 2 ^ (prefixWord ++ tailWord_3262417).sum := by decide
  have hdescent : baseEnd_3262417 < baseStart_3262417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262418 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3262418 : Nat := 118140960795 + 3262418 * 2 ^ 59
def prefixEnd_3262418 : Nat := 4983230072969 + 3 ^ 40 * 3262418 * 2
def baseEnd_3262418 : Nat := 1675188529879922008271419

theorem tailTrace_3262418 : CollatzResearch.WordTrace tailWord_3262418 prefixEnd_3262418 1675188529879922008271419 := by
  unfold tailWord_3262418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747539973706059370102977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79326773263216158320274605 29747539973706059370102977)
  ·
    refine ⟨22310654980279544527577233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29747539973706059370102977 22310654980279544527577233)
    ·
      refine ⟨16732991235209658395682925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22310654980279544527577233 16732991235209658395682925)
      ·
        refine ⟨6274871713203621898381097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16732991235209658395682925 6274871713203621898381097)
        ·
          refine ⟨4706153784902716423785823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6274871713203621898381097 4706153784902716423785823)
          ·
            refine ⟨7059230677354074635678735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706153784902716423785823 7059230677354074635678735)
            ·
              refine ⟨10588846016031111953518103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059230677354074635678735 10588846016031111953518103)
              ·
                refine ⟨15883269024046667930277155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10588846016031111953518103 15883269024046667930277155)
                ·
                  refine ⟨23824903536070001895415733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15883269024046667930277155 23824903536070001895415733)
                  ·
                    refine ⟨2233584706506562677695225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23824903536070001895415733 2233584706506562677695225)
                    ·
                      refine ⟨1675188529879922008271419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233584706506562677695225 1675188529879922008271419)
                      ·
                        rfl

theorem cell23_3262418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3262418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262418 prefixEnd_3262418 := by exact prefixLift 3262418
  have htrace : WordTrace (prefixWord ++ tailWord_3262418) baseStart_3262418 baseEnd_3262418 := by
    simpa [prefixWord, tailWord_3262418, baseEnd_3262418] using wordTrace_append hprefix tailTrace_3262418
  have hstable : (prefixWord ++ tailWord_3262418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262418).length < 2 ^ (prefixWord ++ tailWord_3262418).sum := by decide
  have hdescent : baseEnd_3262418 < baseStart_3262418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262424 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_3262424 : Nat := 118140960795 + 3262424 * 2 ^ 59
def prefixEnd_3262424 : Nat := 4983230072969 + 3 ^ 40 * 3262424 * 2
def baseEnd_3262424 : Nat := 558397203587949661598797

theorem tailTrace_3262424 : CollatzResearch.WordTrace tailWord_3262424 prefixEnd_3262424 558397203587949661598797 := by
  unfold tailWord_3262424
  simp only [CollatzResearch.WordTrace]
  refine ⟨59495189366401250252565163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79326919155201667003420217 59495189366401250252565163)
  ·
    refine ⟨89242784049601875378847745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59495189366401250252565163 89242784049601875378847745)
    ·
      refine ⟨66932088037201406534135809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89242784049601875378847745 66932088037201406534135809)
      ·
        refine ⟨50199066027901054900601857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66932088037201406534135809 50199066027901054900601857)
        ·
          refine ⟨37649299520925791175451393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50199066027901054900601857 37649299520925791175451393)
          ·
            refine ⟨28236974640694343381588545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37649299520925791175451393 28236974640694343381588545)
            ·
              refine ⟨21177730980520757536191409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28236974640694343381588545 21177730980520757536191409)
              ·
                refine ⟨15883298235390568152143557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21177730980520757536191409 15883298235390568152143557)
                ·
                  refine ⟨2978118419135731528526917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15883298235390568152143557 2978118419135731528526917)
                  ·
                    refine ⟨558397203587949661598797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978118419135731528526917 558397203587949661598797)
                    ·
                      rfl

theorem cell23_3262424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_3262424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262424 prefixEnd_3262424 := by exact prefixLift 3262424
  have htrace : WordTrace (prefixWord ++ tailWord_3262424) baseStart_3262424 baseEnd_3262424 := by
    simpa [prefixWord, tailWord_3262424, baseEnd_3262424] using wordTrace_append hprefix tailTrace_3262424
  have hstable : (prefixWord ++ tailWord_3262424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262424).length < 2 ^ (prefixWord ++ tailWord_3262424).sum := by decide
  have hdescent : baseEnd_3262424 < baseStart_3262424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262425 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 1, 1, 3]
def baseStart_3262425 : Nat := 118140960795 + 3262425 * 2 ^ 59
def prefixEnd_3262425 : Nat := 4983230072969 + 3 ^ 40 * 3262425 * 2
def baseEnd_3262425 : Nat := 1675192124244503480883887

theorem tailTrace_3262425 : CollatzResearch.WordTrace tailWord_3262425 prefixEnd_3262425 1675192124244503480883887 := by
  unfold tailWord_3262425
  simp only [CollatzResearch.WordTrace]
  refine ⟨118990415205798877675916729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79326943470532585117277819 118990415205798877675916729)
  ·
    refine ⟨89242811404349158256937547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118990415205798877675916729 89242811404349158256937547)
    ·
      refine ⟨133864217106523737385406321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89242811404349158256937547 133864217106523737385406321)
      ·
        refine ⟨100398162829892803039054741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133864217106523737385406321 100398162829892803039054741)
        ·
          refine ⟨4706163882651225142455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100398162829892803039054741 4706163882651225142455691)
          ·
            refine ⟨7059245823976837713683537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706163882651225142455691 7059245823976837713683537)
            ·
              refine ⟨5294434367982628285262653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7059245823976837713683537 5294434367982628285262653)
              ·
                refine ⟨1985412887993485606973495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5294434367982628285262653 1985412887993485606973495)
                ·
                  refine ⟨2978119331990228410460243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985412887993485606973495 2978119331990228410460243)
                  ·
                    refine ⟨4467178997985342615690365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978119331990228410460243 4467178997985342615690365)
                    ·
                      refine ⟨1675192124244503480883887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467178997985342615690365 1675192124244503480883887)
                      ·
                        rfl

theorem cell23_3262425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_3262425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262425 prefixEnd_3262425 := by exact prefixLift 3262425
  have htrace : WordTrace (prefixWord ++ tailWord_3262425) baseStart_3262425 baseEnd_3262425 := by
    simpa [prefixWord, tailWord_3262425, baseEnd_3262425] using wordTrace_append hprefix tailTrace_3262425
  have hstable : (prefixWord ++ tailWord_3262425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262425).length < 2 ^ (prefixWord ++ tailWord_3262425).sum := by decide
  have hdescent : baseEnd_3262425 < baseStart_3262425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262431 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_3262431 : Nat := 118140960795 + 3262431 * 2 ^ 59
def prefixEnd_3262431 : Nat := 4983230072969 + 3 ^ 40 * 3262431 * 2
def baseEnd_3262431 : Nat := 1675195205128430457408859

theorem tailTrace_3262431 : CollatzResearch.WordTrace tailWord_3262431 prefixEnd_3262431 1675195205128430457408859 := by
  unfold tailWord_3262431
  simp only [CollatzResearch.WordTrace]
  refine ⟨118990634043777140700635147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79327089362518093800423431 118990634043777140700635147)
  ·
    refine ⟨178485951065665711050952721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118990634043777140700635147 178485951065665711050952721)
    ·
      refine ⟨133864463299249283288214541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178485951065665711050952721 133864463299249283288214541)
      ·
        refine ⟨50199173737218481233080453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133864463299249283288214541 50199173737218481233080453)
        ·
          refine ⟨9412345075728465231202585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50199173737218481233080453 9412345075728465231202585)
          ·
            refine ⟨7059258806796348923401939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9412345075728465231202585 7059258806796348923401939)
            ·
              refine ⟨10588888210194523385102909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059258806796348923401939 10588888210194523385102909)
              ·
                refine ⟨3970833078822946269413591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10588888210194523385102909 3970833078822946269413591)
                ·
                  refine ⟨5956249618234419404120387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970833078822946269413591 5956249618234419404120387)
                  ·
                    refine ⟨8934374427351629106180581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956249618234419404120387 8934374427351629106180581)
                    ·
                      refine ⟨1675195205128430457408859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8934374427351629106180581 1675195205128430457408859)
                      ·
                        rfl

theorem cell23_3262431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_3262431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262431 prefixEnd_3262431 := by exact prefixLift 3262431
  have htrace : WordTrace (prefixWord ++ tailWord_3262431) baseStart_3262431 baseEnd_3262431 := by
    simpa [prefixWord, tailWord_3262431, baseEnd_3262431] using wordTrace_append hprefix tailTrace_3262431
  have hstable : (prefixWord ++ tailWord_3262431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262431).length < 2 ^ (prefixWord ++ tailWord_3262431).sum := by decide
  have hdescent : baseEnd_3262431 < baseStart_3262431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262464 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_3262464 : Nat := 118140960795 + 3262464 * 2 ^ 59
def prefixEnd_3262464 : Nat := 4983230072969 + 3 ^ 40 * 3262464 * 2
def baseEnd_3262464 : Nat := 1675212149990028828296207

theorem tailTrace_3262464 : CollatzResearch.WordTrace tailWord_3262464 prefixEnd_3262464 1675212149990028828296207 := by
  unfold tailWord_3262464
  simp only [CollatzResearch.WordTrace]
  refine ⟨59495918826328793668293223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79327891768438391557724297 59495918826328793668293223)
  ·
    refine ⟨89243878239493190502439835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59495918826328793668293223 89243878239493190502439835)
    ·
      refine ⟨133865817359239785753659753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89243878239493190502439835 133865817359239785753659753)
      ·
        refine ⟨100399363019429839315244815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133865817359239785753659753 100399363019429839315244815)
        ·
          refine ⟨150599044529144758972867223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100399363019429839315244815 150599044529144758972867223)
          ·
            refine ⟨225898566793717138459300835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150599044529144758972867223 225898566793717138459300835)
            ·
              refine ⟨338847850190575707688951253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225898566793717138459300835 338847850190575707688951253)
              ·
                refine ⟨7941746488841618148959795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 338847850190575707688951253 7941746488841618148959795)
                ·
                  refine ⟨11912619733262427223439693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941746488841618148959795 11912619733262427223439693)
                  ·
                    refine ⟨4467232399973410208789885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11912619733262427223439693 4467232399973410208789885)
                    ·
                      refine ⟨1675212149990028828296207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467232399973410208789885 1675212149990028828296207)
                      ·
                        rfl

theorem cell23_3262464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_3262464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262464 prefixEnd_3262464 := by exact prefixLift 3262464
  have htrace : WordTrace (prefixWord ++ tailWord_3262464) baseStart_3262464 baseEnd_3262464 := by
    simpa [prefixWord, tailWord_3262464, baseEnd_3262464] using wordTrace_append hprefix tailTrace_3262464
  have hstable : (prefixWord ++ tailWord_3262464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262464).length < 2 ^ (prefixWord ++ tailWord_3262464).sum := by decide
  have hdescent : baseEnd_3262464 < baseStart_3262464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262467 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 7]
def baseStart_3262467 : Nat := 118140960795 + 3262467 * 2 ^ 59
def prefixEnd_3262467 : Nat := 4983230072969 + 3 ^ 40 * 3262467 * 2
def baseEnd_3262467 : Nat := 558404563477330772186231

theorem tailTrace_3262467 : CollatzResearch.WordTrace tailWord_3262467 prefixEnd_3262467 558404563477330772186231 := by
  unfold tailWord_3262467
  simp only [CollatzResearch.WordTrace]
  refine ⟨118991947071646718848945655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79327964714431145899297103 118991947071646718848945655)
  ·
    refine ⟨178487920607470078273418483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118991947071646718848945655 178487920607470078273418483)
    ·
      refine ⟨267731880911205117410127725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178487920607470078273418483 267731880911205117410127725)
      ·
        refine ⟨100399455341701919028797897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267731880911205117410127725 100399455341701919028797897)
        ·
          refine ⟨75299591506276439271598423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100399455341701919028797897 75299591506276439271598423)
          ·
            refine ⟨112949387259414658907397635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75299591506276439271598423 112949387259414658907397635)
            ·
              refine ⟨169424080889121988361096453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112949387259414658907397635 169424080889121988361096453)
              ·
                refine ⟨31767015166710372817705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169424080889121988361096453 31767015166710372817705585)
                ·
                  refine ⟨23825261375032779613279189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31767015166710372817705585 23825261375032779613279189)
                  ·
                    refine ⟨558404563477330772186231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23825261375032779613279189 558404563477330772186231)
                    ·
                      rfl

theorem cell23_3262467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_3262467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262467 prefixEnd_3262467 := by exact prefixLift 3262467
  have htrace : WordTrace (prefixWord ++ tailWord_3262467) baseStart_3262467 baseEnd_3262467 := by
    simpa [prefixWord, tailWord_3262467, baseEnd_3262467] using wordTrace_append hprefix tailTrace_3262467
  have hstable : (prefixWord ++ tailWord_3262467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262467).length < 2 ^ (prefixWord ++ tailWord_3262467).sum := by decide
  have hdescent : baseEnd_3262467 < baseStart_3262467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262471 : List Nat := [1, 1, 4, 3, 1, 4, 2, 7]
def baseStart_3262471 : Nat := 118140960795 + 3262471 * 2 ^ 59
def prefixEnd_3262471 : Nat := 4983230072969 + 3 ^ 40 * 3262471 * 2
def baseEnd_3262471 : Nat := 62045027568689270404025

theorem tailTrace_3262471 : CollatzResearch.WordTrace tailWord_3262471 prefixEnd_3262471 62045027568689270404025 := by
  unfold tailWord_3262471
  simp only [CollatzResearch.WordTrace]
  refine ⟨118992092963632227532091267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79328061975754818354727511 118992092963632227532091267)
  ·
    refine ⟨178488139445448341298136901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118992092963632227532091267 178488139445448341298136901)
    ·
      refine ⟨33466526146021563993400669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178488139445448341298136901 33466526146021563993400669)
      ·
        refine ⟨12549947304758086497525251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33466526146021563993400669 12549947304758086497525251)
        ·
          refine ⟨18824920957137129746287877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12549947304758086497525251 18824920957137129746287877)
          ·
            refine ⟨3529672679463211827428977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18824920957137129746287877 3529672679463211827428977)
            ·
              refine ⟨2647254509597408870571733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529672679463211827428977 2647254509597408870571733)
              ·
                refine ⟨62045027568689270404025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2647254509597408870571733 62045027568689270404025)
                ·
                  rfl

theorem cell23_3262471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 7].length) (baseStart_3262471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262471 prefixEnd_3262471 := by exact prefixLift 3262471
  have htrace : WordTrace (prefixWord ++ tailWord_3262471) baseStart_3262471 baseEnd_3262471 := by
    simpa [prefixWord, tailWord_3262471, baseEnd_3262471] using wordTrace_append hprefix tailTrace_3262471
  have hstable : (prefixWord ++ tailWord_3262471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262471).length < 2 ^ (prefixWord ++ tailWord_3262471).sum := by decide
  have hdescent : baseEnd_3262471 < baseStart_3262471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262498 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3262498 : Nat := 118140960795 + 3262498 * 2 ^ 59
def prefixEnd_3262498 : Nat := 4983230072969 + 3 ^ 40 * 3262498 * 2
def baseEnd_3262498 : Nat := 1675229608332281695271051

theorem tailTrace_3262498 : CollatzResearch.WordTrace tailWord_3262498 prefixEnd_3262498 1675229608332281695271051 := by
  unfold tailWord_3262498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29748269433633602785831037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79328718489689607428882765 29748269433633602785831037)
  ·
    refine ⟨11155601037612601044686639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29748269433633602785831037 11155601037612601044686639)
    ·
      refine ⟨16733401556418901567029959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155601037612601044686639 16733401556418901567029959)
      ·
        refine ⟨25100102334628352350544939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16733401556418901567029959 25100102334628352350544939)
        ·
          refine ⟨37650153501942528525817409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25100102334628352350544939 37650153501942528525817409)
          ·
            refine ⟨28237615126456896394363057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37650153501942528525817409 28237615126456896394363057)
            ·
              refine ⟨21178211344842672295772293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28237615126456896394363057 21178211344842672295772293)
              ·
                refine ⟨3970914627158001055457305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21178211344842672295772293 3970914627158001055457305)
                ·
                  refine ⟨2978185970368500791592979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3970914627158001055457305 2978185970368500791592979)
                  ·
                    refine ⟨4467278955552751187389469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978185970368500791592979 4467278955552751187389469)
                    ·
                      refine ⟨1675229608332281695271051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467278955552751187389469 1675229608332281695271051)
                      ·
                        rfl

theorem cell23_3262498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3262498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262498 prefixEnd_3262498 := by exact prefixLift 3262498
  have htrace : WordTrace (prefixWord ++ tailWord_3262498) baseStart_3262498 baseEnd_3262498 := by
    simpa [prefixWord, tailWord_3262498, baseEnd_3262498] using wordTrace_append hprefix tailTrace_3262498
  have hstable : (prefixWord ++ tailWord_3262498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262498).length < 2 ^ (prefixWord ++ tailWord_3262498).sum := by decide
  have hdescent : baseEnd_3262498 < baseStart_3262498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262524 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3262524 : Nat := 118140960795 + 3262524 * 2 ^ 59
def prefixEnd_3262524 : Nat := 4983230072969 + 3 ^ 40 * 3262524 * 2
def baseEnd_3262524 : Nat := 1675242958829298593545931

theorem tailTrace_3262524 : CollatzResearch.WordTrace tailWord_3262524 prefixEnd_3262524 1675242958829298593545931 := by
  unfold tailWord_3262524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59497013016220108791885313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79329350688293478389180417 59497013016220108791885313)
  ·
    refine ⟨44622759762165081593913985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59497013016220108791885313 44622759762165081593913985)
    ·
      refine ⟨33467069821623811195435489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44622759762165081593913985 33467069821623811195435489)
      ·
        refine ⟨25100302366217858396576617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33467069821623811195435489 25100302366217858396576617)
        ·
          refine ⟨18825226774663393797432463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25100302366217858396576617 18825226774663393797432463)
          ·
            refine ⟨28237840161995090696148695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18825226774663393797432463 28237840161995090696148695)
            ·
              refine ⟨42356760242992636044223043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28237840161995090696148695 42356760242992636044223043)
              ·
                refine ⟨63535140364488954066334565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42356760242992636044223043 63535140364488954066334565)
                ·
                  refine ⟨11912838818341678887437731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63535140364488954066334565 11912838818341678887437731)
                  ·
                    refine ⟨17869258227512518331156597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11912838818341678887437731 17869258227512518331156597)
                    ·
                      refine ⟨1675242958829298593545931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17869258227512518331156597 1675242958829298593545931)
                      ·
                        rfl

theorem cell23_3262524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3262524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262524 prefixEnd_3262524 := by exact prefixLift 3262524
  have htrace : WordTrace (prefixWord ++ tailWord_3262524) baseStart_3262524 baseEnd_3262524 := by
    simpa [prefixWord, tailWord_3262524, baseEnd_3262524] using wordTrace_append hprefix tailTrace_3262524
  have hstable : (prefixWord ++ tailWord_3262524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262524).length < 2 ^ (prefixWord ++ tailWord_3262524).sum := by decide
  have hdescent : baseEnd_3262524 < baseStart_3262524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262541 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3262541 : Nat := 118140960795 + 3262541 * 2 ^ 59
def prefixEnd_3262541 : Nat := 4983230072969 + 3 ^ 40 * 3262541 * 2
def baseEnd_3262541 : Nat := 1675251688000425027033353

theorem tailTrace_3262541 : CollatzResearch.WordTrace tailWord_3262541 prefixEnd_3262541 1675251688000425027033353 := by
  unfold tailWord_3262541
  simp only [CollatzResearch.WordTrace]
  refine ⟨118994646073378629487139477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79329764048919086324759651 118994646073378629487139477)
  ·
    refine ⟨5577874034689623257209663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118994646073378629487139477 5577874034689623257209663)
    ·
      refine ⟨8366811052034434885814495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5577874034689623257209663 8366811052034434885814495)
      ·
        refine ⟨12550216578051652328721743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8366811052034434885814495 12550216578051652328721743)
        ·
          refine ⟨18825324867077478493082615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12550216578051652328721743 18825324867077478493082615)
          ·
            refine ⟨28237987300616217739623923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18825324867077478493082615 28237987300616217739623923)
            ·
              refine ⟨42356980950924326609435885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28237987300616217739623923 42356980950924326609435885)
              ·
                refine ⟨15883867856596622478538457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42356980950924326609435885 15883867856596622478538457)
                ·
                  refine ⟨11912900892447466858903843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15883867856596622478538457 11912900892447466858903843)
                  ·
                    refine ⟨17869351338671200288355765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11912900892447466858903843 17869351338671200288355765)
                    ·
                      refine ⟨1675251688000425027033353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17869351338671200288355765 1675251688000425027033353)
                      ·
                        rfl

theorem cell23_3262541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3262541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262541 prefixEnd_3262541 := by exact prefixLift 3262541
  have htrace : WordTrace (prefixWord ++ tailWord_3262541) baseStart_3262541 baseEnd_3262541 := by
    simpa [prefixWord, tailWord_3262541, baseEnd_3262541] using wordTrace_append hprefix tailTrace_3262541
  have hstable : (prefixWord ++ tailWord_3262541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262541).length < 2 ^ (prefixWord ++ tailWord_3262541).sum := by decide
  have hdescent : baseEnd_3262541 < baseStart_3262541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262685 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 6]
def baseStart_3262685 : Nat := 118140960795 + 3262685 * 2 ^ 59
def prefixEnd_3262685 : Nat := 4983230072969 + 3 ^ 40 * 3262685 * 2
def baseEnd_3262685 : Nat := 186147292134963607070299

theorem tailTrace_3262685 : CollatzResearch.WordTrace tailWord_3262685 prefixEnd_3262685 186147292134963607070299 := by
  unfold tailWord_3262685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118999898184856942080381509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79333265456571294720254339 118999898184856942080381509)
  ·
    refine ⟨22312480909660676640071533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118999898184856942080381509 22312480909660676640071533)
    ·
      refine ⟨8367180341122753740026825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22312480909660676640071533 8367180341122753740026825)
      ·
        refine ⟨6275385255842065305020119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8367180341122753740026825 6275385255842065305020119)
        ·
          refine ⟨9413077883763097957530179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275385255842065305020119 9413077883763097957530179)
          ·
            refine ⟨14119616825644646936295269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413077883763097957530179 14119616825644646936295269)
            ·
              refine ⟨2647428154808371300555363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14119616825644646936295269 2647428154808371300555363)
              ·
                refine ⟨3971142232212556950833045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647428154808371300555363 3971142232212556950833045)
                ·
                  refine ⟨186147292134963607070299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3971142232212556950833045 186147292134963607070299)
                  ·
                    rfl

theorem cell23_3262685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_3262685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262685 prefixEnd_3262685 := by exact prefixLift 3262685
  have htrace : WordTrace (prefixWord ++ tailWord_3262685) baseStart_3262685 baseEnd_3262685 := by
    simpa [prefixWord, tailWord_3262685, baseEnd_3262685] using wordTrace_append hprefix tailTrace_3262685
  have hstable : (prefixWord ++ tailWord_3262685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262685).length < 2 ^ (prefixWord ++ tailWord_3262685).sum := by decide
  have hdescent : baseEnd_3262685 < baseStart_3262685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262688 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2]
def baseStart_3262688 : Nat := 118140960795 + 3262688 * 2 ^ 59
def prefixEnd_3262688 : Nat := 4983230072969 + 3 ^ 40 * 3262688 * 2
def baseEnd_3262688 : Nat := 1675327169656635951895177

theorem tailTrace_3262688 : CollatzResearch.WordTrace tailWord_3262688 prefixEnd_3262688 1675327169656635951895177 := by
  unfold tailWord_3262688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59500003801923036796370359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79333338402564049061827145 59500003801923036796370359)
  ·
    refine ⟨89250005702884555194555539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59500003801923036796370359 89250005702884555194555539)
    ·
      refine ⟨133875008554326832791833309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89250005702884555194555539 133875008554326832791833309)
      ·
        refine ⟨50203128207872562296937491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133875008554326832791833309 50203128207872562296937491)
        ·
          refine ⟨75304692311808843445406237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50203128207872562296937491 75304692311808843445406237)
          ·
            refine ⟨28239259616928316292027339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75304692311808843445406237 28239259616928316292027339)
            ·
              refine ⟨42358889425392474438041009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28239259616928316292027339 42358889425392474438041009)
              ·
                refine ⟨31769167069044355828530757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42358889425392474438041009 31769167069044355828530757)
                ·
                  refine ⟨5956718825445816717849517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31769167069044355828530757 5956718825445816717849517)
                  ·
                    refine ⟨2233769559542181269193569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5956718825445816717849517 2233769559542181269193569)
                    ·
                      refine ⟨1675327169656635951895177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233769559542181269193569 1675327169656635951895177)
                      ·
                        rfl

theorem cell23_3262688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_3262688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262688 prefixEnd_3262688 := by exact prefixLift 3262688
  have htrace : WordTrace (prefixWord ++ tailWord_3262688) baseStart_3262688 baseEnd_3262688 := by
    simpa [prefixWord, tailWord_3262688, baseEnd_3262688] using wordTrace_append hprefix tailTrace_3262688
  have hstable : (prefixWord ++ tailWord_3262688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262688).length < 2 ^ (prefixWord ++ tailWord_3262688).sum := by decide
  have hdescent : baseEnd_3262688 < baseStart_3262688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262722 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3262722 : Nat := 118140960795 + 3262722 * 2 ^ 59
def prefixEnd_3262722 : Nat := 4983230072969 + 3 ^ 40 * 3262722 * 2
def baseEnd_3262722 : Nat := 1675344627998888818870021

theorem tailTrace_3262722 : CollatzResearch.WordTrace tailWord_3262722 prefixEnd_3262722 1675344627998888818870021 := by
  unfold tailWord_3262722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29750311921430724349869605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79334165123815264932985613 29750311921430724349869605)
  ·
    refine ⟨5578183485268260815600551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29750311921430724349869605 5578183485268260815600551)
    ·
      refine ⟨8367275227902391223400827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5578183485268260815600551 8367275227902391223400827)
      ·
        refine ⟨12550912841853586835101241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367275227902391223400827 12550912841853586835101241)
        ·
          refine ⟨9413184631390190126325931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12550912841853586835101241 9413184631390190126325931)
          ·
            refine ⟨14119776947085285189488897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413184631390190126325931 14119776947085285189488897)
            ·
              refine ⟨10589832710313963892116673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14119776947085285189488897 10589832710313963892116673)
              ·
                refine ⟨7942374532735472919087505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10589832710313963892116673 7942374532735472919087505)
                ·
                  refine ⟨5956780899551604689315629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942374532735472919087505 5956780899551604689315629)
                  ·
                    refine ⟨2233792837331851758493361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5956780899551604689315629 2233792837331851758493361)
                    ·
                      refine ⟨1675344627998888818870021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233792837331851758493361 1675344627998888818870021)
                      ·
                        rfl

theorem cell23_3262722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3262722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262722 prefixEnd_3262722 := by exact prefixLift 3262722
  have htrace : WordTrace (prefixWord ++ tailWord_3262722) baseStart_3262722 baseEnd_3262722 := by
    simpa [prefixWord, tailWord_3262722, baseEnd_3262722] using wordTrace_append hprefix tailTrace_3262722
  have hstable : (prefixWord ++ tailWord_3262722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262722).length < 2 ^ (prefixWord ++ tailWord_3262722).sum := by decide
  have hdescent : baseEnd_3262722 < baseStart_3262722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262729 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 1, 1, 3]
def baseStart_3262729 : Nat := 118140960795 + 3262729 * 2 ^ 59
def prefixEnd_3262729 : Nat := 4983230072969 + 3 ^ 40 * 3262729 * 2
def baseEnd_3262729 : Nat := 1675348222363470291482489

theorem tailTrace_3262729 : CollatzResearch.WordTrace tailWord_3262729 prefixEnd_3262729 1675348222363470291482489 := by
  unfold tailWord_3262729
  simp only [CollatzResearch.WordTrace]
  refine ⟨119001502996697537594983241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79334335331131691729988827 119001502996697537594983241)
  ·
    refine ⟨89251127247523153196237431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119001502996697537594983241 89251127247523153196237431)
    ·
      refine ⟨133876690871284729794356147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89251127247523153196237431 133876690871284729794356147)
      ·
        refine ⟨200815036306927094691534221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133876690871284729794356147 200815036306927094691534221)
        ·
          refine ⟨75305638615097660509325333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200815036306927094691534221 75305638615097660509325333)
          ·
            refine ⟨3529951810082702836374625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75305638615097660509325333 3529951810082702836374625)
            ·
              refine ⟨2647463857562027127280969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529951810082702836374625 2647463857562027127280969)
              ·
                refine ⟨1985597893171520345460727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647463857562027127280969 1985597893171520345460727)
                ·
                  refine ⟨2978396839757280518191091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985597893171520345460727 2978396839757280518191091)
                  ·
                    refine ⟨4467595259635920777286637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978396839757280518191091 4467595259635920777286637)
                    ·
                      refine ⟨1675348222363470291482489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467595259635920777286637 1675348222363470291482489)
                      ·
                        rfl

theorem cell23_3262729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 1, 3].length) (baseStart_3262729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262729 prefixEnd_3262729 := by exact prefixLift 3262729
  have htrace : WordTrace (prefixWord ++ tailWord_3262729) baseStart_3262729 baseEnd_3262729 := by
    simpa [prefixWord, tailWord_3262729, baseEnd_3262729] using wordTrace_append hprefix tailTrace_3262729
  have hstable : (prefixWord ++ tailWord_3262729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262729).length < 2 ^ (prefixWord ++ tailWord_3262729).sum := by decide
  have hdescent : baseEnd_3262729 < baseStart_3262729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262731 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_3262731 : Nat := 118140960795 + 3262731 * 2 ^ 59
def prefixEnd_3262731 : Nat := 4983230072969 + 3 ^ 40 * 3262731 * 2
def baseEnd_3262731 : Nat := 1675349249324779283657479

theorem tailTrace_3262731 : CollatzResearch.WordTrace tailWord_3262731 prefixEnd_3262731 1675349249324779283657479 := by
  unfold tailWord_3262731
  simp only [CollatzResearch.WordTrace]
  refine ⟨119001575942690291936556047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79334383961793527957704031 119001575942690291936556047)
  ·
    refine ⟨178502363914035437904834071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119001575942690291936556047 178502363914035437904834071)
    ·
      refine ⟨267753545871053156857251107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178502363914035437904834071 267753545871053156857251107)
      ·
        refine ⟨401630318806579735285876661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267753545871053156857251107 401630318806579735285876661)
        ·
          refine ⟨37652842388116850183050937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401630318806579735285876661 37652842388116850183050937)
          ·
            refine ⟨28239631791087637637288203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37652842388116850183050937 28239631791087637637288203)
            ·
              refine ⟨42359447686631456455932305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28239631791087637637288203 42359447686631456455932305)
              ·
                refine ⟨31769585764973592341949229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42359447686631456455932305 31769585764973592341949229)
                ·
                  refine ⟨11913594661865097128230961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31769585764973592341949229 11913594661865097128230961)
                  ·
                    refine ⟨8935195996398822846173221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11913594661865097128230961 8935195996398822846173221)
                    ·
                      refine ⟨1675349249324779283657479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8935195996398822846173221 1675349249324779283657479)
                      ·
                        rfl

theorem cell23_3262731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_3262731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262731 prefixEnd_3262731 := by exact prefixLift 3262731
  have htrace : WordTrace (prefixWord ++ tailWord_3262731) baseStart_3262731 baseEnd_3262731 := by
    simpa [prefixWord, tailWord_3262731, baseEnd_3262731] using wordTrace_append hprefix tailTrace_3262731
  have hstable : (prefixWord ++ tailWord_3262731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262731).length < 2 ^ (prefixWord ++ tailWord_3262731).sum := by decide
  have hdescent : baseEnd_3262731 < baseStart_3262731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262741 : List Nat := [1, 3, 2, 1, 2, 1, 5, 8]
def baseStart_3262741 : Nat := 118140960795 + 3262741 * 2 ^ 59
def prefixEnd_3262741 : Nat := 4983230072969 + 3 ^ 40 * 3262741 * 2
def baseEnd_3262741 : Nat := 62050162375234231278979

theorem tailTrace_3262741 : CollatzResearch.WordTrace tailWord_3262741 prefixEnd_3262741 62050162375234231278979 := by
  unfold tailWord_3262741
  simp only [CollatzResearch.WordTrace]
  refine ⟨119001940672654063644420077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79334627115102709096280051 119001940672654063644420077)
  ·
    refine ⟨44625727752245273866657529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119001940672654063644420077 44625727752245273866657529)
    ·
      refine ⟨33469295814183955399993147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44625727752245273866657529 33469295814183955399993147)
      ·
        refine ⟨50203943721275933099989721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33469295814183955399993147 50203943721275933099989721)
        ·
          refine ⟨37652957790956949824992291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50203943721275933099989721 37652957790956949824992291)
          ·
            refine ⟨56479436686435424737488437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37652957790956949824992291 56479436686435424737488437)
            ·
              refine ⟨5294947189353321069139541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56479436686435424737488437 5294947189353321069139541)
              ·
                refine ⟨62050162375234231278979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5294947189353321069139541 62050162375234231278979)
                ·
                  rfl

theorem cell23_3262741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 8].length) (baseStart_3262741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262741 prefixEnd_3262741 := by exact prefixLift 3262741
  have htrace : WordTrace (prefixWord ++ tailWord_3262741) baseStart_3262741 baseEnd_3262741 := by
    simpa [prefixWord, tailWord_3262741, baseEnd_3262741] using wordTrace_append hprefix tailTrace_3262741
  have hstable : (prefixWord ++ tailWord_3262741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262741).length < 2 ^ (prefixWord ++ tailWord_3262741).sum := by decide
  have hdescent : baseEnd_3262741 < baseStart_3262741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262752 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3262752 : Nat := 118140960795 + 3262752 * 2 ^ 59
def prefixEnd_3262752 : Nat := 4983230072969 + 3 ^ 40 * 3262752 * 2
def baseEnd_3262752 : Nat := 1675360032418523701494883

theorem tailTrace_3262752 : CollatzResearch.WordTrace tailWord_3262752 prefixEnd_3262752 1675360032418523701494883 := by
  unfold tailWord_3262752
  simp only [CollatzResearch.WordTrace]
  refine ⟨59501170937807106261535255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79334894583742808348713673 59501170937807106261535255)
  ·
    refine ⟨89251756406710659392302883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59501170937807106261535255 89251756406710659392302883)
    ·
      refine ⟨133877634610065989088454325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89251756406710659392302883 133877634610065989088454325)
      ·
        refine ⟨12551028244693686477042593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133877634610065989088454325 12551028244693686477042593)
        ·
          refine ⟨9413271183520264857781945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12551028244693686477042593 9413271183520264857781945)
          ·
            refine ⟨7059953387640198643336459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413271183520264857781945 7059953387640198643336459)
            ·
              refine ⟨10589930081460297965004689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059953387640198643336459 10589930081460297965004689)
              ·
                refine ⟨7942447561095223473753517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10589930081460297965004689 7942447561095223473753517)
                ·
                  refine ⟨2978417835410708802657569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7942447561095223473753517 2978417835410708802657569)
                  ·
                    refine ⟨2233813376558031601993177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978417835410708802657569 2233813376558031601993177)
                    ·
                      refine ⟨1675360032418523701494883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233813376558031601993177 1675360032418523701494883)
                      ·
                        rfl

theorem cell23_3262752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3262752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262752 prefixEnd_3262752 := by exact prefixLift 3262752
  have htrace : WordTrace (prefixWord ++ tailWord_3262752) baseStart_3262752 baseEnd_3262752 := by
    simpa [prefixWord, tailWord_3262752, baseEnd_3262752] using wordTrace_append hprefix tailTrace_3262752
  have hstable : (prefixWord ++ tailWord_3262752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262752).length < 2 ^ (prefixWord ++ tailWord_3262752).sum := by decide
  have hdescent : baseEnd_3262752 < baseStart_3262752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262766 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3262766 : Nat := 118140960795 + 3262766 * 2 ^ 59
def prefixEnd_3262766 : Nat := 4983230072969 + 3 ^ 40 * 3262766 * 2
def baseEnd_3262766 : Nat := 558455740382562215573273

theorem tailTrace_3262766 : CollatzResearch.WordTrace tailWord_3262766 prefixEnd_3262766 558455740382562215573273 := by
  unfold tailWord_3262766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875356562195436614260019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79335234998375661942720101 14875356562195436614260019)
  ·
    refine ⟨22313034843293154921390029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875356562195436614260019 22313034843293154921390029)
    ·
      refine ⟨8367388066234933095521261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22313034843293154921390029 8367388066234933095521261)
      ·
        refine ⟨3137770524838099910820473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8367388066234933095521261 3137770524838099910820473)
        ·
          refine ⟨2353327893628574933115355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3137770524838099910820473 2353327893628574933115355)
          ·
            refine ⟨3529991840442862399673033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353327893628574933115355 3529991840442862399673033)
            ·
              refine ⟨2647493880332146799754775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529991840442862399673033 2647493880332146799754775)
              ·
                refine ⟨3971240820498220199632163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647493880332146799754775 3971240820498220199632163)
                ·
                  refine ⟨5956861230747330299448245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971240820498220199632163 5956861230747330299448245)
                  ·
                    refine ⟨558455740382562215573273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5956861230747330299448245 558455740382562215573273)
                    ·
                      rfl

theorem cell23_3262766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3262766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262766 prefixEnd_3262766 := by exact prefixLift 3262766
  have htrace : WordTrace (prefixWord ++ tailWord_3262766) baseStart_3262766 baseEnd_3262766 := by
    simpa [prefixWord, tailWord_3262766, baseEnd_3262766] using wordTrace_append hprefix tailTrace_3262766
  have hstable : (prefixWord ++ tailWord_3262766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262766).length < 2 ^ (prefixWord ++ tailWord_3262766).sum := by decide
  have hdescent : baseEnd_3262766 < baseStart_3262766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262769 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_3262769 : Nat := 118140960795 + 3262769 * 2 ^ 59
def prefixEnd_3262769 : Nat := 4983230072969 + 3 ^ 40 * 3262769 * 2
def baseEnd_3262769 : Nat := 1675368761589650134982305

theorem tailTrace_3262769 : CollatzResearch.WordTrace tailWord_3262769 prefixEnd_3262769 1675368761589650134982305 := by
  unfold tailWord_3262769
  simp only [CollatzResearch.WordTrace]
  refine ⟨119002961916552624426439361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79335307944368416284292907 119002961916552624426439361)
  ·
    refine ⟨89252221437414468319829521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119002961916552624426439361 89252221437414468319829521)
    ·
      refine ⟨66939166078060851239872141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89252221437414468319829521 66939166078060851239872141)
      ·
        refine ⟨25102187279272819214952053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66939166078060851239872141 25102187279272819214952053)
        ·
          refine ⟨2353330057431826801401755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25102187279272819214952053 2353330057431826801401755)
          ·
            refine ⟨3529995086147740202102633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353330057431826801401755 3529995086147740202102633)
            ·
              refine ⟨2647496314610805151576975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529995086147740202102633 2647496314610805151576975)
              ·
                refine ⟨3971244471916207727365463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647496314610805151576975 3971244471916207727365463)
                ·
                  refine ⟨5956866707874311591048195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971244471916207727365463 5956866707874311591048195)
                  ·
                    refine ⟨8935300061811467386572293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956866707874311591048195 8935300061811467386572293)
                    ·
                      refine ⟨1675368761589650134982305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8935300061811467386572293 1675368761589650134982305)
                      ·
                        rfl

theorem cell23_3262769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_3262769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262769 prefixEnd_3262769 := by exact prefixLift 3262769
  have htrace : WordTrace (prefixWord ++ tailWord_3262769) baseStart_3262769 baseEnd_3262769 := by
    simpa [prefixWord, tailWord_3262769, baseEnd_3262769] using wordTrace_append hprefix tailTrace_3262769
  have hstable : (prefixWord ++ tailWord_3262769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262769).length < 2 ^ (prefixWord ++ tailWord_3262769).sum := by decide
  have hdescent : baseEnd_3262769 < baseStart_3262769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262772 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3262772 : Nat := 118140960795 + 3262772 * 2 ^ 59
def prefixEnd_3262772 : Nat := 4983230072969 + 3 ^ 40 * 3262772 * 2
def baseEnd_3262772 : Nat := 1675370302031613623244791

theorem tailTrace_3262772 : CollatzResearch.WordTrace tailWord_3262772 prefixEnd_3262772 1675370302031613623244791 := by
  unfold tailWord_3262772
  simp only [CollatzResearch.WordTrace]
  refine ⟨59501535667770877969399285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79335380890361170625865713 59501535667770877969399285)
  ·
    refine ⟨5578268968853519809631183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59501535667770877969399285 5578268968853519809631183)
    ·
      refine ⟨8367403453280279714446775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5578268968853519809631183 8367403453280279714446775)
      ·
        refine ⟨12551105179920419571670163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367403453280279714446775 12551105179920419571670163)
        ·
          refine ⟨18826657769880629357505245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12551105179920419571670163 18826657769880629357505245)
          ·
            refine ⟨7059996663705236009064467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18826657769880629357505245 7059996663705236009064467)
            ·
              refine ⟨10589994995557854013596701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059996663705236009064467 10589994995557854013596701)
              ·
                refine ⟨3971248123334195255098763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10589994995557854013596701 3971248123334195255098763)
                ·
                  refine ⟨5956872185001292882648145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971248123334195255098763 5956872185001292882648145)
                  ·
                    refine ⟨4467654138750969661986109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956872185001292882648145 4467654138750969661986109)
                    ·
                      refine ⟨1675370302031613623244791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467654138750969661986109 1675370302031613623244791)
                      ·
                        rfl

theorem cell23_3262772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3262772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262772 prefixEnd_3262772 := by exact prefixLift 3262772
  have htrace : WordTrace (prefixWord ++ tailWord_3262772) baseStart_3262772 baseEnd_3262772 := by
    simpa [prefixWord, tailWord_3262772, baseEnd_3262772] using wordTrace_append hprefix tailTrace_3262772
  have hstable : (prefixWord ++ tailWord_3262772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262772).length < 2 ^ (prefixWord ++ tailWord_3262772).sum := by decide
  have hdescent : baseEnd_3262772 < baseStart_3262772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
